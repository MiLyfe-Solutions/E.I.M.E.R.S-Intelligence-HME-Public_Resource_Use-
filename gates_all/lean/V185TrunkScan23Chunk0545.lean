import V185TrunkScan23Chunk0544

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3222455 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_3222455 : Nat := 118140960795 + 3222455 * 2 ^ 59
def prefixEnd_3222455 : Nat := 4983230072969 + 3 ^ 40 * 3222455 * 2
def baseEnd_3222455 : Nat := 1654668302484294863692705

theorem tailTrace_3222455 : CollatzResearch.WordTrace tailWord_3222455 prefixEnd_3222455 1654668302484294863692705 := by
  unfold tailWord_3222455
  simp only [CollatzResearch.WordTrace]
  refine ⟨117532589540603361343388819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78355059693735574228925879 117532589540603361343388819)
  ·
    refine ⟨176298884310905042015083229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117532589540603361343388819 176298884310905042015083229)
    ·
      refine ⟨66112081616589390755656211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176298884310905042015083229 66112081616589390755656211)
      ·
        refine ⟨99168122424884086133484317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66112081616589390755656211 99168122424884086133484317)
        ·
          refine ⟨37188045909331532300056619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99168122424884086133484317 37188045909331532300056619)
          ·
            refine ⟨55782068863997298450084929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37188045909331532300056619 55782068863997298450084929)
            ·
              refine ⟨41836551647997973837563697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55782068863997298450084929 41836551647997973837563697)
              ·
                refine ⟨31377413735998480378172773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41836551647997973837563697 31377413735998480378172773)
                ·
                  refine ⟨5883265075499715070907395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31377413735998480378172773 5883265075499715070907395)
                  ·
                    refine ⟨8824897613249572606361093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883265075499715070907395 8824897613249572606361093)
                    ·
                      refine ⟨1654668302484294863692705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8824897613249572606361093 1654668302484294863692705)
                      ·
                        rfl

theorem cell23_3222455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_3222455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222455 prefixEnd_3222455 := by exact prefixLift 3222455
  have htrace : WordTrace (prefixWord ++ tailWord_3222455) baseStart_3222455 baseEnd_3222455 := by
    simpa [prefixWord, tailWord_3222455, baseEnd_3222455] using wordTrace_append hprefix tailTrace_3222455
  have hstable : (prefixWord ++ tailWord_3222455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222455).length < 2 ^ (prefixWord ++ tailWord_3222455).sum := by decide
  have hdescent : baseEnd_3222455 < baseStart_3222455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222472 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3222472 : Nat := 118140960795 + 3222472 * 2 ^ 59
def prefixEnd_3222472 : Nat := 4983230072969 + 3 ^ 40 * 3222472 * 2
def baseEnd_3222472 : Nat := 1654677031655421297180127

theorem tailTrace_3222472 : CollatzResearch.WordTrace tailWord_3222472 prefixEnd_3222472 1654677031655421297180127 := by
  unfold tailWord_3222472
  simp only [CollatzResearch.WordTrace]
  refine ⟨58766604790770886623378835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78355473054361182164505113 58766604790770886623378835)
  ·
    refine ⟨88149907186156329935068253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58766604790770886623378835 88149907186156329935068253)
    ·
      refine ⟨33056215194808623725650595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88149907186156329935068253 33056215194808623725650595)
      ·
        refine ⟨49584322792212935588475893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33056215194808623725650595 49584322792212935588475893)
        ·
          refine ⟨4648530261769962711419615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49584322792212935588475893 4648530261769962711419615)
          ·
            refine ⟨6972795392654944067129423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648530261769962711419615 6972795392654944067129423)
            ·
              refine ⟨10459193088982416100694135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6972795392654944067129423 10459193088982416100694135)
              ·
                refine ⟨15688789633473624151041203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10459193088982416100694135 15688789633473624151041203)
                ·
                  refine ⟨23533184450210436226561805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15688789633473624151041203 23533184450210436226561805)
                  ·
                    refine ⟨8824944168828913584960677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23533184450210436226561805 8824944168828913584960677)
                    ·
                      refine ⟨1654677031655421297180127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8824944168828913584960677 1654677031655421297180127)
                      ·
                        rfl

theorem cell23_3222472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3222472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222472 prefixEnd_3222472 := by exact prefixLift 3222472
  have htrace : WordTrace (prefixWord ++ tailWord_3222472) baseStart_3222472 baseEnd_3222472 := by
    simpa [prefixWord, tailWord_3222472, baseEnd_3222472] using wordTrace_append hprefix tailTrace_3222472
  have hstable : (prefixWord ++ tailWord_3222472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222472).length < 2 ^ (prefixWord ++ tailWord_3222472).sum := by decide
  have hdescent : baseEnd_3222472 < baseStart_3222472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222499 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 1, 4]
def baseStart_3222499 : Nat := 118140960795 + 3222499 * 2 ^ 59
def prefixEnd_3222499 : Nat := 4983230072969 + 3 ^ 40 * 3222499 * 2
def baseEnd_3222499 : Nat := 551563631877697563847501

theorem tailTrace_3222499 : CollatzResearch.WordTrace tailWord_3222499 prefixEnd_3222499 551563631877697563847501 := by
  unfold tailWord_3222499
  simp only [CollatzResearch.WordTrace]
  refine ⟨117534194352443956857990551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78356129568295971238660367 117534194352443956857990551)
  ·
    refine ⟨176301291528665935286985827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117534194352443956857990551 176301291528665935286985827)
    ·
      refine ⟨264451937292998902930478741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176301291528665935286985827 264451937292998902930478741)
      ·
        refine ⟨12396184560609323574866191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 264451937292998902930478741 12396184560609323574866191)
        ·
          refine ⟨18594276840913985362299287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12396184560609323574866191 18594276840913985362299287)
          ·
            refine ⟨27891415261370978043448931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18594276840913985362299287 27891415261370978043448931)
            ·
              refine ⟨41837122892056467065173397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27891415261370978043448931 41837122892056467065173397)
              ·
                refine ⟨1961115135565146893680003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41837122892056467065173397 1961115135565146893680003)
                ·
                  refine ⟨2941672703347720340520005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961115135565146893680003 2941672703347720340520005)
                  ·
                    refine ⟨551563631877697563847501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2941672703347720340520005 551563631877697563847501)
                    ·
                      rfl

theorem cell23_3222499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 4].length) (baseStart_3222499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222499 prefixEnd_3222499 := by exact prefixLift 3222499
  have htrace : WordTrace (prefixWord ++ tailWord_3222499) baseStart_3222499 baseEnd_3222499 := by
    simpa [prefixWord, tailWord_3222499, baseEnd_3222499] using wordTrace_append hprefix tailTrace_3222499
  have hstable : (prefixWord ++ tailWord_3222499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222499).length < 2 ^ (prefixWord ++ tailWord_3222499).sum := by decide
  have hdescent : baseEnd_3222499 < baseStart_3222499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222549 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_3222549 : Nat := 118140960795 + 3222549 * 2 ^ 59
def prefixEnd_3222549 : Nat := 4983230072969 + 3 ^ 40 * 3222549 * 2
def baseEnd_3222549 : Nat := 1654716569665817495917273

theorem tailTrace_3222549 : CollatzResearch.WordTrace tailWord_3222549 prefixEnd_3222549 1654716569665817495917273 := by
  unfold tailWord_3222549
  simp only [CollatzResearch.WordTrace]
  refine ⟨117536018002262815397310701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78357345334841876931540467 117536018002262815397310701)
  ·
    refine ⟨44076006750848555773991513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117536018002262815397310701 44076006750848555773991513)
    ·
      refine ⟨33057005063136416830493635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44076006750848555773991513 33057005063136416830493635)
      ·
        refine ⟨49585507594704625245740453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33057005063136416830493635 49585507594704625245740453)
        ·
          refine ⟨9297282674007117233576335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49585507594704625245740453 9297282674007117233576335)
          ·
            refine ⟨13945924011010675850364503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297282674007117233576335 13945924011010675850364503)
            ·
              refine ⟨20918886016516013775546755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13945924011010675850364503 20918886016516013775546755)
              ·
                refine ⟨31378329024774020663320133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20918886016516013775546755 31378329024774020663320133)
                ·
                  refine ⟨5883436692145128874372525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31378329024774020663320133 5883436692145128874372525)
                  ·
                    refine ⟨2206288759554423327889697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5883436692145128874372525 2206288759554423327889697)
                    ·
                      refine ⟨1654716569665817495917273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206288759554423327889697 1654716569665817495917273)
                      ·
                        rfl

theorem cell23_3222549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_3222549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222549 prefixEnd_3222549 := by exact prefixLift 3222549
  have htrace : WordTrace (prefixWord ++ tailWord_3222549) baseStart_3222549 baseEnd_3222549 := by
    simpa [prefixWord, tailWord_3222549, baseEnd_3222549] using wordTrace_append hprefix tailTrace_3222549
  have hstable : (prefixWord ++ tailWord_3222549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222549).length < 2 ^ (prefixWord ++ tailWord_3222549).sum := by decide
  have hdescent : baseEnd_3222549 < baseStart_3222549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222579 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 5, 2, 2]
def baseStart_3222579 : Nat := 118140960795 + 3222579 * 2 ^ 59
def prefixEnd_3222579 : Nat := 4983230072969 + 3 ^ 40 * 3222579 * 2
def baseEnd_3222579 : Nat := 1654731974085452378542135

theorem tailTrace_3222579 : CollatzResearch.WordTrace tailWord_3222579 prefixEnd_3222579 1654731974085452378542135 := by
  unfold tailWord_3222579
  simp only [CollatzResearch.WordTrace]
  refine ⟨117537112192154130520902791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78358074794769420347268527 117537112192154130520902791)
  ·
    refine ⟨176305668288231195781354187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117537112192154130520902791 176305668288231195781354187)
    ·
      refine ⟨264458502432346793672031281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176305668288231195781354187 264458502432346793672031281)
      ·
        refine ⟨198343876824260095254023461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264458502432346793672031281 198343876824260095254023461)
        ·
          refine ⟨37189476904548767860129399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198343876824260095254023461 37189476904548767860129399)
          ·
            refine ⟨55784215356823151790194099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37189476904548767860129399 55784215356823151790194099)
            ·
              refine ⟨83676323035234727685291149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55784215356823151790194099 83676323035234727685291149)
              ·
                refine ⟨31378621138213022881984181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83676323035234727685291149 31378621138213022881984181)
                ·
                  refine ⟨2941745731707470895186017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31378621138213022881984181 2941745731707470895186017)
                  ·
                    refine ⟨2206309298780603171389513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941745731707470895186017 2206309298780603171389513)
                    ·
                      refine ⟨1654731974085452378542135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206309298780603171389513 1654731974085452378542135)
                      ·
                        rfl

theorem cell23_3222579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 2, 2].length) (baseStart_3222579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222579 prefixEnd_3222579 := by exact prefixLift 3222579
  have htrace : WordTrace (prefixWord ++ tailWord_3222579) baseStart_3222579 baseEnd_3222579 := by
    simpa [prefixWord, tailWord_3222579, baseEnd_3222579] using wordTrace_append hprefix tailTrace_3222579
  have hstable : (prefixWord ++ tailWord_3222579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222579).length < 2 ^ (prefixWord ++ tailWord_3222579).sum := by decide
  have hdescent : baseEnd_3222579 < baseStart_3222579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222592 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_3222592 : Nat := 118140960795 + 3222592 * 2 ^ 59
def prefixEnd_3222592 : Nat := 4983230072969 + 3 ^ 40 * 3222592 * 2
def baseEnd_3222592 : Nat := 1654738649333960827679575

theorem tailTrace_3222592 : CollatzResearch.WordTrace tailWord_3222592 prefixEnd_3222592 1654738649333960827679575 := by
  unfold tailWord_3222592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58768793170553516870563015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78358390894071355827417353 58768793170553516870563015)
  ·
    refine ⟨88153189755830275305844523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58768793170553516870563015 88153189755830275305844523)
    ·
      refine ⟨132229784633745412958766785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88153189755830275305844523 132229784633745412958766785)
      ·
        refine ⟨99172338475309059719075089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132229784633745412958766785 99172338475309059719075089)
        ·
          refine ⟨74379253856481794789306317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99172338475309059719075089 74379253856481794789306317)
          ·
            refine ⟨27892220196180673045989869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74379253856481794789306317 27892220196180673045989869)
            ·
              refine ⟨10459582573567752392246201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27892220196180673045989869 10459582573567752392246201)
              ·
                refine ⟨7844686930175814294184651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10459582573567752392246201 7844686930175814294184651)
                ·
                  refine ⟨11767030395263721441276977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844686930175814294184651 11767030395263721441276977)
                  ·
                    refine ⟨8825272796447791080957733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11767030395263721441276977 8825272796447791080957733)
                    ·
                      refine ⟨1654738649333960827679575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8825272796447791080957733 1654738649333960827679575)
                      ·
                        rfl

theorem cell23_3222592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_3222592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222592 prefixEnd_3222592 := by exact prefixLift 3222592
  have htrace : WordTrace (prefixWord ++ tailWord_3222592) baseStart_3222592 baseEnd_3222592 := by
    simpa [prefixWord, tailWord_3222592, baseEnd_3222592] using wordTrace_append hprefix tailTrace_3222592
  have hstable : (prefixWord ++ tailWord_3222592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222592).length < 2 ^ (prefixWord ++ tailWord_3222592).sum := by decide
  have hdescent : baseEnd_3222592 < baseStart_3222592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222599 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_3222599 : Nat := 118140960795 + 3222599 * 2 ^ 59
def prefixEnd_3222599 : Nat := 4983230072969 + 3 ^ 40 * 3222599 * 2
def baseEnd_3222599 : Nat := 1654742243698542300292043

theorem tailTrace_3222599 : CollatzResearch.WordTrace tailWord_3222599 prefixEnd_3222599 1654742243698542300292043 := by
  unfold tailWord_3222599
  simp only [CollatzResearch.WordTrace]
  refine ⟨117537841652081673936630851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78358561101387782624420567 117537841652081673936630851)
  ·
    refine ⟨176306762478122510904946277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117537841652081673936630851 176306762478122510904946277)
    ·
      refine ⟨33057517964647970794677427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176306762478122510904946277 33057517964647970794677427)
      ·
        refine ⟨49586276946971956192016141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33057517964647970794677427 49586276946971956192016141)
        ·
          refine ⟨18594853855114483572006053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49586276946971956192016141 18594853855114483572006053)
          ·
            refine ⟨3486535097833965669751135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18594853855114483572006053 3486535097833965669751135)
            ·
              refine ⟨5229802646750948504626703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486535097833965669751135 5229802646750948504626703)
              ·
                refine ⟨7844703970126422756940055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229802646750948504626703 7844703970126422756940055)
                ·
                  refine ⟨11767055955189634135410083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844703970126422756940055 11767055955189634135410083)
                  ·
                    refine ⟨17650583932784451203115125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11767055955189634135410083 17650583932784451203115125)
                    ·
                      refine ⟨1654742243698542300292043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17650583932784451203115125 1654742243698542300292043)
                      ·
                        rfl

theorem cell23_3222599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_3222599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222599 prefixEnd_3222599 := by exact prefixLift 3222599
  have htrace : WordTrace (prefixWord ++ tailWord_3222599) baseStart_3222599 baseEnd_3222599 := by
    simpa [prefixWord, tailWord_3222599, baseEnd_3222599] using wordTrace_append hprefix tailTrace_3222599
  have hstable : (prefixWord ++ tailWord_3222599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222599).length < 2 ^ (prefixWord ++ tailWord_3222599).sum := by decide
  have hdescent : baseEnd_3222599 < baseStart_3222599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222613 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3222613 : Nat := 118140960795 + 3222613 * 2 ^ 59
def prefixEnd_3222613 : Nat := 4983230072969 + 3 ^ 40 * 3222613 * 2
def baseEnd_3222613 : Nat := 1654749432427705245516979

theorem tailTrace_3222613 : CollatzResearch.WordTrace tailWord_3222613 prefixEnd_3222613 1654749432427705245516979 := by
  unfold tailWord_3222613
  simp only [CollatzResearch.WordTrace]
  refine ⟨117538352274030954327640493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78358901516020636218426995 117538352274030954327640493)
  ·
    refine ⟨44076882102761607872865185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117538352274030954327640493 44076882102761607872865185)
    ·
      refine ⟨33057661577071205904648889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44076882102761607872865185 33057661577071205904648889)
      ·
        refine ⟨24793246182803404428486667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33057661577071205904648889 24793246182803404428486667)
        ·
          refine ⟨37189869274205106642730001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24793246182803404428486667 37189869274205106642730001)
          ·
            refine ⟨27892401955653829982047501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37189869274205106642730001 27892401955653829982047501)
            ·
              refine ⟨10459650733370186243267813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27892401955653829982047501 10459650733370186243267813)
              ·
                refine ⟨1961184512506909920612715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10459650733370186243267813 1961184512506909920612715)
                ·
                  refine ⟨2941776768760364880919073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961184512506909920612715 2941776768760364880919073)
                  ·
                    refine ⟨2206332576570273660689305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941776768760364880919073 2206332576570273660689305)
                    ·
                      refine ⟨1654749432427705245516979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206332576570273660689305 1654749432427705245516979)
                      ·
                        rfl

theorem cell23_3222613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3222613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222613 prefixEnd_3222613 := by exact prefixLift 3222613
  have htrace : WordTrace (prefixWord ++ tailWord_3222613) baseStart_3222613 baseEnd_3222613 := by
    simpa [prefixWord, tailWord_3222613, baseEnd_3222613] using wordTrace_append hprefix tailTrace_3222613
  have hstable : (prefixWord ++ tailWord_3222613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222613).length < 2 ^ (prefixWord ++ tailWord_3222613).sum := by decide
  have hdescent : baseEnd_3222613 < baseStart_3222613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222626 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3222626 : Nat := 118140960795 + 3222626 * 2 ^ 59
def prefixEnd_3222626 : Nat := 4983230072969 + 3 ^ 40 * 3222626 * 2
def baseEnd_3222626 : Nat := 1654756107676213694654419

theorem tailTrace_3222626 : CollatzResearch.WordTrace tailWord_3222626 prefixEnd_3222626 1654756107676213694654419 := by
  unfold tailWord_3222626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29384706605745964386965933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78359217615322571698575821 29384706605745964386965933)
  ·
    refine ⟨11019264977154736645112225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29384706605745964386965933 11019264977154736645112225)
    ·
      refine ⟨8264448732866052483834169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11019264977154736645112225 8264448732866052483834169)
      ·
        refine ⟨6198336549649539362875627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8264448732866052483834169 6198336549649539362875627)
        ·
          refine ⟨9297504824474309044313441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198336549649539362875627 9297504824474309044313441)
          ·
            refine ⟨6973128618355731783235081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9297504824474309044313441 6973128618355731783235081)
            ·
              refine ⟨5229846463766798837426311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973128618355731783235081 5229846463766798837426311)
              ·
                refine ⟨7844769695650198256139467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229846463766798837426311 7844769695650198256139467)
                ·
                  refine ⟨11767154543475297384209201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844769695650198256139467 11767154543475297384209201)
                  ·
                    refine ⟨8825365907606473038156901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11767154543475297384209201 8825365907606473038156901)
                    ·
                      refine ⟨1654756107676213694654419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8825365907606473038156901 1654756107676213694654419)
                      ·
                        rfl

theorem cell23_3222626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3222626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222626 prefixEnd_3222626 := by exact prefixLift 3222626
  have htrace : WordTrace (prefixWord ++ tailWord_3222626) baseStart_3222626 baseEnd_3222626 := by
    simpa [prefixWord, tailWord_3222626, baseEnd_3222626] using wordTrace_append hprefix tailTrace_3222626
  have hstable : (prefixWord ++ tailWord_3222626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222626).length < 2 ^ (prefixWord ++ tailWord_3222626).sum := by decide
  have hdescent : baseEnd_3222626 < baseStart_3222626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222629 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3222629 : Nat := 118140960795 + 3222629 * 2 ^ 59
def prefixEnd_3222629 : Nat := 4983230072969 + 3 ^ 40 * 3222629 * 2
def baseEnd_3222629 : Nat := 1654757648118177182916905

theorem tailTrace_3222629 : CollatzResearch.WordTrace tailWord_3222629 prefixEnd_3222629 1654757648118177182916905 := by
  unfold tailWord_3222629
  simp only [CollatzResearch.WordTrace]
  refine ⟨117538935841972989060222941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78359290561315326040148627 117538935841972989060222941)
  ·
    refine ⟨44077100940739870897583603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117538935841972989060222941 44077100940739870897583603)
    ·
      refine ⟨66115651411109806346375405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44077100940739870897583603 66115651411109806346375405)
      ·
        refine ⟨24793369279166177379890777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66115651411109806346375405 24793369279166177379890777)
        ·
          refine ⟨18595026959374633034918083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24793369279166177379890777 18595026959374633034918083)
          ·
            refine ⟨27892540439061949552377125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18595026959374633034918083 27892540439061949552377125)
            ·
              refine ⟨5229851332324115541070711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27892540439061949552377125 5229851332324115541070711)
              ·
                refine ⟨7844776998486173311606067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5229851332324115541070711 7844776998486173311606067)
                ·
                  refine ⟨11767165497729259967409101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7844776998486173311606067 11767165497729259967409101)
                  ·
                    refine ⟨4412687061648472487778413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11767165497729259967409101 4412687061648472487778413)
                    ·
                      refine ⟨1654757648118177182916905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412687061648472487778413 1654757648118177182916905)
                      ·
                        rfl

theorem cell23_3222629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3222629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222629 prefixEnd_3222629 := by exact prefixLift 3222629
  have htrace : WordTrace (prefixWord ++ tailWord_3222629) baseStart_3222629 baseEnd_3222629 := by
    simpa [prefixWord, tailWord_3222629, baseEnd_3222629] using wordTrace_append hprefix tailTrace_3222629
  have hstable : (prefixWord ++ tailWord_3222629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222629).length < 2 ^ (prefixWord ++ tailWord_3222629).sum := by decide
  have hdescent : baseEnd_3222629 < baseStart_3222629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222639 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 3, 3, 2]
def baseStart_3222639 : Nat := 118140960795 + 3222639 * 2 ^ 59
def prefixEnd_3222639 : Nat := 4983230072969 + 3 ^ 40 * 3222639 * 2
def baseEnd_3222639 : Nat := 1654762782924722143791859

theorem tailTrace_3222639 : CollatzResearch.WordTrace tailWord_3222639 prefixEnd_3222639 1654762782924722143791859 := by
  unfold tailWord_3222639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117539300571936760768086971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78359533714624507178724647 117539300571936760768086971)
  ·
    refine ⟨176308950857905141152130457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117539300571936760768086971 176308950857905141152130457)
    ·
      refine ⟨132231713143428855864097843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176308950857905141152130457 132231713143428855864097843)
      ·
        refine ⟨198347569715143283796146765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132231713143428855864097843 198347569715143283796146765)
        ·
          refine ⟨74380338643178731423555037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198347569715143283796146765 74380338643178731423555037)
          ·
            refine ⟨27892626991192024283833139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74380338643178731423555037 27892626991192024283833139)
            ·
              refine ⟨41838940486788036425749709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27892626991192024283833139 41838940486788036425749709)
              ·
                refine ⟨15689602682545513659656141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41838940486788036425749709 15689602682545513659656141)
                ·
                  refine ⟨5883601005954567622371053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15689602682545513659656141 5883601005954567622371053)
                  ·
                    refine ⟨2206350377232962858389145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5883601005954567622371053 2206350377232962858389145)
                    ·
                      refine ⟨1654762782924722143791859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206350377232962858389145 1654762782924722143791859)
                      ·
                        rfl

theorem cell23_3222639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 3, 2].length) (baseStart_3222639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222639 prefixEnd_3222639 := by exact prefixLift 3222639
  have htrace : WordTrace (prefixWord ++ tailWord_3222639) baseStart_3222639 baseEnd_3222639 := by
    simpa [prefixWord, tailWord_3222639, baseEnd_3222639] using wordTrace_append hprefix tailTrace_3222639
  have hstable : (prefixWord ++ tailWord_3222639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222639).length < 2 ^ (prefixWord ++ tailWord_3222639).sum := by decide
  have hdescent : baseEnd_3222639 < baseStart_3222639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222642 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3222642 : Nat := 118140960795 + 3222642 * 2 ^ 59
def prefixEnd_3222642 : Nat := 4983230072969 + 3 ^ 40 * 3222642 * 2
def baseEnd_3222642 : Nat := 1654764323366685632054345

theorem tailTrace_3222642 : CollatzResearch.WordTrace tailWord_3222642 prefixEnd_3222642 1654764323366685632054345 := by
  unfold tailWord_3222642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29384852497731473070111545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78359606660617261520297453 29384852497731473070111545)
  ·
    refine ⟨22038639373298604802583659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29384852497731473070111545 22038639373298604802583659)
    ·
      refine ⟨33057959059947907203875489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22038639373298604802583659 33057959059947907203875489)
      ·
        refine ⟨24793469294960930402906617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33057959059947907203875489 24793469294960930402906617)
        ·
          refine ⟨18595101971220697802179963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24793469294960930402906617 18595101971220697802179963)
          ·
            refine ⟨27892652956831046703269945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18595101971220697802179963 27892652956831046703269945)
            ·
              refine ⟨20919489717623285027452459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27892652956831046703269945 20919489717623285027452459)
              ·
                refine ⟨31379234576434927541178689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20919489717623285027452459 31379234576434927541178689)
                ·
                  refine ⟨23534425932326195655884017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31379234576434927541178689 23534425932326195655884017)
                  ·
                    refine ⟨17650819449244646741913013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23534425932326195655884017 17650819449244646741913013)
                    ·
                      refine ⟨1654764323366685632054345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17650819449244646741913013 1654764323366685632054345)
                      ·
                        rfl

theorem cell23_3222642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3222642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222642 prefixEnd_3222642 := by exact prefixLift 3222642
  have htrace : WordTrace (prefixWord ++ tailWord_3222642) baseStart_3222642 baseEnd_3222642 := by
    simpa [prefixWord, tailWord_3222642, baseEnd_3222642] using wordTrace_append hprefix tailTrace_3222642
  have hstable : (prefixWord ++ tailWord_3222642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222642).length < 2 ^ (prefixWord ++ tailWord_3222642).sum := by decide
  have hdescent : baseEnd_3222642 < baseStart_3222642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222646 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3222646 : Nat := 118140960795 + 3222646 * 2 ^ 59
def prefixEnd_3222646 : Nat := 4983230072969 + 3 ^ 40 * 3222646 * 2
def baseEnd_3222646 : Nat := 1654766377289303616404327

theorem tailTrace_3222646 : CollatzResearch.WordTrace tailWord_3222646 prefixEnd_3222646 1654766377289303616404327 := by
  unfold tailWord_3222646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346222242681962560224487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78359703921940933975727861 7346222242681962560224487)
  ·
    refine ⟨11019333364022943840336731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7346222242681962560224487 11019333364022943840336731)
    ·
      refine ⟨16529000046034415760505097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11019333364022943840336731 16529000046034415760505097)
      ·
        refine ⟨12396750034525811820378823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16529000046034415760505097 12396750034525811820378823)
        ·
          refine ⟨18595125051788717730568235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12396750034525811820378823 18595125051788717730568235)
          ·
            refine ⟨27892687577683076595852353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18595125051788717730568235 27892687577683076595852353)
            ·
              refine ⟨20919515683262307446889265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27892687577683076595852353 20919515683262307446889265)
              ·
                refine ⟨15689636762446730585166949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20919515683262307446889265 15689636762446730585166949)
                ·
                  refine ⟨2941806892958761984718803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15689636762446730585166949 2941806892958761984718803)
                  ·
                    refine ⟨4412710339438142977078205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941806892958761984718803 4412710339438142977078205)
                    ·
                      refine ⟨1654766377289303616404327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412710339438142977078205 1654766377289303616404327)
                      ·
                        rfl

theorem cell23_3222646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3222646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222646 prefixEnd_3222646 := by exact prefixLift 3222646
  have htrace : WordTrace (prefixWord ++ tailWord_3222646) baseStart_3222646 baseEnd_3222646 := by
    simpa [prefixWord, tailWord_3222646, baseEnd_3222646] using wordTrace_append hprefix tailTrace_3222646
  have hstable : (prefixWord ++ tailWord_3222646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222646).length < 2 ^ (prefixWord ++ tailWord_3222646).sum := by decide
  have hdescent : baseEnd_3222646 < baseStart_3222646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222672 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3]
def baseStart_3222672 : Nat := 118140960795 + 3222672 * 2 ^ 59
def prefixEnd_3222672 : Nat := 4983230072969 + 3 ^ 40 * 3222672 * 2
def baseEnd_3222672 : Nat := 1654779727786320514679207

theorem tailTrace_3222672 : CollatzResearch.WordTrace tailWord_3222672 prefixEnd_3222672 1654779727786320514679207 := by
  unfold tailWord_3222672
  simp only [CollatzResearch.WordTrace]
  refine ⟨58770252090408603702019135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78360336120544804936025513 58770252090408603702019135)
  ·
    refine ⟨88155378135612905553028703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58770252090408603702019135 88155378135612905553028703)
    ·
      refine ⟨132233067203419358329543055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88155378135612905553028703 132233067203419358329543055)
      ·
        refine ⟨198349600805129037494314583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132233067203419358329543055 198349600805129037494314583)
        ·
          refine ⟨297524401207693556241471875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198349600805129037494314583 297524401207693556241471875)
          ·
            refine ⟨446286601811540334362207813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297524401207693556241471875 446286601811540334362207813)
            ·
              refine ⟨83678737839663812692913965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 446286601811540334362207813 83678737839663812692913965)
              ·
                refine ⟨31379526689873929759842737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83678737839663812692913965 31379526689873929759842737)
                ·
                  refine ⟨23534645017405447319882053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31379526689873929759842737 23534645017405447319882053)
                  ·
                    refine ⟨4412745940763521372477885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23534645017405447319882053 4412745940763521372477885)
                    ·
                      refine ⟨1654779727786320514679207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412745940763521372477885 1654779727786320514679207)
                      ·
                        rfl

theorem cell23_3222672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_3222672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222672 prefixEnd_3222672 := by exact prefixLift 3222672
  have htrace : WordTrace (prefixWord ++ tailWord_3222672) baseStart_3222672 baseEnd_3222672 := by
    simpa [prefixWord, tailWord_3222672, baseEnd_3222672] using wordTrace_append hprefix tailTrace_3222672
  have hstable : (prefixWord ++ tailWord_3222672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222672).length < 2 ^ (prefixWord ++ tailWord_3222672).sum := by decide
  have hdescent : baseEnd_3222672 < baseStart_3222672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222690 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3222690 : Nat := 118140960795 + 3222690 * 2 ^ 59
def prefixEnd_3222690 : Nat := 4983230072969 + 3 ^ 40 * 3222690 * 2
def baseEnd_3222690 : Nat := 1654788970438101444254125

theorem tailTrace_3222690 : CollatzResearch.WordTrace tailWord_3222690 prefixEnd_3222690 1654788970438101444254125 := by
  unfold tailWord_3222690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29385290173687999119548381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78360773796501330985462349 29385290173687999119548381)
  ·
    refine ⟨11019483815132999669830643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29385290173687999119548381 11019483815132999669830643)
    ·
      refine ⟨16529225722699499504745965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11019483815132999669830643 16529225722699499504745965)
      ·
        refine ⟨6198459646012312314279737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16529225722699499504745965 6198459646012312314279737)
        ·
          refine ⟨4648844734509234235709803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198459646012312314279737 4648844734509234235709803)
          ·
            refine ⟨6973267101763851353564705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648844734509234235709803 6973267101763851353564705)
            ·
              refine ⟨5229950326322888515173529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973267101763851353564705 5229950326322888515173529)
              ·
                refine ⟨3922462744742166386380147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229950326322888515173529 3922462744742166386380147)
                ·
                  refine ⟨5883694117113249579570221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922462744742166386380147 5883694117113249579570221)
                  ·
                    refine ⟨2206385293917468592338833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5883694117113249579570221 2206385293917468592338833)
                    ·
                      refine ⟨1654788970438101444254125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206385293917468592338833 1654788970438101444254125)
                      ·
                        rfl

theorem cell23_3222690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3222690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222690 prefixEnd_3222690 := by exact prefixLift 3222690
  have htrace : WordTrace (prefixWord ++ tailWord_3222690) baseStart_3222690 baseEnd_3222690 := by
    simpa [prefixWord, tailWord_3222690, baseEnd_3222690] using wordTrace_append hprefix tailTrace_3222690
  have hstable : (prefixWord ++ tailWord_3222690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222690).length < 2 ^ (prefixWord ++ tailWord_3222690).sum := by decide
  have hdescent : baseEnd_3222690 < baseStart_3222690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222813 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3222813 : Nat := 118140960795 + 3222813 * 2 ^ 59
def prefixEnd_3222813 : Nat := 4983230072969 + 3 ^ 40 * 3222813 * 2
def baseEnd_3222813 : Nat := 1654852128558604463016059

theorem tailTrace_3222813 : CollatzResearch.WordTrace tailWord_3222813 prefixEnd_3222813 1654852128558604463016059 := by
  unfold tailWord_3222813
  simp only [CollatzResearch.WordTrace]
  refine ⟨117545646873306388484921093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78363764582204258989947395 117545646873306388484921093)
  ·
    refine ⟨22039808788744947840922705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117545646873306388484921093 22039808788744947840922705)
    ·
      refine ⟨16529856591558710880692029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22039808788744947840922705 16529856591558710880692029)
      ·
        refine ⟨6198696221834516580259511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16529856591558710880692029 6198696221834516580259511)
        ·
          refine ⟨9298044332751774870389267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198696221834516580259511 9298044332751774870389267)
          ·
            refine ⟨13947066499127662305583901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9298044332751774870389267 13947066499127662305583901)
            ·
              refine ⟨5230149937172873364593963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13947066499127662305583901 5230149937172873364593963)
              ·
                refine ⟨7845224905759310046890945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230149937172873364593963 7845224905759310046890945)
                ·
                  refine ⟨5883918679319482535168209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7845224905759310046890945 5883918679319482535168209)
                  ·
                    refine ⟨4412939009489611901376157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5883918679319482535168209 4412939009489611901376157)
                    ·
                      refine ⟨1654852128558604463016059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4412939009489611901376157 1654852128558604463016059)
                      ·
                        rfl

theorem cell23_3222813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3222813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222813 prefixEnd_3222813 := by exact prefixLift 3222813
  have htrace : WordTrace (prefixWord ++ tailWord_3222813) baseStart_3222813 baseEnd_3222813 := by
    simpa [prefixWord, tailWord_3222813, baseEnd_3222813] using wordTrace_append hprefix tailTrace_3222813
  have hstable : (prefixWord ++ tailWord_3222813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222813).length < 2 ^ (prefixWord ++ tailWord_3222813).sum := by decide
  have hdescent : baseEnd_3222813 < baseStart_3222813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222866 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_3222866 : Nat := 118140960795 + 3222866 * 2 ^ 59
def prefixEnd_3222866 : Nat := 4983230072969 + 3 ^ 40 * 3222866 * 2
def baseEnd_3222866 : Nat := 1654879343033292755653315

theorem tailTrace_3222866 : CollatzResearch.WordTrace tailWord_3222866 prefixEnd_3222866 1654879343033292755653315 := by
  unfold tailWord_3222866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386894985528594634150113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78365053294742919024400301 29386894985528594634150113)
  ·
    refine ⟨22040171239146445975612585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29386894985528594634150113 22040171239146445975612585)
    ·
      refine ⟨16530128429359834481709439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22040171239146445975612585 16530128429359834481709439)
      ·
        refine ⟨24795192644039751722564159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16530128429359834481709439 24795192644039751722564159)
        ·
          refine ⟨37192788966059627583846239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24795192644039751722564159 37192788966059627583846239)
          ·
            refine ⟨55789183449089441375769359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37192788966059627583846239 55789183449089441375769359)
            ·
              refine ⟨83683775173634162063654039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55789183449089441375769359 83683775173634162063654039)
              ·
                refine ⟨125525662760451243095481059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83683775173634162063654039 125525662760451243095481059)
                ·
                  refine ⟨188288494140676864643221589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125525662760451243095481059 188288494140676864643221589)
                  ·
                    refine ⟨2206505790711057007537753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 188288494140676864643221589 2206505790711057007537753)
                    ·
                      refine ⟨1654879343033292755653315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206505790711057007537753 1654879343033292755653315)
                      ·
                        rfl

theorem cell23_3222866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_3222866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222866 prefixEnd_3222866 := by exact prefixLift 3222866
  have htrace : WordTrace (prefixWord ++ tailWord_3222866) baseStart_3222866 baseEnd_3222866 := by
    simpa [prefixWord, tailWord_3222866, baseEnd_3222866] using wordTrace_append hprefix tailTrace_3222866
  have hstable : (prefixWord ++ tailWord_3222866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222866).length < 2 ^ (prefixWord ++ tailWord_3222866).sum := by decide
  have hdescent : baseEnd_3222866 < baseStart_3222866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222879 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3222879 : Nat := 118140960795 + 3222879 * 2 ^ 59
def prefixEnd_3222879 : Nat := 4983230072969 + 3 ^ 40 * 3222879 * 2
def baseEnd_3222879 : Nat := 1654886018281801204790755

theorem tailTrace_3222879 : CollatzResearch.WordTrace tailWord_3222879 prefixEnd_3222879 1654886018281801204790755 := by
  unfold tailWord_3222879
  simp only [CollatzResearch.WordTrace]
  refine ⟨117548054091067281756823691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78365369394044854504549127 117548054091067281756823691)
  ·
    refine ⟨176322081136600922635235537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117548054091067281756823691 176322081136600922635235537)
    ·
      refine ⟨132241560852450691976426653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176322081136600922635235537 132241560852450691976426653)
      ·
        refine ⟨49590585319669009491159995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132241560852450691976426653 49590585319669009491159995)
        ·
          refine ⟨74385877979503514236739993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49590585319669009491159995 74385877979503514236739993)
          ·
            refine ⟨55789408484627635677554995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74385877979503514236739993 55789408484627635677554995)
            ·
              refine ⟨83684112726941453516332493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55789408484627635677554995 83684112726941453516332493)
              ·
                refine ⟨31381542272603045068624685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83684112726941453516332493 31381542272603045068624685)
                ·
                  refine ⟨11768078352226141900734257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31381542272603045068624685 11768078352226141900734257)
                  ·
                    refine ⟨8826058764169606425550693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11768078352226141900734257 8826058764169606425550693)
                    ·
                      refine ⟨1654886018281801204790755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8826058764169606425550693 1654886018281801204790755)
                      ·
                        rfl

theorem cell23_3222879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3222879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222879 prefixEnd_3222879 := by exact prefixLift 3222879
  have htrace : WordTrace (prefixWord ++ tailWord_3222879) baseStart_3222879 baseEnd_3222879 := by
    simpa [prefixWord, tailWord_3222879, baseEnd_3222879] using wordTrace_append hprefix tailTrace_3222879
  have hstable : (prefixWord ++ tailWord_3222879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222879).length < 2 ^ (prefixWord ++ tailWord_3222879).sum := by decide
  have hdescent : baseEnd_3222879 < baseStart_3222879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222894 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3222894 : Nat := 118140960795 + 3222894 * 2 ^ 59
def prefixEnd_3222894 : Nat := 4983230072969 + 3 ^ 40 * 3222894 * 2
def baseEnd_3222894 : Nat := 1654893720491618646103187

theorem tailTrace_3222894 : CollatzResearch.WordTrace tailWord_3222894 prefixEnd_3222894 1654893720491618646103187 := by
  unfold tailWord_3222894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693575148251617414827467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78365734124008626212413157 14693575148251617414827467)
  ·
    refine ⟨22040362722377426122241201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14693575148251617414827467 22040362722377426122241201)
    ·
      refine ⟨16530272041783069591680901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22040362722377426122241201 16530272041783069591680901)
      ·
        refine ⟨3099426007834325548440169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16530272041783069591680901 3099426007834325548440169)
        ·
          refine ⟨2324569505875744161330127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3099426007834325548440169 2324569505875744161330127)
          ·
            refine ⟨3486854258813616241995191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324569505875744161330127 3486854258813616241995191)
            ·
              refine ⟨5230281388220424362992787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486854258813616241995191 5230281388220424362992787)
              ·
                refine ⟨7845422082330636544489181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230281388220424362992787 7845422082330636544489181)
                ·
                  refine ⟨2942033280873988704183443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7845422082330636544489181 2942033280873988704183443)
                  ·
                    refine ⟨4413049921310983056275165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2942033280873988704183443 4413049921310983056275165)
                    ·
                      refine ⟨1654893720491618646103187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4413049921310983056275165 1654893720491618646103187)
                      ·
                        rfl

theorem cell23_3222894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3222894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222894 prefixEnd_3222894 := by exact prefixLift 3222894
  have htrace : WordTrace (prefixWord ++ tailWord_3222894) baseStart_3222894 baseEnd_3222894 := by
    simpa [prefixWord, tailWord_3222894, baseEnd_3222894] using wordTrace_append hprefix tailTrace_3222894
  have hstable : (prefixWord ++ tailWord_3222894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222894).length < 2 ^ (prefixWord ++ tailWord_3222894).sum := by decide
  have hdescent : baseEnd_3222894 < baseStart_3222894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222899 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3]
def baseStart_3222899 : Nat := 118140960795 + 3222899 * 2 ^ 59
def prefixEnd_3222899 : Nat := 4983230072969 + 3 ^ 40 * 3222899 * 2
def baseEnd_3222899 : Nat := 1654896287894891126540663

theorem tailTrace_3222899 : CollatzResearch.WordTrace tailWord_3222899 prefixEnd_3222899 1654896287894891126540663 := by
  unfold tailWord_3222899
  simp only [CollatzResearch.WordTrace]
  refine ⟨117548783550994825172551751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78365855700663216781701167 117548783550994825172551751)
  ·
    refine ⟨176323175326492237758827627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117548783550994825172551751 176323175326492237758827627)
    ·
      refine ⟨264484762989738356638241441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176323175326492237758827627 264484762989738356638241441)
      ·
        refine ⟨198363572242303767478681081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264484762989738356638241441 198363572242303767478681081)
        ·
          refine ⟨148772679181727825609010811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198363572242303767478681081 148772679181727825609010811)
          ·
            refine ⟨223159018772591738413516217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148772679181727825609010811 223159018772591738413516217)
            ·
              refine ⟨167369264079443803810137163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223159018772591738413516217 167369264079443803810137163)
              ·
                refine ⟨251053896119165705715205745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167369264079443803810137163 251053896119165705715205745)
                ·
                  refine ⟨188290422089374279286404309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251053896119165705715205745 188290422089374279286404309)
                  ·
                    refine ⟨4413056767719709670775101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188290422089374279286404309 4413056767719709670775101)
                    ·
                      refine ⟨1654896287894891126540663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4413056767719709670775101 1654896287894891126540663)
                      ·
                        rfl

theorem cell23_3222899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_3222899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222899 prefixEnd_3222899 := by exact prefixLift 3222899
  have htrace : WordTrace (prefixWord ++ tailWord_3222899) baseStart_3222899 baseEnd_3222899 := by
    simpa [prefixWord, tailWord_3222899, baseEnd_3222899] using wordTrace_append hprefix tailTrace_3222899
  have hstable : (prefixWord ++ tailWord_3222899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222899).length < 2 ^ (prefixWord ++ tailWord_3222899).sum := by decide
  have hdescent : baseEnd_3222899 < baseStart_3222899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222909 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3222909 : Nat := 118140960795 + 3222909 * 2 ^ 59
def prefixEnd_3222909 : Nat := 4983230072969 + 3 ^ 40 * 3222909 * 2
def baseEnd_3222909 : Nat := 1654901422701436087415617

theorem tailTrace_3222909 : CollatzResearch.WordTrace tailWord_3222909 prefixEnd_3222909 1654901422701436087415617 := by
  unfold tailWord_3222909
  simp only [CollatzResearch.WordTrace]
  refine ⟨117549148280958596880415781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78366098853972397920277187 117549148280958596880415781)
  ·
    refine ⟨22040465302679736915077959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117549148280958596880415781 22040465302679736915077959)
    ·
      refine ⟨33060697954019605372616939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22040465302679736915077959 33060697954019605372616939)
      ·
        refine ⟨49591046931029408058925409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33060697954019605372616939 49591046931029408058925409)
        ·
          refine ⟨37193285198272056044194057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49591046931029408058925409 37193285198272056044194057)
          ·
            refine ⟨27894963898704042033145543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37193285198272056044194057 27894963898704042033145543)
            ·
              refine ⟨41842445848056063049718315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27894963898704042033145543 41842445848056063049718315)
              ·
                refine ⟨62763668772084094574577473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41842445848056063049718315 62763668772084094574577473)
                ·
                  refine ⟨47072751579063070930933105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62763668772084094574577473 47072751579063070930933105)
                  ·
                    refine ⟨35304563684297303198199829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47072751579063070930933105 35304563684297303198199829)
                    ·
                      refine ⟨1654901422701436087415617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35304563684297303198199829 1654901422701436087415617)
                      ·
                        rfl

theorem cell23_3222909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3222909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222909 prefixEnd_3222909 := by exact prefixLift 3222909
  have htrace : WordTrace (prefixWord ++ tailWord_3222909) baseStart_3222909 baseEnd_3222909 := by
    simpa [prefixWord, tailWord_3222909, baseEnd_3222909] using wordTrace_append hprefix tailTrace_3222909
  have hstable : (prefixWord ++ tailWord_3222909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222909).length < 2 ^ (prefixWord ++ tailWord_3222909).sum := by decide
  have hdescent : baseEnd_3222909 < baseStart_3222909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222920 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3222920 : Nat := 118140960795 + 3222920 * 2 ^ 59
def prefixEnd_3222920 : Nat := 4983230072969 + 3 ^ 40 * 3222920 * 2
def baseEnd_3222920 : Nat := 1654907070988635544378067

theorem tailTrace_3222920 : CollatzResearch.WordTrace tailWord_3222920 prefixEnd_3222920 1654907070988635544378067 := by
  unfold tailWord_3222920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58774774741959372879533107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78366366322612497172710809 58774774741959372879533107)
  ·
    refine ⟨88162162112939059319299661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58774774741959372879533107 88162162112939059319299661)
    ·
      refine ⟨33060810792352147244737373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88162162112939059319299661 33060810792352147244737373)
      ·
        refine ⟨12397804047132055216776515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33060810792352147244737373 12397804047132055216776515)
        ·
          refine ⟨18596706070698082825164773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12397804047132055216776515 18596706070698082825164773)
          ·
            refine ⟨3486882388255890529718395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18596706070698082825164773 3486882388255890529718395)
            ·
              refine ⟨5230323582383835794577593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3486882388255890529718395 5230323582383835794577593)
              ·
                refine ⟨3922742686787876845933195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5230323582383835794577593 3922742686787876845933195)
                ·
                  refine ⟨5884114030181815268899793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922742686787876845933195 5884114030181815268899793)
                  ·
                    refine ⟨4413085522636361451674845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5884114030181815268899793 4413085522636361451674845)
                    ·
                      refine ⟨1654907070988635544378067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4413085522636361451674845 1654907070988635544378067)
                      ·
                        rfl

theorem cell23_3222920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3222920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222920 prefixEnd_3222920 := by exact prefixLift 3222920
  have htrace : WordTrace (prefixWord ++ tailWord_3222920) baseStart_3222920 baseEnd_3222920 := by
    simpa [prefixWord, tailWord_3222920, baseEnd_3222920] using wordTrace_append hprefix tailTrace_3222920
  have hstable : (prefixWord ++ tailWord_3222920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222920).length < 2 ^ (prefixWord ++ tailWord_3222920).sum := by decide
  have hdescent : baseEnd_3222920 < baseStart_3222920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222930 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3222930 : Nat := 118140960795 + 3222930 * 2 ^ 59
def prefixEnd_3222930 : Nat := 4983230072969 + 3 ^ 40 * 3222930 * 2
def baseEnd_3222930 : Nat := 1654912205795180505253021

theorem tailTrace_3222930 : CollatzResearch.WordTrace tailWord_3222930 prefixEnd_3222930 1654912205795180505253021 := by
  unfold tailWord_3222930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29387478553470629366732561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78366609475921678311286829 29387478553470629366732561)
  ·
    refine ⟨22040608915102972025049421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29387478553470629366732561 22040608915102972025049421)
    ·
      refine ⟨8265228343163614509393533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22040608915102972025049421 8265228343163614509393533)
      ·
        refine ⟨3099460628686355441022575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8265228343163614509393533 3099460628686355441022575)
        ·
          refine ⟨4649190943029533161533863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099460628686355441022575 4649190943029533161533863)
          ·
            refine ⟨6973786414544299742300795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649190943029533161533863 6973786414544299742300795)
            ·
              refine ⟨10460679621816449613451193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973786414544299742300795 10460679621816449613451193)
              ·
                refine ⟨7845509716362337210088395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10460679621816449613451193 7845509716362337210088395)
                ·
                  refine ⟨11768264574543505815132593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7845509716362337210088395 11768264574543505815132593)
                  ·
                    refine ⟨8826198430907629361349445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11768264574543505815132593 8826198430907629361349445)
                    ·
                      refine ⟨1654912205795180505253021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8826198430907629361349445 1654912205795180505253021)
                      ·
                        rfl

theorem cell23_3222930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3222930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222930 prefixEnd_3222930 := by exact prefixLift 3222930
  have htrace : WordTrace (prefixWord ++ tailWord_3222930) baseStart_3222930 baseEnd_3222930 := by
    simpa [prefixWord, tailWord_3222930, baseEnd_3222930] using wordTrace_append hprefix tailTrace_3222930
  have hstable : (prefixWord ++ tailWord_3222930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222930).length < 2 ^ (prefixWord ++ tailWord_3222930).sum := by decide
  have hdescent : baseEnd_3222930 < baseStart_3222930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222959 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_3222959 : Nat := 118140960795 + 3222959 * 2 ^ 59
def prefixEnd_3222959 : Nat := 4983230072969 + 3 ^ 40 * 3222959 * 2
def baseEnd_3222959 : Nat := 1654927096734160891790387

theorem tailTrace_3222959 : CollatzResearch.WordTrace tailWord_3222959 prefixEnd_3222959 1654927096734160891790387 := by
  unfold tailWord_3222959
  simp only [CollatzResearch.WordTrace]
  refine ⟨117550971930777455419735931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78367314620518303613157287 117550971930777455419735931)
  ·
    refine ⟨176326457896166183129603897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117550971930777455419735931 176326457896166183129603897)
    ·
      refine ⟨132244843422124637347202923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176326457896166183129603897 132244843422124637347202923)
      ·
        refine ⟨198367265133186956020804385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132244843422124637347202923 198367265133186956020804385)
        ·
          refine ⟨148775448849890217015603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198367265133186956020804385 148775448849890217015603289)
          ·
            refine ⟨111581586637417662761702467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148775448849890217015603289 111581586637417662761702467)
            ·
              refine ⟨167372379956126494142553701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111581586637417662761702467 167372379956126494142553701)
              ·
                refine ⟨31382321241773717651728819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167372379956126494142553701 31382321241773717651728819)
                ·
                  refine ⟨47073481862660576477593229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31382321241773717651728819 47073481862660576477593229)
                  ·
                    refine ⟨17652555698497716179097461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47073481862660576477593229 17652555698497716179097461)
                    ·
                      refine ⟨1654927096734160891790387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17652555698497716179097461 1654927096734160891790387)
                      ·
                        rfl

theorem cell23_3222959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_3222959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222959 prefixEnd_3222959 := by exact prefixLift 3222959
  have htrace : WordTrace (prefixWord ++ tailWord_3222959) baseStart_3222959 baseEnd_3222959 := by
    simpa [prefixWord, tailWord_3222959, baseEnd_3222959] using wordTrace_append hprefix tailTrace_3222959
  have hstable : (prefixWord ++ tailWord_3222959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222959).length < 2 ^ (prefixWord ++ tailWord_3222959).sum := by decide
  have hdescent : baseEnd_3222959 < baseStart_3222959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3222979 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 9]
def baseStart_3222979 : Nat := 118140960795 + 3222979 * 2 ^ 59
def prefixEnd_3222979 : Nat := 4983230072969 + 3 ^ 40 * 3222979 * 2
def baseEnd_3222979 : Nat := 183881929594138979282255

theorem tailTrace_3222979 : CollatzResearch.WordTrace tailWord_3222979 prefixEnd_3222979 183881929594138979282255 := by
  unfold tailWord_3222979
  simp only [CollatzResearch.WordTrace]
  refine ⟨117551701390704998835463991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78367800927136665890309327 117551701390704998835463991)
  ·
    refine ⟨176327552086057498253195987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117551701390704998835463991 176327552086057498253195987)
    ·
      refine ⟨264491328129086247379793981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176327552086057498253195987 264491328129086247379793981)
      ·
        refine ⟨99184248048407342767422743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264491328129086247379793981 99184248048407342767422743)
        ·
          refine ⟨148776372072611014151134115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99184248048407342767422743 148776372072611014151134115)
          ·
            refine ⟨223164558108916521226701173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148776372072611014151134115 223164558108916521226701173)
            ·
              refine ⟨20921677322710923865003235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223164558108916521226701173 20921677322710923865003235)
              ·
                refine ⟨31382515984066385797504853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20921677322710923865003235 31382515984066385797504853)
                ·
                  refine ⟨183881929594138979282255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31382515984066385797504853 183881929594138979282255)
                  ·
                    rfl

theorem cell23_3222979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 9].length) (baseStart_3222979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3222979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3222979 prefixEnd_3222979 := by exact prefixLift 3222979
  have htrace : WordTrace (prefixWord ++ tailWord_3222979) baseStart_3222979 baseEnd_3222979 := by
    simpa [prefixWord, tailWord_3222979, baseEnd_3222979] using wordTrace_append hprefix tailTrace_3222979
  have hstable : (prefixWord ++ tailWord_3222979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3222979).length < 2 ^ (prefixWord ++ tailWord_3222979).sum := by decide
  have hdescent : baseEnd_3222979 < baseStart_3222979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3222979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223013 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 7]
def baseStart_3223013 : Nat := 118140960795 + 3223013 * 2 ^ 59
def prefixEnd_3223013 : Nat := 4983230072969 + 3 ^ 40 * 3223013 * 2
def baseEnd_3223013 : Nat := 183883869409944853390571

theorem tailTrace_3223013 : CollatzResearch.WordTrace tailWord_3223013 prefixEnd_3223013 183883869409944853390571 := by
  unfold tailWord_3223013
  simp only [CollatzResearch.WordTrace]
  refine ⟨117552941472581822642201693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78368627648387881761467795 117552941472581822642201693)
  ·
    refine ⟨44082353052218183490825635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117552941472581822642201693 44082353052218183490825635)
    ·
      refine ⟨66123529578327275236238453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44082353052218183490825635 66123529578327275236238453)
      ·
        refine ⟨6199080897968182053397355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66123529578327275236238453 6199080897968182053397355)
        ·
          refine ⟨9298621346952273080096033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199080897968182053397355 9298621346952273080096033)
          ·
            refine ⟨6973966010214204810072025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9298621346952273080096033 6973966010214204810072025)
            ·
              refine ⟨5230474507660653607554019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6973966010214204810072025 5230474507660653607554019)
              ·
                refine ⟨7845711761490980411331029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230474507660653607554019 7845711761490980411331029)
                ·
                  refine ⟨183883869409944853390571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7845711761490980411331029 183883869409944853390571)
                  ·
                    rfl

theorem cell23_3223013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_3223013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223013 prefixEnd_3223013 := by exact prefixLift 3223013
  have htrace : WordTrace (prefixWord ++ tailWord_3223013) baseStart_3223013 baseEnd_3223013 := by
    simpa [prefixWord, tailWord_3223013, baseEnd_3223013] using wordTrace_append hprefix tailTrace_3223013
  have hstable : (prefixWord ++ tailWord_3223013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223013).length < 2 ^ (prefixWord ++ tailWord_3223013).sum := by decide
  have hdescent : baseEnd_3223013 < baseStart_3223013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223157 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3223157 : Nat := 118140960795 + 3223157 * 2 ^ 59
def prefixEnd_3223157 : Nat := 4983230072969 + 3 ^ 40 * 3223157 * 2
def baseEnd_3223157 : Nat := 1655028765903751117114477

theorem tailTrace_3223157 : CollatzResearch.WordTrace tailWord_3223157 prefixEnd_3223157 1655028765903751117114477 := by
  unfold tailWord_3223157
  simp only [CollatzResearch.WordTrace]
  refine ⟨117558193584060135235443725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78372129056040090156962483 117558193584060135235443725)
  ·
    refine ⟨44084322594022550713291397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117558193584060135235443725 44084322594022550713291397)
    ·
      refine ⟨8265810486379228258742137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44084322594022550713291397 8265810486379228258742137)
      ·
        refine ⟨6199357864784421194056603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8265810486379228258742137 6199357864784421194056603)
        ·
          refine ⟨9299036797176631791084905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199357864784421194056603 9299036797176631791084905)
          ·
            refine ⟨6974277597882473843313679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9299036797176631791084905 6974277597882473843313679)
            ·
              refine ⟨10461416396823710764970519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6974277597882473843313679 10461416396823710764970519)
              ·
                refine ⟨15692124595235566147455779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10461416396823710764970519 15692124595235566147455779)
                ·
                  refine ⟨23538186892853349221183669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15692124595235566147455779 23538186892853349221183669)
                  ·
                    refine ⟨2206705021205001489485969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23538186892853349221183669 2206705021205001489485969)
                    ·
                      refine ⟨1655028765903751117114477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206705021205001489485969 1655028765903751117114477)
                      ·
                        rfl

theorem cell23_3223157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3223157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223157 prefixEnd_3223157 := by exact prefixLift 3223157
  have htrace : WordTrace (prefixWord ++ tailWord_3223157) baseStart_3223157 baseEnd_3223157 := by
    simpa [prefixWord, tailWord_3223157, baseEnd_3223157] using wordTrace_append hprefix tailTrace_3223157
  have hstable : (prefixWord ++ tailWord_3223157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223157).length < 2 ^ (prefixWord ++ tailWord_3223157).sum := by decide
  have hdescent : baseEnd_3223157 < baseStart_3223157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223163 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 4, 4]
def baseStart_3223163 : Nat := 118140960795 + 3223163 * 2 ^ 59
def prefixEnd_3223163 : Nat := 4983230072969 + 3 ^ 40 * 3223163 * 2
def baseEnd_3223163 : Nat := 551677282262559364546483

theorem tailTrace_3223163 : CollatzResearch.WordTrace tailWord_3223163 prefixEnd_3223163 551677282262559364546483 := by
  unfold tailWord_3223163
  simp only [CollatzResearch.WordTrace]
  refine ⟨117558412422038398260162143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78372274948025598840108095 117558412422038398260162143)
  ·
    refine ⟨176337618633057597390243215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117558412422038398260162143 176337618633057597390243215)
    ·
      refine ⟨264506427949586396085364823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176337618633057597390243215 264506427949586396085364823)
      ·
        refine ⟨396759641924379594128047235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264506427949586396085364823 396759641924379594128047235)
        ·
          refine ⟨595139462886569391192070853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396759641924379594128047235 595139462886569391192070853)
          ·
            refine ⟨111588649291231760848513285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 595139462886569391192070853 111588649291231760848513285)
            ·
              refine ⟨20922871742105955159096241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111588649291231760848513285 20922871742105955159096241)
              ·
                refine ⟨15692153806579466369322181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20922871742105955159096241 15692153806579466369322181)
                ·
                  refine ⟨2942278838733649944247909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15692153806579466369322181 2942278838733649944247909)
                  ·
                    refine ⟨551677282262559364546483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2942278838733649944247909 551677282262559364546483)
                    ·
                      rfl

theorem cell23_3223163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 4].length) (baseStart_3223163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223163 prefixEnd_3223163 := by exact prefixLift 3223163
  have htrace : WordTrace (prefixWord ++ tailWord_3223163) baseStart_3223163 baseEnd_3223163 := by
    simpa [prefixWord, tailWord_3223163, baseEnd_3223163] using wordTrace_append hprefix tailTrace_3223163
  have hstable : (prefixWord ++ tailWord_3223163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223163).length < 2 ^ (prefixWord ++ tailWord_3223163).sum := by decide
  have hdescent : baseEnd_3223163 < baseStart_3223163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223173 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_3223173 : Nat := 118140960795 + 3223173 * 2 ^ 59
def prefixEnd_3223173 : Nat := 4983230072969 + 3 ^ 40 * 3223173 * 2
def baseEnd_3223173 : Nat := 1655036981594223054514403

theorem tailTrace_3223173 : CollatzResearch.WordTrace tailWord_3223173 prefixEnd_3223173 1655036981594223054514403 := by
  unfold tailWord_3223173
  simp only [CollatzResearch.WordTrace]
  refine ⟨117558777152002169968026173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78372518101334779978684115 117558777152002169968026173)
  ·
    refine ⟨44084541432000813738009815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117558777152002169968026173 44084541432000813738009815)
    ·
      refine ⟨66126812148001220607014723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44084541432000813738009815 66126812148001220607014723)
      ·
        refine ⟨99190218222001830910522085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66126812148001220607014723 99190218222001830910522085)
        ·
          refine ⟨18598165916625343295722891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99190218222001830910522085 18598165916625343295722891)
          ·
            refine ⟨27897248874938014943584337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18598165916625343295722891 27897248874938014943584337)
            ·
              refine ⟨20922936656203511207688253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27897248874938014943584337 20922936656203511207688253)
              ·
                refine ⟨7846101246076316702883095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20922936656203511207688253 7846101246076316702883095)
                ·
                  refine ⟨11769151869114475054324643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846101246076316702883095 11769151869114475054324643)
                  ·
                    refine ⟨17653727803671712581486965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11769151869114475054324643 17653727803671712581486965)
                    ·
                      refine ⟨1655036981594223054514403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17653727803671712581486965 1655036981594223054514403)
                      ·
                        rfl

theorem cell23_3223173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_3223173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223173 prefixEnd_3223173 := by exact prefixLift 3223173
  have htrace : WordTrace (prefixWord ++ tailWord_3223173) baseStart_3223173 baseEnd_3223173 := by
    simpa [prefixWord, tailWord_3223173, baseEnd_3223173] using wordTrace_append hprefix tailTrace_3223173
  have hstable : (prefixWord ++ tailWord_3223173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223173).length < 2 ^ (prefixWord ++ tailWord_3223173).sum := by decide
  have hdescent : baseEnd_3223173 < baseStart_3223173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223200 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3223200 : Nat := 118140960795 + 3223200 * 2 ^ 59
def prefixEnd_3223200 : Nat := 4983230072969 + 3 ^ 40 * 3223200 * 2
def baseEnd_3223200 : Nat := 1655050845571894448876779

theorem tailTrace_3223200 : CollatzResearch.WordTrace tailWord_3223200 prefixEnd_3223200 1655050845571894448876779 := by
  unfold tailWord_3223200
  simp only [CollatzResearch.WordTrace]
  refine ⟨58779880961452176789629527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78373174615269569052839369 58779880961452176789629527)
  ·
    refine ⟨88169821442178265184444291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58779880961452176789629527 88169821442178265184444291)
    ·
      refine ⟨132254732163267397776666437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88169821442178265184444291 132254732163267397776666437)
      ·
        refine ⟨24797762280612637083124957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132254732163267397776666437 24797762280612637083124957)
        ·
          refine ⟨9299160855229738906171859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24797762280612637083124957 9299160855229738906171859)
          ·
            refine ⟨13948741282844608359257789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9299160855229738906171859 13948741282844608359257789)
            ·
              refine ⟨5230777981066728134721671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13948741282844608359257789 5230777981066728134721671)
              ·
                refine ⟨7846166971600092202082507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230777981066728134721671 7846166971600092202082507)
                ·
                  refine ⟨11769250457400138303123761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846166971600092202082507 11769250457400138303123761)
                  ·
                    refine ⟨8826937843050103727342821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11769250457400138303123761 8826937843050103727342821)
                    ·
                      refine ⟨1655050845571894448876779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8826937843050103727342821 1655050845571894448876779)
                      ·
                        rfl

theorem cell23_3223200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3223200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223200 prefixEnd_3223200 := by exact prefixLift 3223200
  have htrace : WordTrace (prefixWord ++ tailWord_3223200) baseStart_3223200 baseEnd_3223200 := by
    simpa [prefixWord, tailWord_3223200, baseEnd_3223200] using wordTrace_append hprefix tailTrace_3223200
  have hstable : (prefixWord ++ tailWord_3223200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223200).length < 2 ^ (prefixWord ++ tailWord_3223200).sum := by decide
  have hdescent : baseEnd_3223200 < baseStart_3223200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223238 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3223238 : Nat := 118140960795 + 3223238 * 2 ^ 59
def prefixEnd_3223238 : Nat := 4983230072969 + 3 ^ 40 * 3223238 * 2
def baseEnd_3223238 : Nat := 1655070357836765300201605

theorem tailTrace_3223238 : CollatzResearch.WordTrace tailWord_3223238 prefixEnd_3223238 1655070357836765300201605 := by
  unfold tailWord_3223238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673785871773958939660699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78374098597844457379428245 3673785871773958939660699)
  ·
    refine ⟨5510678807660938409491049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673785871773958939660699 5510678807660938409491049)
    ·
      refine ⟨4133009105745703807118287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5510678807660938409491049 4133009105745703807118287)
      ·
        refine ⟨6199513658618555710677431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133009105745703807118287 6199513658618555710677431)
        ·
          refine ⟨9299270487927833566016147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199513658618555710677431 9299270487927833566016147)
          ·
            refine ⟨13948905731891750349024221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9299270487927833566016147 13948905731891750349024221)
            ·
              refine ⟨5230839649459406380884083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13948905731891750349024221 5230839649459406380884083)
              ·
                refine ⟨7846259474189109571326125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5230839649459406380884083 7846259474189109571326125)
                ·
                  refine ⟨2942347302820916089247297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7846259474189109571326125 2942347302820916089247297)
                  ·
                    refine ⟨2206760477115687066935473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2942347302820916089247297 2206760477115687066935473)
                    ·
                      refine ⟨1655070357836765300201605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206760477115687066935473 1655070357836765300201605)
                      ·
                        rfl

theorem cell23_3223238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3223238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223238 prefixEnd_3223238 := by exact prefixLift 3223238
  have htrace : WordTrace (prefixWord ++ tailWord_3223238) baseStart_3223238 baseEnd_3223238 := by
    simpa [prefixWord, tailWord_3223238, baseEnd_3223238] using wordTrace_append hprefix tailTrace_3223238
  have hstable : (prefixWord ++ tailWord_3223238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223238).length < 2 ^ (prefixWord ++ tailWord_3223238).sum := by decide
  have hdescent : baseEnd_3223238 < baseStart_3223238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223263 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3223263 : Nat := 118140960795 + 3223263 * 2 ^ 59
def prefixEnd_3223263 : Nat := 4983230072969 + 3 ^ 40 * 3223263 * 2
def baseEnd_3223263 : Nat := 1655083194853127702388989

theorem tailTrace_3223263 : CollatzResearch.WordTrace tailWord_3223263 prefixEnd_3223263 1655083194853127702388989 := by
  unfold tailWord_3223263
  simp only [CollatzResearch.WordTrace]
  refine ⟨117562059721676115338802443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78374706481117410225868295 117562059721676115338802443)
  ·
    refine ⟨176343089582514173008203665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117562059721676115338802443 176343089582514173008203665)
    ·
      refine ⟨132257317186885629756152749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176343089582514173008203665 132257317186885629756152749)
      ·
        refine ⟨49596493945082111158557281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132257317186885629756152749 49596493945082111158557281)
        ·
          refine ⟨37197370458811583368917961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49596493945082111158557281 37197370458811583368917961)
          ·
            refine ⟨27898027844108687526688471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37197370458811583368917961 27898027844108687526688471)
            ·
              refine ⟨41847041766163031290032707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27898027844108687526688471 41847041766163031290032707)
              ·
                refine ⟨62770562649244546935049061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41847041766163031290032707 62770562649244546935049061)
                ·
                  refine ⟨11769480496733352550321699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62770562649244546935049061 11769480496733352550321699)
                  ·
                    refine ⟨17654220745100028825482549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11769480496733352550321699 17654220745100028825482549)
                    ·
                      refine ⟨1655083194853127702388989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17654220745100028825482549 1655083194853127702388989)
                      ·
                        rfl

theorem cell23_3223263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3223263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223263 prefixEnd_3223263 := by exact prefixLift 3223263
  have htrace : WordTrace (prefixWord ++ tailWord_3223263) baseStart_3223263 baseEnd_3223263 := by
    simpa [prefixWord, tailWord_3223263, baseEnd_3223263] using wordTrace_append hprefix tailTrace_3223263
  have hstable : (prefixWord ++ tailWord_3223263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223263).length < 2 ^ (prefixWord ++ tailWord_3223263).sum := by decide
  have hdescent : baseEnd_3223263 < baseStart_3223263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223273 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_3223273 : Nat := 118140960795 + 3223273 * 2 ^ 59
def prefixEnd_3223273 : Nat := 4983230072969 + 3 ^ 40 * 3223273 * 2
def baseEnd_3223273 : Nat := 1655088329659672663263943

theorem tailTrace_3223273 : CollatzResearch.WordTrace tailWord_3223273 prefixEnd_3223273 1655088329659672663263943 := by
  unfold tailWord_3223273
  simp only [CollatzResearch.WordTrace]
  refine ⟨117562424451639887046666473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78374949634426591364444315 117562424451639887046666473)
  ·
    refine ⟨88171818338729915284999855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117562424451639887046666473 88171818338729915284999855)
    ·
      refine ⟨132257727508094872927499783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88171818338729915284999855 132257727508094872927499783)
      ·
        refine ⟨198386591262142309391249675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132257727508094872927499783 198386591262142309391249675)
        ·
          refine ⟨297579886893213464086874513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198386591262142309391249675 297579886893213464086874513)
          ·
            refine ⟨223184915169910098065155885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297579886893213464086874513 223184915169910098065155885)
            ·
              refine ⟨83694343188716286774433457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223184915169910098065155885 83694343188716286774433457)
              ·
                refine ⟨62770757391537215080825093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83694343188716286774433457 62770757391537215080825093)
                ·
                  refine ⟨11769517010913227827654705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62770757391537215080825093 11769517010913227827654705)
                  ·
                    refine ⟨8827137758184920870741029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11769517010913227827654705 8827137758184920870741029)
                    ·
                      refine ⟨1655088329659672663263943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8827137758184920870741029 1655088329659672663263943)
                      ·
                        rfl

theorem cell23_3223273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_3223273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223273 prefixEnd_3223273 := by exact prefixLift 3223273
  have htrace : WordTrace (prefixWord ++ tailWord_3223273) baseStart_3223273 baseEnd_3223273 := by
    simpa [prefixWord, tailWord_3223273, baseEnd_3223273] using wordTrace_append hprefix tailTrace_3223273
  have hstable : (prefixWord ++ tailWord_3223273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223273).length < 2 ^ (prefixWord ++ tailWord_3223273).sum := by decide
  have hdescent : baseEnd_3223273 < baseStart_3223273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223277 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_3223277 : Nat := 118140960795 + 3223277 * 2 ^ 59
def prefixEnd_3223277 : Nat := 4983230072969 + 3 ^ 40 * 3223277 * 2
def baseEnd_3223277 : Nat := 1655090383582290647613925

theorem tailTrace_3223277 : CollatzResearch.WordTrace tailWord_3223277 prefixEnd_3223277 1655090383582290647613925 := by
  unfold tailWord_3223277
  simp only [CollatzResearch.WordTrace]
  refine ⟨117562570343625395729812085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78375046895750263819874723 117562570343625395729812085)
  ·
    refine ⟨11021490969714880849669883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117562570343625395729812085 11021490969714880849669883)
    ·
      refine ⟨16532236454572321274504825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11021490969714880849669883 16532236454572321274504825)
      ·
        refine ⟨12399177340929240955878619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16532236454572321274504825 12399177340929240955878619)
        ·
          refine ⟨18598766011393861433817929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12399177340929240955878619 18598766011393861433817929)
          ·
            refine ⟨13949074508545396075363447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18598766011393861433817929 13949074508545396075363447)
            ·
              refine ⟨20923611762818094113045171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13949074508545396075363447 20923611762818094113045171)
              ·
                refine ⟨31385417644227141169567757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20923611762818094113045171 31385417644227141169567757)
                ·
                  refine ⟨11769531616585177938587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31385417644227141169567757 11769531616585177938587909)
                  ·
                    refine ⟨2206787178109720863485233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11769531616585177938587909 2206787178109720863485233)
                    ·
                      refine ⟨1655090383582290647613925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206787178109720863485233 1655090383582290647613925)
                      ·
                        rfl

theorem cell23_3223277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_3223277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223277 prefixEnd_3223277 := by exact prefixLift 3223277
  have htrace : WordTrace (prefixWord ++ tailWord_3223277) baseStart_3223277 baseEnd_3223277 := by
    simpa [prefixWord, tailWord_3223277, baseEnd_3223277] using wordTrace_append hprefix tailTrace_3223277
  have hstable : (prefixWord ++ tailWord_3223277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223277).length < 2 ^ (prefixWord ++ tailWord_3223277).sum := by decide
  have hdescent : baseEnd_3223277 < baseStart_3223277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223310 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3223310 : Nat := 118140960795 + 3223310 * 2 ^ 59
def prefixEnd_3223310 : Nat := 4983230072969 + 3 ^ 40 * 3223310 * 2
def baseEnd_3223310 : Nat := 1655107328443889018501273

theorem tailTrace_3223310 : CollatzResearch.WordTrace tailWord_3223310 prefixEnd_3223310 1655107328443889018501273 := by
  unfold tailWord_3223310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695471744063230295720423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78375849301670561577175589 14695471744063230295720423)
  ·
    refine ⟨22043207616094845443580635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14695471744063230295720423 22043207616094845443580635)
    ·
      refine ⟨33064811424142268165370953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22043207616094845443580635 33064811424142268165370953)
      ·
        refine ⟨24798608568106701124028215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33064811424142268165370953 24798608568106701124028215)
        ·
          refine ⟨37197912852160051686042323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24798608568106701124028215 37197912852160051686042323)
          ·
            refine ⟨55796869278240077529063485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37197912852160051686042323 55796869278240077529063485)
            ·
              refine ⟨20923825979340029073398807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55796869278240077529063485 20923825979340029073398807)
              ·
                refine ⟨31385738969010043610098211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20923825979340029073398807 31385738969010043610098211)
                ·
                  refine ⟨47078608453515065415147317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31385738969010043610098211 47078608453515065415147317)
                  ·
                    refine ⟨4413619542517037382670061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47078608453515065415147317 4413619542517037382670061)
                    ·
                      refine ⟨1655107328443889018501273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4413619542517037382670061 1655107328443889018501273)
                      ·
                        rfl

theorem cell23_3223310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3223310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223310 prefixEnd_3223310 := by exact prefixLift 3223310
  have htrace : WordTrace (prefixWord ++ tailWord_3223310) baseStart_3223310 baseEnd_3223310 := by
    simpa [prefixWord, tailWord_3223310, baseEnd_3223310] using wordTrace_append hprefix tailTrace_3223310
  have hstable : (prefixWord ++ tailWord_3223310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223310).length < 2 ^ (prefixWord ++ tailWord_3223310).sum := by decide
  have hdescent : baseEnd_3223310 < baseStart_3223310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223313 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_3223313 : Nat := 118140960795 + 3223313 * 2 ^ 59
def prefixEnd_3223313 : Nat := 4983230072969 + 3 ^ 40 * 3223313 * 2
def baseEnd_3223313 : Nat := 551702956295284168921253

theorem tailTrace_3223313 : CollatzResearch.WordTrace tailWord_3223313 prefixEnd_3223313 551702956295284168921253 := by
  unfold tailWord_3223313
  simp only [CollatzResearch.WordTrace]
  refine ⟨117563883371494973878122593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78375922247663315918748395 117563883371494973878122593)
  ·
    refine ⟨88172912528621230408591945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117563883371494973878122593 88172912528621230408591945)
    ·
      refine ⟨66129684396465922806443959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88172912528621230408591945 66129684396465922806443959)
      ·
        refine ⟨99194526594698884209665939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66129684396465922806443959 99194526594698884209665939)
        ·
          refine ⟨148791789892048326314498909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99194526594698884209665939 148791789892048326314498909)
          ·
            refine ⟨55796921209518122367937091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148791789892048326314498909 55796921209518122367937091)
            ·
              refine ⟨83695381814277183551905637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55796921209518122367937091 83695381814277183551905637)
              ·
                refine ⟨15692884090176971915982307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83695381814277183551905637 15692884090176971915982307)
                ·
                  refine ⟨23539326135265457873973461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15692884090176971915982307 23539326135265457873973461)
                  ·
                    refine ⟨551702956295284168921253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23539326135265457873973461 551702956295284168921253)
                    ·
                      rfl

theorem cell23_3223313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_3223313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223313 prefixEnd_3223313 := by exact prefixLift 3223313
  have htrace : WordTrace (prefixWord ++ tailWord_3223313) baseStart_3223313 baseEnd_3223313 := by
    simpa [prefixWord, tailWord_3223313, baseEnd_3223313] using wordTrace_append hprefix tailTrace_3223313
  have hstable : (prefixWord ++ tailWord_3223313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223313).length < 2 ^ (prefixWord ++ tailWord_3223313).sum := by decide
  have hdescent : baseEnd_3223313 < baseStart_3223313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223330 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3223330 : Nat := 118140960795 + 3223330 * 2 ^ 59
def prefixEnd_3223330 : Nat := 4983230072969 + 3 ^ 40 * 3223330 * 2
def baseEnd_3223330 : Nat := 551705866018992980083727

theorem tailTrace_3223330 : CollatzResearch.WordTrace tailWord_3223330 prefixEnd_3223330 551705866018992980083727 := by
  unfold tailWord_3223330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29391125853108346445372861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78376335608288923854327629 29391125853108346445372861)
  ·
    refine ⟨11021672194915629917014823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29391125853108346445372861 11021672194915629917014823)
    ·
      refine ⟨16532508292373444875522235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11021672194915629917014823 16532508292373444875522235)
      ·
        refine ⟨24798762438560167313283353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16532508292373444875522235 24798762438560167313283353)
        ·
          refine ⟨18599071828920125484962515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24798762438560167313283353 18599071828920125484962515)
          ·
            refine ⟨27898607743380188227443773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18599071828920125484962515 27898607743380188227443773)
            ·
              refine ⟨10461977903767570585291415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27898607743380188227443773 10461977903767570585291415)
              ·
                refine ⟨15692966855651355877937123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10461977903767570585291415 15692966855651355877937123)
                ·
                  refine ⟨23539450283477033816905685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15692966855651355877937123 23539450283477033816905685)
                  ·
                    refine ⟨551705866018992980083727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23539450283477033816905685 551705866018992980083727)
                    ·
                      rfl

theorem cell23_3223330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3223330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223330 prefixEnd_3223330 := by exact prefixLift 3223330
  have htrace : WordTrace (prefixWord ++ tailWord_3223330) baseStart_3223330 baseEnd_3223330 := by
    simpa [prefixWord, tailWord_3223330, baseEnd_3223330] using wordTrace_append hprefix tailTrace_3223330
  have hstable : (prefixWord ++ tailWord_3223330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223330).length < 2 ^ (prefixWord ++ tailWord_3223330).sum := by decide
  have hdescent : baseEnd_3223330 < baseStart_3223330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223367 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_3223367 : Nat := 118140960795 + 3223367 * 2 ^ 59
def prefixEnd_3223367 : Nat := 4983230072969 + 3 ^ 40 * 3223367 * 2
def baseEnd_3223367 : Nat := 1655136596841195295488511

theorem tailTrace_3223367 : CollatzResearch.WordTrace tailWord_3223367 prefixEnd_3223367 1655136596841195295488511 := by
  unfold tailWord_3223367
  simp only [CollatzResearch.WordTrace]
  refine ⟨117565852913299341100588355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78377235275532894067058903 117565852913299341100588355)
  ·
    refine ⟨176348779369949011650882533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117565852913299341100588355 176348779369949011650882533)
    ·
      refine ⟨33065396131865439684540475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176348779369949011650882533 33065396131865439684540475)
      ·
        refine ⟨49598094197798159526810713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33065396131865439684540475 49598094197798159526810713)
        ·
          refine ⟨37198570648348619645108035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49598094197798159526810713 37198570648348619645108035)
          ·
            refine ⟨55797855972522929467662053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37198570648348619645108035 55797855972522929467662053)
            ·
              refine ⟨10462097994848049275186635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55797855972522929467662053 10462097994848049275186635)
              ·
                refine ⟨15693146992272073912779953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462097994848049275186635 15693146992272073912779953)
                ·
                  refine ⟨11769860244204055434584965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15693146992272073912779953 11769860244204055434584965)
                  ·
                    refine ⟨2206848795788260393984681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11769860244204055434584965 2206848795788260393984681)
                    ·
                      refine ⟨1655136596841195295488511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206848795788260393984681 1655136596841195295488511)
                      ·
                        rfl

theorem cell23_3223367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_3223367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223367 prefixEnd_3223367 := by exact prefixLift 3223367
  have htrace : WordTrace (prefixWord ++ tailWord_3223367) baseStart_3223367 baseEnd_3223367 := by
    simpa [prefixWord, tailWord_3223367, baseEnd_3223367] using wordTrace_append hprefix tailTrace_3223367
  have hstable : (prefixWord ++ tailWord_3223367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223367).length < 2 ^ (prefixWord ++ tailWord_3223367).sum := by decide
  have hdescent : baseEnd_3223367 < baseStart_3223367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223370 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_3223370 : Nat := 118140960795 + 3223370 * 2 ^ 59
def prefixEnd_3223370 : Nat := 4983230072969 + 3 ^ 40 * 3223370 * 2
def baseEnd_3223370 : Nat := 1655138137283158783750997

theorem tailTrace_3223370 : CollatzResearch.WordTrace tailWord_3223370 prefixEnd_3223370 1655138137283158783750997 := by
  unfold tailWord_3223370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29391490583072118153236891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78377308221525648408631709 29391490583072118153236891)
  ·
    refine ⟨44087235874608177229855337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29391490583072118153236891 44087235874608177229855337)
    ·
      refine ⟨33065426905956132922391503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44087235874608177229855337 33065426905956132922391503)
      ·
        refine ⟨49598140358934199383587255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33065426905956132922391503 49598140358934199383587255)
        ·
          refine ⟨74397210538401299075380883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49598140358934199383587255 74397210538401299075380883)
          ·
            refine ⟨111595815807601948613071325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74397210538401299075380883 111595815807601948613071325)
            ·
              refine ⟨41848430927850730729901747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111595815807601948613071325 41848430927850730729901747)
              ·
                refine ⟨62772646391776096094852621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41848430927850730729901747 62772646391776096094852621)
                ·
                  refine ⟨23539742396916036035569733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62772646391776096094852621 23539742396916036035569733)
                  ·
                    refine ⟨4413701699421756756669325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23539742396916036035569733 4413701699421756756669325)
                    ·
                      refine ⟨1655138137283158783750997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4413701699421756756669325 1655138137283158783750997)
                      ·
                        rfl

theorem cell23_3223370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_3223370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223370 prefixEnd_3223370 := by exact prefixLift 3223370
  have htrace : WordTrace (prefixWord ++ tailWord_3223370) baseStart_3223370 baseEnd_3223370 := by
    simpa [prefixWord, tailWord_3223370, baseEnd_3223370] using wordTrace_append hprefix tailTrace_3223370
  have hstable : (prefixWord ++ tailWord_3223370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223370).length < 2 ^ (prefixWord ++ tailWord_3223370).sum := by decide
  have hdescent : baseEnd_3223370 < baseStart_3223370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223377 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_3223377 : Nat := 118140960795 + 3223377 * 2 ^ 59
def prefixEnd_3223377 : Nat := 4983230072969 + 3 ^ 40 * 3223377 * 2
def baseEnd_3223377 : Nat := 551713910549246752121155

theorem tailTrace_3223377 : CollatzResearch.WordTrace tailWord_3223377 prefixEnd_3223377 551713910549246752121155 := by
  unfold tailWord_3223377
  simp only [CollatzResearch.WordTrace]
  refine ⟨117566217643263112808452385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78377478428842075205634923 117566217643263112808452385)
  ·
    refine ⟨88174663232447334606339289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117566217643263112808452385 88174663232447334606339289)
    ·
      refine ⟨66130997424335500954754467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88174663232447334606339289 66130997424335500954754467)
      ·
        refine ⟨99196496136503251432131701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66130997424335500954754467 99196496136503251432131701)
        ·
          refine ⟨9299671512797179821762347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99196496136503251432131701 9299671512797179821762347)
          ·
            refine ⟨13949507269195769732643521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9299671512797179821762347 13949507269195769732643521)
            ·
              refine ⟨10462130451896827299482641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13949507269195769732643521 10462130451896827299482641)
              ·
                refine ⟨7846597838922620474611981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10462130451896827299482641 7846597838922620474611981)
                ·
                  refine ⟨2942474189595982677979493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7846597838922620474611981 2942474189595982677979493)
                  ·
                    refine ⟨551713910549246752121155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2942474189595982677979493 551713910549246752121155)
                    ·
                      rfl

theorem cell23_3223377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_3223377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223377 prefixEnd_3223377 := by exact prefixLift 3223377
  have htrace : WordTrace (prefixWord ++ tailWord_3223377) baseStart_3223377 baseEnd_3223377 := by
    simpa [prefixWord, tailWord_3223377, baseEnd_3223377] using wordTrace_append hprefix tailTrace_3223377
  have hstable : (prefixWord ++ tailWord_3223377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223377).length < 2 ^ (prefixWord ++ tailWord_3223377).sum := by decide
  have hdescent : baseEnd_3223377 < baseStart_3223377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223474 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_3223474 : Nat := 118140960795 + 3223474 * 2 ^ 59
def prefixEnd_3223474 : Nat := 4983230072969 + 3 ^ 40 * 3223474 * 2
def baseEnd_3223474 : Nat := 1655191539271226376850519

theorem tailTrace_3223474 : CollatzResearch.WordTrace tailWord_3223474 prefixEnd_3223474 1655191539271226376850519 := by
  unfold tailWord_3223474
  simp only [CollatzResearch.WordTrace]
  refine ⟨29392438880977924593683369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78379837015941132249822317 29392438880977924593683369)
  ·
    refine ⟨22044329160733443445262527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29392438880977924593683369 22044329160733443445262527)
    ·
      refine ⟨33066493741100165167893791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22044329160733443445262527 33066493741100165167893791)
      ·
        refine ⟨49599740611650247751840687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33066493741100165167893791 49599740611650247751840687)
        ·
          refine ⟨74399610917475371627761031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49599740611650247751840687 74399610917475371627761031)
          ·
            refine ⟨111599416376213057441641547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74399610917475371627761031 111599416376213057441641547)
            ·
              refine ⟨167399124564319586162462321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111599416376213057441641547 167399124564319586162462321)
              ·
                refine ⟨125549343423239689621846741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167399124564319586162462321 125549343423239689621846741)
                ·
                  refine ⟨2942562736482180225512033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125549343423239689621846741 2942562736482180225512033)
                  ·
                    refine ⟨2206922052361635169134025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2942562736482180225512033 2206922052361635169134025)
                    ·
                      refine ⟨1655191539271226376850519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206922052361635169134025 1655191539271226376850519)
                      ·
                        rfl

theorem cell23_3223474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_3223474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223474 prefixEnd_3223474 := by exact prefixLift 3223474
  have htrace : WordTrace (prefixWord ++ tailWord_3223474) baseStart_3223474 baseEnd_3223474 := by
    simpa [prefixWord, tailWord_3223474, baseEnd_3223474] using wordTrace_append hprefix tailTrace_3223474
  have hstable : (prefixWord ++ tailWord_3223474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223474).length < 2 ^ (prefixWord ++ tailWord_3223474).sum := by decide
  have hdescent : baseEnd_3223474 < baseStart_3223474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223487 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_3223487 : Nat := 118140960795 + 3223487 * 2 ^ 59
def prefixEnd_3223487 : Nat := 4983230072969 + 3 ^ 40 * 3223487 * 2
def baseEnd_3223487 : Nat := 1655198214519734825987959

theorem tailTrace_3223487 : CollatzResearch.WordTrace tailWord_3223487 prefixEnd_3223487 1655198214519734825987959 := by
  unfold tailWord_3223487
  simp only [CollatzResearch.WordTrace]
  refine ⟨117570229672864601594956715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78380153115243067729971143 117570229672864601594956715)
  ·
    refine ⟨176355344509296902392435073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117570229672864601594956715 176355344509296902392435073)
    ·
      refine ⟨132266508381972676794326305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176355344509296902392435073 132266508381972676794326305)
      ·
        refine ⟨99199881286479507595744729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132266508381972676794326305 99199881286479507595744729)
        ·
          refine ⟨74399910964859630696808547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99199881286479507595744729 74399910964859630696808547)
          ·
            refine ⟨111599866447289446045212821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74399910964859630696808547 111599866447289446045212821)
            ·
              refine ⟨5231243739716692783369351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111599866447289446045212821 5231243739716692783369351)
              ·
                refine ⟨7846865609575039175054027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5231243739716692783369351 7846865609575039175054027)
                ·
                  refine ⟨11770298414362558762581041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7846865609575039175054027 11770298414362558762581041)
                  ·
                    refine ⟨8827723810771919071935781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11770298414362558762581041 8827723810771919071935781)
                    ·
                      refine ⟨1655198214519734825987959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8827723810771919071935781 1655198214519734825987959)
                      ·
                        rfl

theorem cell23_3223487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_3223487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223487 prefixEnd_3223487 := by exact prefixLift 3223487
  have htrace : WordTrace (prefixWord ++ tailWord_3223487) baseStart_3223487 baseEnd_3223487 := by
    simpa [prefixWord, tailWord_3223487, baseEnd_3223487] using wordTrace_append hprefix tailTrace_3223487
  have hstable : (prefixWord ++ tailWord_3223487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223487).length < 2 ^ (prefixWord ++ tailWord_3223487).sum := by decide
  have hdescent : baseEnd_3223487 < baseStart_3223487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223524 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_3223524 : Nat := 118140960795 + 3223524 * 2 ^ 59
def prefixEnd_3223524 : Nat := 4983230072969 + 3 ^ 40 * 3223524 * 2
def baseEnd_3223524 : Nat := 1655217213303951181225289

theorem tailTrace_3223524 : CollatzResearch.WordTrace tailWord_3223524 prefixEnd_3223524 1655217213303951181225289 := by
  unfold tailWord_3223524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58785789586865278457026813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78381052782487037942702417 58785789586865278457026813)
  ·
    refine ⟨22044671095074479421385055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58785789586865278457026813 22044671095074479421385055)
    ·
      refine ⟨33067006642611719132077583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22044671095074479421385055 33067006642611719132077583)
      ·
        refine ⟨49600509963917578698116375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33067006642611719132077583 49600509963917578698116375)
        ·
          refine ⟨74400764945876368047174563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49600509963917578698116375 74400764945876368047174563)
          ·
            refine ⟨111601147418814552070761845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74400764945876368047174563 111601147418814552070761845)
            ·
              refine ⟨10462607570513864256633923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111601147418814552070761845 10462607570513864256633923)
              ·
                refine ⟨15693911355770796384950885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462607570513864256633923 15693911355770796384950885)
                ·
                  refine ⟨2942608379207024322178291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15693911355770796384950885 2942608379207024322178291)
                  ·
                    refine ⟨4413912568810536483267437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2942608379207024322178291 4413912568810536483267437)
                    ·
                      refine ⟨1655217213303951181225289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4413912568810536483267437 1655217213303951181225289)
                      ·
                        rfl

theorem cell23_3223524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_3223524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223524 prefixEnd_3223524 := by exact prefixLift 3223524
  have htrace : WordTrace (prefixWord ++ tailWord_3223524) baseStart_3223524 baseEnd_3223524 := by
    simpa [prefixWord, tailWord_3223524, baseEnd_3223524] using wordTrace_append hprefix tailTrace_3223524
  have hstable : (prefixWord ++ tailWord_3223524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223524).length < 2 ^ (prefixWord ++ tailWord_3223524).sum := by decide
  have hdescent : baseEnd_3223524 < baseStart_3223524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223564 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_3223564 : Nat := 118140960795 + 3223564 * 2 ^ 59
def prefixEnd_3223564 : Nat := 4983230072969 + 3 ^ 40 * 3223564 * 2
def baseEnd_3223564 : Nat := 1655237752530131024725105

theorem tailTrace_3223564 : CollatzResearch.WordTrace tailWord_3223564 prefixEnd_3223564 1655237752530131024725105 := by
  unfold tailWord_3223564
  simp only [CollatzResearch.WordTrace]
  refine ⟨58786519046792821872754873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78382025395723762497006497 58786519046792821872754873)
  ·
    refine ⟨44089889285094616404566155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58786519046792821872754873 44089889285094616404566155)
    ·
      refine ⟨66134833927641924606849233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44089889285094616404566155 66134833927641924606849233)
      ·
        refine ⟨49601125445731443455136925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66134833927641924606849233 49601125445731443455136925)
        ·
          refine ⟨18600422042149291295676347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49601125445731443455136925 18600422042149291295676347)
          ·
            refine ⟨27900633063223936943514521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18600422042149291295676347 27900633063223936943514521)
            ·
              refine ⟨20925474797417952707635891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27900633063223936943514521 20925474797417952707635891)
              ·
                refine ⟨31388212196126929061453837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20925474797417952707635891 31388212196126929061453837)
                ·
                  refine ⟨11770579573547598398045189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31388212196126929061453837 11770579573547598398045189)
                  ·
                    refine ⟨2206983670040174699633473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11770579573547598398045189 2206983670040174699633473)
                    ·
                      refine ⟨1655237752530131024725105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2206983670040174699633473 1655237752530131024725105)
                      ·
                        rfl

theorem cell23_3223564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_3223564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223564 prefixEnd_3223564 := by exact prefixLift 3223564
  have htrace : WordTrace (prefixWord ++ tailWord_3223564) baseStart_3223564 baseEnd_3223564 := by
    simpa [prefixWord, tailWord_3223564, baseEnd_3223564] using wordTrace_append hprefix tailTrace_3223564
  have hstable : (prefixWord ++ tailWord_3223564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223564).length < 2 ^ (prefixWord ++ tailWord_3223564).sum := by decide
  have hdescent : baseEnd_3223564 < baseStart_3223564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223592 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3223592 : Nat := 118140960795 + 3223592 * 2 ^ 59
def prefixEnd_3223592 : Nat := 4983230072969 + 3 ^ 40 * 3223592 * 2
def baseEnd_3223592 : Nat := 1655252129988456915174977

theorem tailTrace_3223592 : CollatzResearch.WordTrace tailWord_3223592 prefixEnd_3223592 1655252129988456915174977 := by
  unfold tailWord_3223592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58787029668742102263764515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78382706224989469685019353 58787029668742102263764515)
  ·
    refine ⟨88180544503113153395646773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58787029668742102263764515 88180544503113153395646773)
    ·
      refine ⟨8266926047166858130841885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88180544503113153395646773 8266926047166858130841885)
      ·
        refine ⟨3100097267687571799065707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8266926047166858130841885 3100097267687571799065707)
        ·
          refine ⟨4650145901531357698598561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100097267687571799065707 4650145901531357698598561)
          ·
            refine ⟨3487609426148518273948921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650145901531357698598561 3487609426148518273948921)
            ·
              refine ⟨2615707069611388705461691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487609426148518273948921 2615707069611388705461691)
              ·
                refine ⟨3923560604417083058192537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615707069611388705461691 3923560604417083058192537)
                ·
                  refine ⟨2942670453312812293644403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3923560604417083058192537 2942670453312812293644403)
                  ·
                    refine ⟨4414005679969218440466605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2942670453312812293644403 4414005679969218440466605)
                    ·
                      refine ⟨1655252129988456915174977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414005679969218440466605 1655252129988456915174977)
                      ·
                        rfl

theorem cell23_3223592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3223592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223592 prefixEnd_3223592 := by exact prefixLift 3223592
  have htrace : WordTrace (prefixWord ++ tailWord_3223592) baseStart_3223592 baseEnd_3223592 := by
    simpa [prefixWord, tailWord_3223592, baseEnd_3223592] using wordTrace_append hprefix tailTrace_3223592
  have hstable : (prefixWord ++ tailWord_3223592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223592).length < 2 ^ (prefixWord ++ tailWord_3223592).sum := by decide
  have hdescent : baseEnd_3223592 < baseStart_3223592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223644 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3223644 : Nat := 118140960795 + 3223644 * 2 ^ 59
def prefixEnd_3223644 : Nat := 4983230072969 + 3 ^ 40 * 3223644 * 2
def baseEnd_3223644 : Nat := 1655278830982490711724737

theorem tailTrace_3223644 : CollatzResearch.WordTrace tailWord_3223644 prefixEnd_3223644 1655278830982490711724737 := by
  unfold tailWord_3223644
  simp only [CollatzResearch.WordTrace]
  refine ⟨58787977966647908704210993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78383970622197211605614657 58787977966647908704210993)
  ·
    refine ⟨44090983474985931528158245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58787977966647908704210993 44090983474985931528158245)
    ·
      refine ⟨8267059401559862161529671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44090983474985931528158245 8267059401559862161529671)
      ·
        refine ⟨12400589102339793242294507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267059401559862161529671 12400589102339793242294507)
        ·
          refine ⟨18600883653509689863441761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12400589102339793242294507 18600883653509689863441761)
          ·
            refine ⟨13950662740132267397581321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18600883653509689863441761 13950662740132267397581321)
            ·
              refine ⟨10462997055099200548185991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13950662740132267397581321 10462997055099200548185991)
              ·
                refine ⟨15694495582648800822278987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462997055099200548185991 15694495582648800822278987)
                ·
                  refine ⟨23541743373973201233418481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15694495582648800822278987 23541743373973201233418481)
                  ·
                    refine ⟨17656307530479900925063861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23541743373973201233418481 17656307530479900925063861)
                    ·
                      refine ⟨1655278830982490711724737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17656307530479900925063861 1655278830982490711724737)
                      ·
                        rfl

theorem cell23_3223644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3223644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223644 prefixEnd_3223644 := by exact prefixLift 3223644
  have htrace : WordTrace (prefixWord ++ tailWord_3223644) baseStart_3223644 baseEnd_3223644 := by
    simpa [prefixWord, tailWord_3223644, baseEnd_3223644] using wordTrace_append hprefix tailTrace_3223644
  have hstable : (prefixWord ++ tailWord_3223644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223644).length < 2 ^ (prefixWord ++ tailWord_3223644).sum := by decide
  have hdescent : baseEnd_3223644 < baseStart_3223644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223664 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_3223664 : Nat := 118140960795 + 3223664 * 2 ^ 59
def prefixEnd_3223664 : Nat := 4983230072969 + 3 ^ 40 * 3223664 * 2
def baseEnd_3223664 : Nat := 551763033531860211158215

theorem tailTrace_3223664 : CollatzResearch.WordTrace tailWord_3223664 prefixEnd_3223664 551763033531860211158215 := by
  unfold tailWord_3223664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58788342696611680412075023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78384456928815573882766697 58788342696611680412075023)
  ·
    refine ⟨88182514044917520618112535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58788342696611680412075023 88182514044917520618112535)
    ·
      refine ⟨132273771067376280927168803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88182514044917520618112535 132273771067376280927168803)
      ·
        refine ⟨198410656601064421390753205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132273771067376280927168803 198410656601064421390753205)
        ·
          refine ⟨18600999056349789505383113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198410656601064421390753205 18600999056349789505383113)
          ·
            refine ⟨13950749292262342129037335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18600999056349789505383113 13950749292262342129037335)
            ·
              refine ⟨20926123938393513193556003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13950749292262342129037335 20926123938393513193556003)
              ·
                refine ⟨31389185907590269790334005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20926123938393513193556003 31389185907590269790334005)
                ·
                  refine ⟨2942736178836587792843813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31389185907590269790334005 2942736178836587792843813)
                  ·
                    refine ⟨551763033531860211158215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2942736178836587792843813 551763033531860211158215)
                    ·
                      rfl

theorem cell23_3223664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_3223664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223664 prefixEnd_3223664 := by exact prefixLift 3223664
  have htrace : WordTrace (prefixWord ++ tailWord_3223664) baseStart_3223664 baseEnd_3223664 := by
    simpa [prefixWord, tailWord_3223664, baseEnd_3223664] using wordTrace_append hprefix tailTrace_3223664
  have hstable : (prefixWord ++ tailWord_3223664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223664).length < 2 ^ (prefixWord ++ tailWord_3223664).sum := by decide
  have hdescent : baseEnd_3223664 < baseStart_3223664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223671 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_3223671 : Nat := 118140960795 + 3223671 * 2 ^ 59
def prefixEnd_3223671 : Nat := 4983230072969 + 3 ^ 40 * 3223671 * 2
def baseEnd_3223671 : Nat := 1655292694960162106087113

theorem tailTrace_3223671 : CollatzResearch.WordTrace tailWord_3223671 prefixEnd_3223671 1655292694960162106087113 := by
  unfold tailWord_3223671
  simp only [CollatzResearch.WordTrace]
  refine ⟨117576940704198001019654867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78384627136132000679769911 117576940704198001019654867)
  ·
    refine ⟨176365411056297001529482301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117576940704198001019654867 176365411056297001529482301)
    ·
      refine ⟨66137029146111375573555863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176365411056297001529482301 66137029146111375573555863)
      ·
        refine ⟨99205543719167063360333795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66137029146111375573555863 99205543719167063360333795)
        ·
          refine ⟨148808315578750595040500693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99205543719167063360333795 148808315578750595040500693)
          ·
            refine ⟨3487694896376967071261735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 148808315578750595040500693 3487694896376967071261735)
            ·
              refine ⟨5231542344565450606892603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487694896376967071261735 5231542344565450606892603)
              ·
                refine ⟨7847313516848175910338905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5231542344565450606892603 7847313516848175910338905)
                ·
                  refine ⟨5885485137636131932754179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7847313516848175910338905 5885485137636131932754179)
                  ·
                    refine ⟨8828227706454197899131269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885485137636131932754179 8828227706454197899131269)
                    ·
                      refine ⟨1655292694960162106087113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8828227706454197899131269 1655292694960162106087113)
                      ·
                        rfl

theorem cell23_3223671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_3223671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223671 prefixEnd_3223671 := by exact prefixLift 3223671
  have htrace : WordTrace (prefixWord ++ tailWord_3223671) baseStart_3223671 baseEnd_3223671 := by
    simpa [prefixWord, tailWord_3223671, baseEnd_3223671] using wordTrace_append hprefix tailTrace_3223671
  have hstable : (prefixWord ++ tailWord_3223671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223671).length < 2 ^ (prefixWord ++ tailWord_3223671).sum := by decide
  have hdescent : baseEnd_3223671 < baseStart_3223671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223698 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3223698 : Nat := 118140960795 + 3223698 * 2 ^ 59
def prefixEnd_3223698 : Nat := 4983230072969 + 3 ^ 40 * 3223698 * 2
def baseEnd_3223698 : Nat := 551768852979277833483163

theorem tailTrace_3223698 : CollatzResearch.WordTrace tailWord_3223698 prefixEnd_3223698 551768852979277833483163 := by
  unfold tailWord_3223698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29394481368775046157721937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78385283650066789753925165 29394481368775046157721937)
  ·
    refine ⟨22045861026581284618291453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29394481368775046157721937 22045861026581284618291453)
    ·
      refine ⟨8267197884967981731859295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22045861026581284618291453 8267197884967981731859295)
      ·
        refine ⟨12400796827451972597788943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267197884967981731859295 12400796827451972597788943)
        ·
          refine ⟨18601195241177958896683415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12400796827451972597788943 18601195241177958896683415)
          ·
            refine ⟨27901792861766938345025123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18601195241177958896683415 27901792861766938345025123)
            ·
              refine ⟨41852689292650407517537685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27901792861766938345025123 41852689292650407517537685)
              ·
                refine ⟨1961844810592987852384579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41852689292650407517537685 1961844810592987852384579)
                ·
                  refine ⟨2942767215889481778576869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961844810592987852384579 2942767215889481778576869)
                  ·
                    refine ⟨551768852979277833483163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2942767215889481778576869 551768852979277833483163)
                    ·
                      rfl

theorem cell23_3223698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3223698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223698 prefixEnd_3223698 := by exact prefixLift 3223698
  have htrace : WordTrace (prefixWord ++ tailWord_3223698) baseStart_3223698 baseEnd_3223698 := by
    simpa [prefixWord, tailWord_3223698, baseEnd_3223698] using wordTrace_append hprefix tailTrace_3223698
  have hstable : (prefixWord ++ tailWord_3223698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223698).length < 2 ^ (prefixWord ++ tailWord_3223698).sum := by decide
  have hdescent : baseEnd_3223698 < baseStart_3223698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223731 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 2, 3, 2]
def baseStart_3223731 : Nat := 118140960795 + 3223731 * 2 ^ 59
def prefixEnd_3223731 : Nat := 4983230072969 + 3 ^ 40 * 3223731 * 2
def baseEnd_3223731 : Nat := 1655323503799431871336837

theorem tailTrace_3223731 : CollatzResearch.WordTrace tailWord_3223731 prefixEnd_3223731 1655323503799431871336837 := by
  unfold tailWord_3223731
  simp only [CollatzResearch.WordTrace]
  refine ⟨117579129083980631266839047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78386086055987087511226031 117579129083980631266839047)
  ·
    refine ⟨176368693625970946900258571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117579129083980631266839047 176368693625970946900258571)
    ·
      refine ⟨264553040438956420350387857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176368693625970946900258571 264553040438956420350387857)
      ·
        refine ⟨198414780329217315262790893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264553040438956420350387857 198414780329217315262790893)
        ·
          refine ⟨74405542623456493223546585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198414780329217315262790893 74405542623456493223546585)
          ·
            refine ⟨55804156967592369917659939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74405542623456493223546585 55804156967592369917659939)
            ·
              refine ⟨83706235451388554876489909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55804156967592369917659939 83706235451388554876489909)
              ·
                refine ⟨7847459573567677019670929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83706235451388554876489909 7847459573567677019670929)
                ·
                  refine ⟨5885594680175757764753197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7847459573567677019670929 5885594680175757764753197)
                  ·
                    refine ⟨2207098005065909161782449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5885594680175757764753197 2207098005065909161782449)
                    ·
                      refine ⟨1655323503799431871336837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207098005065909161782449 1655323503799431871336837)
                      ·
                        rfl

theorem cell23_3223731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3, 2].length) (baseStart_3223731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223731 prefixEnd_3223731 := by exact prefixLift 3223731
  have htrace : WordTrace (prefixWord ++ tailWord_3223731) baseStart_3223731 baseEnd_3223731 := by
    simpa [prefixWord, tailWord_3223731, baseEnd_3223731] using wordTrace_append hprefix tailTrace_3223731
  have hstable : (prefixWord ++ tailWord_3223731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223731).length < 2 ^ (prefixWord ++ tailWord_3223731).sum := by decide
  have hdescent : baseEnd_3223731 < baseStart_3223731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223748 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_3223748 : Nat := 118140960795 + 3223748 * 2 ^ 59
def prefixEnd_3223748 : Nat := 4983230072969 + 3 ^ 40 * 3223748 * 2
def baseEnd_3223748 : Nat := 1655332232970558304824259

theorem tailTrace_3223748 : CollatzResearch.WordTrace tailWord_3223748 prefixEnd_3223748 1655332232970558304824259 := by
  unfold tailWord_3223748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58789874562459521585103949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78386499416612695446805265 58789874562459521585103949)
  ·
    refine ⟨22046202960922320594413981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58789874562459521585103949 22046202960922320594413981)
    ·
      refine ⟨8267326110345870222905243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22046202960922320594413981 8267326110345870222905243)
      ·
        refine ⟨12400989165518805334357865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267326110345870222905243 12400989165518805334357865)
        ·
          refine ⟨9300741874139104000768399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12400989165518805334357865 9300741874139104000768399)
          ·
            refine ⟨13951112811208656001152599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9300741874139104000768399 13951112811208656001152599)
            ·
              refine ⟨20926669216812984001728899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13951112811208656001152599 20926669216812984001728899)
              ·
                refine ⟨31390003825219476002593349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20926669216812984001728899 31390003825219476002593349)
                ·
                  refine ⟨5885625717228651750486253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31390003825219476002593349 5885625717228651750486253)
                  ·
                    refine ⟨2207109643960744406432345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5885625717228651750486253 2207109643960744406432345)
                    ·
                      refine ⟨1655332232970558304824259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207109643960744406432345 1655332232970558304824259)
                      ·
                        rfl

theorem cell23_3223748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_3223748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223748 prefixEnd_3223748 := by exact prefixLift 3223748
  have htrace : WordTrace (prefixWord ++ tailWord_3223748) baseStart_3223748 baseEnd_3223748 := by
    simpa [prefixWord, tailWord_3223748, baseEnd_3223748] using wordTrace_append hprefix tailTrace_3223748
  have hstable : (prefixWord ++ tailWord_3223748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223748).length < 2 ^ (prefixWord ++ tailWord_3223748).sum := by decide
  have hdescent : baseEnd_3223748 < baseStart_3223748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223755 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 1, 1, 3]
def baseStart_3223755 : Nat := 118140960795 + 3223755 * 2 ^ 59
def prefixEnd_3223755 : Nat := 4983230072969 + 3 ^ 40 * 3223755 * 2
def baseEnd_3223755 : Nat := 1655335827335139777436727

theorem tailTrace_3223755 : CollatzResearch.WordTrace tailWord_3223755 prefixEnd_3223755 1655335827335139777436727 := by
  unfold tailWord_3223755
  simp only [CollatzResearch.WordTrace]
  refine ⟨117580004435893683365712719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78386669623929122243808479 117580004435893683365712719)
  ·
    refine ⟨176370006653840525048569079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117580004435893683365712719 176370006653840525048569079)
    ·
      refine ⟨264555009980760787572853619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176370006653840525048569079 264555009980760787572853619)
      ·
        refine ⟨396832514971141181359280429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264555009980760787572853619 396832514971141181359280429)
        ·
          refine ⟨148812193114177943009730161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396832514971141181359280429 148812193114177943009730161)
          ·
            refine ⟨111609144835633457257297621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148812193114177943009730161 111609144835633457257297621)
            ·
              refine ⟨2615839332085159154467913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111609144835633457257297621 2615839332085159154467913)
              ·
                refine ⟨1961879499063869365850935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2615839332085159154467913 1961879499063869365850935)
                ·
                  refine ⟨2942819248595804048776403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961879499063869365850935 2942819248595804048776403)
                  ·
                    refine ⟨4414228872893706073164605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2942819248595804048776403 4414228872893706073164605)
                    ·
                      refine ⟨1655335827335139777436727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414228872893706073164605 1655335827335139777436727)
                      ·
                        rfl

theorem cell23_3223755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 1, 3].length) (baseStart_3223755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223755 prefixEnd_3223755 := by exact prefixLift 3223755
  have htrace : WordTrace (prefixWord ++ tailWord_3223755) baseStart_3223755 baseEnd_3223755 := by
    simpa [prefixWord, tailWord_3223755, baseEnd_3223755] using wordTrace_append hprefix tailTrace_3223755
  have hstable : (prefixWord ++ tailWord_3223755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223755).length < 2 ^ (prefixWord ++ tailWord_3223755).sum := by decide
  have hdescent : baseEnd_3223755 < baseStart_3223755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223784 : List Nat := [2, 1, 4, 1, 2, 2, 2, 9]
def baseStart_3223784 : Nat := 118140960795 + 3223784 * 2 ^ 59
def prefixEnd_3223784 : Nat := 4983230072969 + 3 ^ 40 * 3223784 * 2
def baseEnd_3223784 : Nat := 61309285862004450517559

theorem tailTrace_3223784 : CollatzResearch.WordTrace tailWord_3223784 prefixEnd_3223784 61309285862004450517559 := by
  unfold tailWord_3223784
  simp only [CollatzResearch.WordTrace]
  refine ⟨58790531076394310659259203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78387374768525747545678937 58790531076394310659259203)
  ·
    refine ⟨88185796614591465988888805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58790531076394310659259203 88185796614591465988888805)
    ·
      refine ⟨16534836865235899872916651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88185796614591465988888805 16534836865235899872916651)
      ·
        refine ⟨24802255297853849809374977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534836865235899872916651 24802255297853849809374977)
        ·
          refine ⟨18601691473390387357031233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24802255297853849809374977 18601691473390387357031233)
          ·
            refine ⟨13951268605042790517773425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18601691473390387357031233 13951268605042790517773425)
            ·
              refine ⟨10463451453782092888330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13951268605042790517773425 10463451453782092888330069)
              ·
                refine ⟨61309285862004450517559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10463451453782092888330069 61309285862004450517559)
                ·
                  rfl

theorem cell23_3223784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 9].length) (baseStart_3223784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223784 prefixEnd_3223784 := by exact prefixLift 3223784
  have htrace : WordTrace (prefixWord ++ tailWord_3223784) baseStart_3223784 baseEnd_3223784 := by
    simpa [prefixWord, tailWord_3223784, baseEnd_3223784] using wordTrace_append hprefix tailTrace_3223784
  have hstable : (prefixWord ++ tailWord_3223784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223784).length < 2 ^ (prefixWord ++ tailWord_3223784).sum := by decide
  have hdescent : baseEnd_3223784 < baseStart_3223784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223791 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_3223791 : Nat := 118140960795 + 3223791 * 2 ^ 59
def prefixEnd_3223791 : Nat := 4983230072969 + 3 ^ 40 * 3223791 * 2
def baseEnd_3223791 : Nat := 1655354312638701636586561

theorem tailTrace_3223791 : CollatzResearch.WordTrace tailWord_3223791 prefixEnd_3223791 1655354312638701636586561 := by
  unfold tailWord_3223791
  simp only [CollatzResearch.WordTrace]
  refine ⟨117581317463763261514023227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78387544975842174342682151 117581317463763261514023227)
  ·
    refine ⟨176371976195644892271034841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117581317463763261514023227 176371976195644892271034841)
    ·
      refine ⟨132278982146733669203276131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176371976195644892271034841 132278982146733669203276131)
      ·
        refine ⟨198418473220100503804914197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132278982146733669203276131 198418473220100503804914197)
        ·
          refine ⟨9300865932192211115855353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198418473220100503804914197 9300865932192211115855353)
          ·
            refine ⟨6975649449144158336891515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9300865932192211115855353 6975649449144158336891515)
            ·
              refine ⟨10463474173716237505337273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975649449144158336891515 10463474173716237505337273)
              ·
                refine ⟨7847605630287178129002955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10463474173716237505337273 7847605630287178129002955)
                ·
                  refine ⟨11771408445430767193504433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7847605630287178129002955 11771408445430767193504433)
                  ·
                    refine ⟨8828556334073075395128325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11771408445430767193504433 8828556334073075395128325)
                    ·
                      refine ⟨1655354312638701636586561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8828556334073075395128325 1655354312638701636586561)
                      ·
                        rfl

theorem cell23_3223791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_3223791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223791 prefixEnd_3223791 := by exact prefixLift 3223791
  have htrace : WordTrace (prefixWord ++ tailWord_3223791) baseStart_3223791 baseEnd_3223791 := by
    simpa [prefixWord, tailWord_3223791, baseEnd_3223791] using wordTrace_append hprefix tailTrace_3223791
  have hstable : (prefixWord ++ tailWord_3223791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223791).length < 2 ^ (prefixWord ++ tailWord_3223791).sum := by decide
  have hdescent : baseEnd_3223791 < baseStart_3223791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223795 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 1, 2, 2]
def baseStart_3223795 : Nat := 118140960795 + 3223795 * 2 ^ 59
def prefixEnd_3223795 : Nat := 4983230072969 + 3 ^ 40 * 3223795 * 2
def baseEnd_3223795 : Nat := 1655356366561319620936543

theorem tailTrace_3223795 : CollatzResearch.WordTrace tailWord_3223795 prefixEnd_3223795 1655356366561319620936543 := by
  unfold tailWord_3223795
  simp only [CollatzResearch.WordTrace]
  refine ⟨117581463355748770197168839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78387642237165846798112559 117581463355748770197168839)
  ·
    refine ⟨176372195033623155295753259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117581463355748770197168839 176372195033623155295753259)
    ·
      refine ⟨264558292550434732943629889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176372195033623155295753259 264558292550434732943629889)
      ·
        refine ⟨198418719412826049707722417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264558292550434732943629889 198418719412826049707722417)
        ·
          refine ⟨148814039559619537280791813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198418719412826049707722417 148814039559619537280791813)
          ·
            refine ⟨27902632417428663240148465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148814039559619537280791813 27902632417428663240148465)
            ·
              refine ⟨20926974313071497430111349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27902632417428663240148465 20926974313071497430111349)
              ·
                refine ⟨1961903841850452884072939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20926974313071497430111349 1961903841850452884072939)
                ·
                  refine ⟨2942855762775679326109409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961903841850452884072939 2942855762775679326109409)
                  ·
                    refine ⟨2207141822081759494582057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2942855762775679326109409 2207141822081759494582057)
                    ·
                      refine ⟨1655356366561319620936543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207141822081759494582057 1655356366561319620936543)
                      ·
                        rfl

theorem cell23_3223795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 2, 2].length) (baseStart_3223795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223795 prefixEnd_3223795 := by exact prefixLift 3223795
  have htrace : WordTrace (prefixWord ++ tailWord_3223795) baseStart_3223795 baseEnd_3223795 := by
    simpa [prefixWord, tailWord_3223795, baseEnd_3223795] using wordTrace_append hprefix tailTrace_3223795
  have hstable : (prefixWord ++ tailWord_3223795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223795).length < 2 ^ (prefixWord ++ tailWord_3223795).sum := by decide
  have hdescent : baseEnd_3223795 < baseStart_3223795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223798 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3223798 : Nat := 118140960795 + 3223798 * 2 ^ 59
def prefixEnd_3223798 : Nat := 4983230072969 + 3 ^ 40 * 3223798 * 2
def baseEnd_3223798 : Nat := 1655357907003283109199029

theorem tailTrace_3223798 : CollatzResearch.WordTrace tailWord_3223798 prefixEnd_3223798 1655357907003283109199029 := by
  unfold tailWord_3223798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348848298421118856845503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78387715183158601139685365 7348848298421118856845503)
  ·
    refine ⟨11023272447631678285268255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348848298421118856845503 11023272447631678285268255)
    ·
      refine ⟨16534908671447517427902383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023272447631678285268255 16534908671447517427902383)
      ·
        refine ⟨24802363007171276141853575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534908671447517427902383 24802363007171276141853575)
        ·
          refine ⟨37203544510756914212780363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802363007171276141853575 37203544510756914212780363)
          ·
            refine ⟨55805316766135371319170545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37203544510756914212780363 55805316766135371319170545)
            ·
              refine ⟨41853987574601528489377909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55805316766135371319170545 41853987574601528489377909)
              ·
                refine ⟨3923811335118893295879179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41853987574601528489377909 3923811335118893295879179)
                ·
                  refine ⟨5885717002678339943818769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923811335118893295879179 5885717002678339943818769)
                  ·
                    refine ⟨4414287752008754957864077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5885717002678339943818769 4414287752008754957864077)
                    ·
                      refine ⟨1655357907003283109199029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414287752008754957864077 1655357907003283109199029)
                      ·
                        rfl

theorem cell23_3223798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3223798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223798 prefixEnd_3223798 := by exact prefixLift 3223798
  have htrace : WordTrace (prefixWord ++ tailWord_3223798) baseStart_3223798 baseEnd_3223798 := by
    simpa [prefixWord, tailWord_3223798, baseEnd_3223798] using wordTrace_append hprefix tailTrace_3223798
  have hstable : (prefixWord ++ tailWord_3223798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223798).length < 2 ^ (prefixWord ++ tailWord_3223798).sum := by decide
  have hdescent : baseEnd_3223798 < baseStart_3223798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223855 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 1, 3, 2]
def baseStart_3223855 : Nat := 118140960795 + 3223855 * 2 ^ 59
def prefixEnd_3223855 : Nat := 4983230072969 + 3 ^ 40 * 3223855 * 2
def baseEnd_3223855 : Nat := 1655387175400589386186267

theorem tailTrace_3223855 : CollatzResearch.WordTrace tailWord_3223855 prefixEnd_3223855 1655387175400589386186267 := by
  unfold tailWord_3223855
  simp only [CollatzResearch.WordTrace]
  refine ⟨117583651735531400444353019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78389101157020933629568679 117583651735531400444353019)
  ·
    refine ⟨176375477603297100666529529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117583651735531400444353019 176375477603297100666529529)
    ·
      refine ⟨132281608202472825499897147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176375477603297100666529529 132281608202472825499897147)
      ·
        refine ⟨198422412303709238249845721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132281608202472825499897147 198422412303709238249845721)
        ·
          refine ⟨148816809227781928687384291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198422412303709238249845721 148816809227781928687384291)
          ·
            refine ⟨223225213841672893031076437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148816809227781928687384291 223225213841672893031076437)
            ·
              refine ⟨2615920474707104215207927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 223225213841672893031076437 2615920474707104215207927)
              ·
                refine ⟨3923880712060656322811891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615920474707104215207927 3923880712060656322811891)
                ·
                  refine ⟨5885821068090984484217837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923880712060656322811891 5885821068090984484217837)
                  ·
                    refine ⟨2207182900534119181581689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5885821068090984484217837 2207182900534119181581689)
                    ·
                      refine ⟨1655387175400589386186267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207182900534119181581689 1655387175400589386186267)
                      ·
                        rfl

theorem cell23_3223855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 3, 2].length) (baseStart_3223855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223855 prefixEnd_3223855 := by exact prefixLift 3223855
  have htrace : WordTrace (prefixWord ++ tailWord_3223855) baseStart_3223855 baseEnd_3223855 := by
    simpa [prefixWord, tailWord_3223855, baseEnd_3223855] using wordTrace_append hprefix tailTrace_3223855
  have hstable : (prefixWord ++ tailWord_3223855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223855).length < 2 ^ (prefixWord ++ tailWord_3223855).sum := by decide
  have hdescent : baseEnd_3223855 < baseStart_3223855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223931 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5]
def baseStart_3223931 : Nat := 118140960795 + 3223931 * 2 ^ 59
def prefixEnd_3223931 : Nat := 4983230072969 + 3 ^ 40 * 3223931 * 2
def baseEnd_3223931 : Nat := 1655426199930331088835917

theorem tailTrace_3223931 : CollatzResearch.WordTrace tailWord_3223931 prefixEnd_3223931 1655426199930331088835917 := by
  unfold tailWord_3223931
  simp only [CollatzResearch.WordTrace]
  refine ⟨117586423683256065424119647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78390949122170710282746431 117586423683256065424119647)
  ·
    refine ⟨176379635524884098136179471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117586423683256065424119647 176379635524884098136179471)
    ·
      refine ⟨264569453287326147204269207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176379635524884098136179471 264569453287326147204269207)
      ·
        refine ⟨396854179930989220806403811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264569453287326147204269207 396854179930989220806403811)
        ·
          refine ⟨595281269896483831209605717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396854179930989220806403811 595281269896483831209605717)
          ·
            refine ⟨6975952381599419896987567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 595281269896483831209605717 6975952381599419896987567)
            ·
              refine ⟨10463928572399129845481351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6975952381599419896987567 10463928572399129845481351)
              ·
                refine ⟨15695892858598694768222027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10463928572399129845481351 15695892858598694768222027)
                ·
                  refine ⟨23543839287898042152333041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15695892858598694768222027 23543839287898042152333041)
                  ·
                    refine ⟨17657879465923531614249781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23543839287898042152333041 17657879465923531614249781)
                    ·
                      refine ⟨1655426199930331088835917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17657879465923531614249781 1655426199930331088835917)
                      ·
                        rfl

theorem cell23_3223931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_3223931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223931 prefixEnd_3223931 := by exact prefixLift 3223931
  have htrace : WordTrace (prefixWord ++ tailWord_3223931) baseStart_3223931 baseEnd_3223931 := by
    simpa [prefixWord, tailWord_3223931, baseEnd_3223931] using wordTrace_append hprefix tailTrace_3223931
  have hstable : (prefixWord ++ tailWord_3223931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223931).length < 2 ^ (prefixWord ++ tailWord_3223931).sum := by decide
  have hdescent : baseEnd_3223931 < baseStart_3223931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223941 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_3223941 : Nat := 118140960795 + 3223941 * 2 ^ 59
def prefixEnd_3223941 : Nat := 4983230072969 + 3 ^ 40 * 3223941 * 2
def baseEnd_3223941 : Nat := 1655431334736876049710871

theorem tailTrace_3223941 : CollatzResearch.WordTrace tailWord_3223941 prefixEnd_3223941 1655431334736876049710871 := by
  unfold tailWord_3223941
  simp only [CollatzResearch.WordTrace]
  refine ⟨117586788413219837131983677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78391192275479891421322451 117586788413219837131983677)
  ·
    refine ⟨44095045654957438924493879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117586788413219837131983677 44095045654957438924493879)
    ·
      refine ⟨66142568482436158386740819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44095045654957438924493879 66142568482436158386740819)
      ·
        refine ⟨99213852723654237580111229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66142568482436158386740819 99213852723654237580111229)
        ·
          refine ⟨37205194771370339092541711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99213852723654237580111229 37205194771370339092541711)
          ·
            refine ⟨55807792157055508638812567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37205194771370339092541711 55807792157055508638812567)
            ·
              refine ⟨83711688235583262958218851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55807792157055508638812567 83711688235583262958218851)
              ·
                refine ⟨125567532353374894437328277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83711688235583262958218851 125567532353374894437328277)
                ·
                  refine ⟨5885978079064448176749763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125567532353374894437328277 5885978079064448176749763)
                  ·
                    refine ⟨8828967118596672265124645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5885978079064448176749763 8828967118596672265124645)
                    ·
                      refine ⟨1655431334736876049710871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8828967118596672265124645 1655431334736876049710871)
                      ·
                        rfl

theorem cell23_3223941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_3223941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223941 prefixEnd_3223941 := by exact prefixLift 3223941
  have htrace : WordTrace (prefixWord ++ tailWord_3223941) baseStart_3223941 baseEnd_3223941 := by
    simpa [prefixWord, tailWord_3223941, baseEnd_3223941] using wordTrace_append hprefix tailTrace_3223941
  have hstable : (prefixWord ++ tailWord_3223941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223941).length < 2 ^ (prefixWord ++ tailWord_3223941).sum := by decide
  have hdescent : baseEnd_3223941 < baseStart_3223941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3223998 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_3223998 : Nat := 118140960795 + 3223998 * 2 ^ 59
def prefixEnd_3223998 : Nat := 4983230072969 + 3 ^ 40 * 3223998 * 2
def baseEnd_3223998 : Nat := 183940067014909147410901

theorem tailTrace_3223998 : CollatzResearch.WordTrace tailWord_3223998 prefixEnd_3223998 183940067014909147410901 := by
  unfold tailWord_3223998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14698608421751666983351081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78392578249342223911205765 14698608421751666983351081)
  ·
    refine ⟨11023956316313750237513311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14698608421751666983351081 11023956316313750237513311)
    ·
      refine ⟨16535934474470625356269967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023956316313750237513311 16535934474470625356269967)
      ·
        refine ⟨24803901711705938034404951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16535934474470625356269967 24803901711705938034404951)
        ·
          refine ⟨37205852567558907051607427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24803901711705938034404951 37205852567558907051607427)
          ·
            refine ⟨55808778851338360577411141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37205852567558907051607427 55808778851338360577411141)
            ·
              refine ⟨10464146034625942608264589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55808778851338360577411141 10464146034625942608264589)
              ·
                refine ⟨3924054762984728478099221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10464146034625942608264589 3924054762984728478099221)
                ·
                  refine ⟨183940067014909147410901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3924054762984728478099221 183940067014909147410901)
                  ·
                    rfl

theorem cell23_3223998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_3223998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3223998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3223998 prefixEnd_3223998 := by exact prefixLift 3223998
  have htrace : WordTrace (prefixWord ++ tailWord_3223998) baseStart_3223998 baseEnd_3223998 := by
    simpa [prefixWord, tailWord_3223998, baseEnd_3223998] using wordTrace_append hprefix tailTrace_3223998
  have hstable : (prefixWord ++ tailWord_3223998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3223998).length < 2 ^ (prefixWord ++ tailWord_3223998).sum := by decide
  have hdescent : baseEnd_3223998 < baseStart_3223998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3223998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224012 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3224012 : Nat := 118140960795 + 3224012 * 2 ^ 59
def prefixEnd_3224012 : Nat := 4983230072969 + 3 ^ 40 * 3224012 * 2
def baseEnd_3224012 : Nat := 1655467791863345271923045

theorem tailTrace_3224012 : CollatzResearch.WordTrace tailWord_3224012 prefixEnd_3224012 1655467791863345271923045 := by
  unfold tailWord_3224012
  simp only [CollatzResearch.WordTrace]
  refine ⟨58794688997981308128909145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78392918663975077505212193 58794688997981308128909145)
  ·
    refine ⟨44096016748485981096681859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58794688997981308128909145 44096016748485981096681859)
    ·
      refine ⟨66144025122728971645022789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44096016748485981096681859 66144025122728971645022789)
      ·
        refine ⟨12402004710511682183441773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66144025122728971645022789 12402004710511682183441773)
        ·
          refine ⟨4650751766441880818790665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12402004710511682183441773 4650751766441880818790665)
          ·
            refine ⟨3488063824831410614092999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650751766441880818790665 3488063824831410614092999)
            ·
              refine ⟨5232095737247115921139499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488063824831410614092999 5232095737247115921139499)
              ·
                refine ⟨7848143605870673881709249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232095737247115921139499 7848143605870673881709249)
                ·
                  refine ⟨5886107704403005411281937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7848143605870673881709249 5886107704403005411281937)
                  ·
                    refine ⟨4414580778302254058461453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886107704403005411281937 4414580778302254058461453)
                    ·
                      refine ⟨1655467791863345271923045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414580778302254058461453 1655467791863345271923045)
                      ·
                        rfl

theorem cell23_3224012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3224012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224012 prefixEnd_3224012 := by exact prefixLift 3224012
  have htrace : WordTrace (prefixWord ++ tailWord_3224012) baseStart_3224012 baseEnd_3224012 := by
    simpa [prefixWord, tailWord_3224012, baseEnd_3224012] using wordTrace_append hprefix tailTrace_3224012
  have hstable : (prefixWord ++ tailWord_3224012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224012).length < 2 ^ (prefixWord ++ tailWord_3224012).sum := by decide
  have hdescent : baseEnd_3224012 < baseStart_3224012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224042 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3224042 : Nat := 118140960795 + 3224042 * 2 ^ 59
def prefixEnd_3224042 : Nat := 4983230072969 + 3 ^ 40 * 3224042 * 2
def baseEnd_3224042 : Nat := 1655483196282980154547907

theorem tailTrace_3224042 : CollatzResearch.WordTrace tailWord_3224042 prefixEnd_3224042 1655483196282980154547907 := by
  unfold tailWord_3224042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397618046463482845352595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78393648123902620920940253 29397618046463482845352595)
  ·
    refine ⟨44096427069695224268028893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29397618046463482845352595 44096427069695224268028893)
    ·
      refine ⟨16536160151135709100510835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44096427069695224268028893 16536160151135709100510835)
      ·
        refine ⟨24804240226703563650766253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16536160151135709100510835 24804240226703563650766253)
        ·
          refine ⟨9301590085013836369037345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24804240226703563650766253 9301590085013836369037345)
          ·
            refine ⟨6976192563760377276778009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9301590085013836369037345 6976192563760377276778009)
            ·
              refine ⟨5232144422820282957583507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6976192563760377276778009 5232144422820282957583507)
              ·
                refine ⟨7848216634230424436375261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232144422820282957583507 7848216634230424436375261)
                ·
                  refine ⟨2943081237836409163640723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7848216634230424436375261 2943081237836409163640723)
                  ·
                    refine ⟨4414621856754613745461085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943081237836409163640723 4414621856754613745461085)
                    ·
                      refine ⟨1655483196282980154547907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414621856754613745461085 1655483196282980154547907)
                      ·
                        rfl

theorem cell23_3224042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3224042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224042 prefixEnd_3224042 := by exact prefixLift 3224042
  have htrace : WordTrace (prefixWord ++ tailWord_3224042) baseStart_3224042 baseEnd_3224042 := by
    simpa [prefixWord, tailWord_3224042, baseEnd_3224042] using wordTrace_append hprefix tailTrace_3224042
  have hstable : (prefixWord ++ tailWord_3224042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224042).length < 2 ^ (prefixWord ++ tailWord_3224042).sum := by decide
  have hdescent : baseEnd_3224042 < baseStart_3224042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224065 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3224065 : Nat := 118140960795 + 3224065 * 2 ^ 59
def prefixEnd_3224065 : Nat := 4983230072969 + 3 ^ 40 * 3224065 * 2
def baseEnd_3224065 : Nat := 1655495006338033564560301

theorem tailTrace_3224065 : CollatzResearch.WordTrace tailWord_3224065 prefixEnd_3224065 1655495006338033564560301 := by
  unfold tailWord_3224065
  simp only [CollatzResearch.WordTrace]
  refine ⟨117591311064770606309497649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78394207376513737539665099 117591311064770606309497649)
  ·
    refine ⟨88193483298577954732123237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117591311064770606309497649 88193483298577954732123237)
    ·
      refine ⟨16536278118483366512273107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88193483298577954732123237 16536278118483366512273107)
      ·
        refine ⟨24804417177725049768409661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16536278118483366512273107 24804417177725049768409661)
        ·
          refine ⟨9301656441646893663153623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24804417177725049768409661 9301656441646893663153623)
          ·
            refine ⟨13952484662470340494730435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9301656441646893663153623 13952484662470340494730435)
            ·
              refine ⟨20928726993705510742095653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13952484662470340494730435 20928726993705510742095653)
              ·
                refine ⟨3924136311319783264142935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20928726993705510742095653 3924136311319783264142935)
                ·
                  refine ⟨5886204466979674896214403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924136311319783264142935 5886204466979674896214403)
                  ·
                    refine ⟨8829306700469512344321605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886204466979674896214403 8829306700469512344321605)
                    ·
                      refine ⟨1655495006338033564560301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8829306700469512344321605 1655495006338033564560301)
                      ·
                        rfl

theorem cell23_3224065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3224065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224065 prefixEnd_3224065 := by exact prefixLift 3224065
  have htrace : WordTrace (prefixWord ++ tailWord_3224065) baseStart_3224065 baseEnd_3224065 := by
    simpa [prefixWord, tailWord_3224065, baseEnd_3224065] using wordTrace_append hprefix tailTrace_3224065
  have hstable : (prefixWord ++ tailWord_3224065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224065).length < 2 ^ (prefixWord ++ tailWord_3224065).sum := by decide
  have hdescent : baseEnd_3224065 < baseStart_3224065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224085 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_3224085 : Nat := 118140960795 + 3224085 * 2 ^ 59
def prefixEnd_3224085 : Nat := 4983230072969 + 3 ^ 40 * 3224085 * 2
def baseEnd_3224085 : Nat := 1655505275951123486310209

theorem tailTrace_3224085 : CollatzResearch.WordTrace tailWord_3224085 prefixEnd_3224085 1655505275951123486310209 := by
  unfold tailWord_3224085
  simp only [CollatzResearch.WordTrace]
  refine ⟨117592040524698149725225709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78394693683132099816817139 117592040524698149725225709)
  ·
    refine ⟨44097015196761806146959641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117592040524698149725225709 44097015196761806146959641)
    ·
      refine ⟨33072761397571354610219731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44097015196761806146959641 33072761397571354610219731)
      ·
        refine ⟨49609142096357031915329597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33072761397571354610219731 49609142096357031915329597)
        ·
          refine ⟨18603428286133886968248599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49609142096357031915329597 18603428286133886968248599)
          ·
            refine ⟨27905142429200830452372899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18603428286133886968248599 27905142429200830452372899)
            ·
              refine ⟨41857713643801245678559349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27905142429200830452372899 41857713643801245678559349)
              ·
                refine ⟨3924160654106366782364939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41857713643801245678559349 3924160654106366782364939)
                ·
                  refine ⟨5886240981159550173547409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924160654106366782364939 5886240981159550173547409)
                  ·
                    refine ⟨4414680735869662630160557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886240981159550173547409 4414680735869662630160557)
                    ·
                      refine ⟨1655505275951123486310209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414680735869662630160557 1655505275951123486310209)
                      ·
                        rfl

theorem cell23_3224085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_3224085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224085 prefixEnd_3224085 := by exact prefixLift 3224085
  have htrace : WordTrace (prefixWord ++ tailWord_3224085) baseStart_3224085 baseEnd_3224085 := by
    simpa [prefixWord, tailWord_3224085, baseEnd_3224085] using wordTrace_append hprefix tailTrace_3224085
  have hstable : (prefixWord ++ tailWord_3224085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224085).length < 2 ^ (prefixWord ++ tailWord_3224085).sum := by decide
  have hdescent : baseEnd_3224085 < baseStart_3224085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224088 : List Nat := [2, 1, 2, 3, 3, 3, 9]
def baseStart_3224088 : Nat := 118140960795 + 3224088 * 2 ^ 59
def prefixEnd_3224088 : Nat := 4983230072969 + 3 ^ 40 * 3224088 * 2
def baseEnd_3224088 : Nat := 20438355757939345365095

theorem tailTrace_3224088 : CollatzResearch.WordTrace tailWord_3224088 prefixEnd_3224088 20438355757939345365095 := by
  unfold tailWord_3224088
  simp only [CollatzResearch.WordTrace]
  refine ⟨58796074971843640618792459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78394766629124854158389945 58796074971843640618792459)
  ·
    refine ⟨88194112457765460928188689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58796074971843640618792459 88194112457765460928188689)
    ·
      refine ⟨66145584343324095696141517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88194112457765460928188689 66145584343324095696141517)
      ·
        refine ⟨24804594128746535886053069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66145584343324095696141517 24804594128746535886053069)
        ·
          refine ⟨9301722798279950957269901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24804594128746535886053069 9301722798279950957269901)
          ·
            refine ⟨3488146049354981608976213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9301722798279950957269901 3488146049354981608976213)
            ·
              refine ⟨20438355757939345365095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3488146049354981608976213 20438355757939345365095)
              ·
                rfl

theorem cell23_3224088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 9].length) (baseStart_3224088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224088 prefixEnd_3224088 := by exact prefixLift 3224088
  have htrace : WordTrace (prefixWord ++ tailWord_3224088) baseStart_3224088 baseEnd_3224088 := by
    simpa [prefixWord, tailWord_3224088, baseEnd_3224088] using wordTrace_append hprefix tailTrace_3224088
  have hstable : (prefixWord ++ tailWord_3224088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224088).length < 2 ^ (prefixWord ++ tailWord_3224088).sum := by decide
  have hdescent : baseEnd_3224088 < baseStart_3224088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224099 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 3, 2, 2]
def baseStart_3224099 : Nat := 118140960795 + 3224099 * 2 ^ 59
def prefixEnd_3224099 : Nat := 4983230072969 + 3 ^ 40 * 3224099 * 2
def baseEnd_3224099 : Nat := 1655512464680286431535145

theorem tailTrace_3224099 : CollatzResearch.WordTrace tailWord_3224099 prefixEnd_3224099 1655512464680286431535145 := by
  unfold tailWord_3224099
  simp only [CollatzResearch.WordTrace]
  refine ⟨117592551146647430116235351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78395034097764953410823567 117592551146647430116235351)
  ·
    refine ⟨176388826719971145174353027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117592551146647430116235351 176388826719971145174353027)
    ·
      refine ⟨264583240079956717761529541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176388826719971145174353027 264583240079956717761529541)
      ·
        refine ⟨49609357514991884580286789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264583240079956717761529541 49609357514991884580286789)
        ·
          refine ⟨9301754534060978358803773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49609357514991884580286789 9301754534060978358803773)
          ·
            refine ⟨3488157950272866884551415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9301754534060978358803773 3488157950272866884551415)
            ·
              refine ⟨5232236925409300326827123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488157950272866884551415 5232236925409300326827123)
              ·
                refine ⟨7848355388113950490240685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232236925409300326827123 7848355388113950490240685)
                ·
                  refine ⟨2943133270542731433840257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7848355388113950490240685 2943133270542731433840257)
                  ·
                    refine ⟨2207349952907048575380193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2943133270542731433840257 2207349952907048575380193)
                    ·
                      refine ⟨1655512464680286431535145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207349952907048575380193 1655512464680286431535145)
                      ·
                        rfl

theorem cell23_3224099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_3224099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224099 prefixEnd_3224099 := by exact prefixLift 3224099
  have htrace : WordTrace (prefixWord ++ tailWord_3224099) baseStart_3224099 baseEnd_3224099 := by
    simpa [prefixWord, tailWord_3224099, baseEnd_3224099] using wordTrace_append hprefix tailTrace_3224099
  have hstable : (prefixWord ++ tailWord_3224099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224099).length < 2 ^ (prefixWord ++ tailWord_3224099).sum := by decide
  have hdescent : baseEnd_3224099 < baseStart_3224099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224116 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3224116 : Nat := 118140960795 + 3224116 * 2 ^ 59
def prefixEnd_3224116 : Nat := 4983230072969 + 3 ^ 40 * 3224116 * 2
def baseEnd_3224116 : Nat := 1655521193851412865022567

theorem tailTrace_3224116 : CollatzResearch.WordTrace tailWord_3224116 prefixEnd_3224116 1655521193851412865022567 := by
  unfold tailWord_3224116
  simp only [CollatzResearch.WordTrace]
  refine ⟨58796585593792921009802101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78395447458390561346402801 58796585593792921009802101)
  ·
    refine ⟨5512179899418086344668947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58796585593792921009802101 5512179899418086344668947)
    ·
      refine ⟨8268269849127129517003421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512179899418086344668947 8268269849127129517003421)
      ·
        refine ⟨3100601193422673568876283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8268269849127129517003421 3100601193422673568876283)
        ·
          refine ⟨4650901790134010353314425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100601193422673568876283 4650901790134010353314425)
          ·
            refine ⟨3488176342600507764985819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650901790134010353314425 3488176342600507764985819)
            ·
              refine ⟨5232264513900761647478729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488176342600507764985819 5232264513900761647478729)
              ·
                refine ⟨3924198385425571235609047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232264513900761647478729 3924198385425571235609047)
                ·
                  refine ⟨5886297578138356853413571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924198385425571235609047 5886297578138356853413571)
                  ·
                    refine ⟨8829446367207535280120357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886297578138356853413571 8829446367207535280120357)
                    ·
                      refine ⟨1655521193851412865022567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8829446367207535280120357 1655521193851412865022567)
                      ·
                        rfl

theorem cell23_3224116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3224116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224116 prefixEnd_3224116 := by exact prefixLift 3224116
  have htrace : WordTrace (prefixWord ++ tailWord_3224116) baseStart_3224116 baseEnd_3224116 := by
    simpa [prefixWord, tailWord_3224116, baseEnd_3224116] using wordTrace_append hprefix tailTrace_3224116
  have hstable : (prefixWord ++ tailWord_3224116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224116).length < 2 ^ (prefixWord ++ tailWord_3224116).sum := by decide
  have hdescent : baseEnd_3224116 < baseStart_3224116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224142 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_3224142 : Nat := 118140960795 + 3224142 * 2 ^ 59
def prefixEnd_3224142 : Nat := 4983230072969 + 3 ^ 40 * 3224142 * 2
def baseEnd_3224142 : Nat := 1655534544348429763297447

theorem tailTrace_3224142 : CollatzResearch.WordTrace tailWord_3224142 prefixEnd_3224142 1655534544348429763297447 := by
  unfold tailWord_3224142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14699264935686456057506335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78396079656994432306700453 14699264935686456057506335)
  ·
    refine ⟨22048897403529684086259503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14699264935686456057506335 22048897403529684086259503)
    ·
      refine ⟨33073346105294526129389255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22048897403529684086259503 33073346105294526129389255)
      ·
        refine ⟨49610019157941789194083883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33073346105294526129389255 49610019157941789194083883)
        ·
          refine ⟨74415028736912683791125825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49610019157941789194083883 74415028736912683791125825)
          ·
            refine ⟨55811271552684512843344369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74415028736912683791125825 55811271552684512843344369)
            ·
              refine ⟨41858453664513384632508277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55811271552684512843344369 41858453664513384632508277)
              ·
                refine ⟨3924230031048129809297651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41858453664513384632508277 3924230031048129809297651)
                ·
                  refine ⟨5886345046572194713946477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924230031048129809297651 5886345046572194713946477)
                  ·
                    refine ⟨2207379392464573017729929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5886345046572194713946477 2207379392464573017729929)
                    ·
                      refine ⟨1655534544348429763297447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207379392464573017729929 1655534544348429763297447)
                      ·
                        rfl

theorem cell23_3224142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_3224142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224142 prefixEnd_3224142 := by exact prefixLift 3224142
  have htrace : WordTrace (prefixWord ++ tailWord_3224142) baseStart_3224142 baseEnd_3224142 := by
    simpa [prefixWord, tailWord_3224142, baseEnd_3224142] using wordTrace_append hprefix tailTrace_3224142
  have hstable : (prefixWord ++ tailWord_3224142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224142).length < 2 ^ (prefixWord ++ tailWord_3224142).sum := by decide
  have hdescent : baseEnd_3224142 < baseStart_3224142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224165 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_3224165 : Nat := 118140960795 + 3224165 * 2 ^ 59
def prefixEnd_3224165 : Nat := 4983230072969 + 3 ^ 40 * 3224165 * 2
def baseEnd_3224165 : Nat := 551848784801161057769947

theorem tailTrace_3224165 : CollatzResearch.WordTrace tailWord_3224165 prefixEnd_3224165 551848784801161057769947 := by
  unfold tailWord_3224165
  simp only [CollatzResearch.WordTrace]
  refine ⟨117594958364408323388137949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78396638909605548925425299 117594958364408323388137949)
  ·
    refine ⟨44098109386653121270551731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117594958364408323388137949 44098109386653121270551731)
    ·
      refine ⟨66147164079979681905827597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44098109386653121270551731 66147164079979681905827597)
      ·
        refine ⟨24805186529992380714685349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66147164079979681905827597 24805186529992380714685349)
        ·
          refine ⟨4650972474373571384003503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24805186529992380714685349 4650972474373571384003503)
          ·
            refine ⟨6976458711560357076005255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650972474373571384003503 6976458711560357076005255)
            ·
              refine ⟨10464688067340535614007883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976458711560357076005255 10464688067340535614007883)
              ·
                refine ⟨15697032101010803421011825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10464688067340535614007883 15697032101010803421011825)
                ·
                  refine ⟨11772774075758102565758869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15697032101010803421011825 11772774075758102565758869)
                  ·
                    refine ⟨551848784801161057769947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11772774075758102565758869 551848784801161057769947)
                    ·
                      rfl

theorem cell23_3224165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_3224165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224165 prefixEnd_3224165 := by exact prefixLift 3224165
  have htrace : WordTrace (prefixWord ++ tailWord_3224165) baseStart_3224165 baseEnd_3224165 := by
    simpa [prefixWord, tailWord_3224165, baseEnd_3224165] using wordTrace_append hprefix tailTrace_3224165
  have hstable : (prefixWord ++ tailWord_3224165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224165).length < 2 ^ (prefixWord ++ tailWord_3224165).sum := by decide
  have hdescent : baseEnd_3224165 < baseStart_3224165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224195 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 5]
def baseStart_3224195 : Nat := 118140960795 + 3224195 * 2 ^ 59
def prefixEnd_3224195 : Nat := 4983230072969 + 3 ^ 40 * 3224195 * 2
def baseEnd_3224195 : Nat := 183951306535902006214967

theorem tailTrace_3224195 : CollatzResearch.WordTrace tailWord_3224195 prefixEnd_3224195 183951306535902006214967 := by
  unfold tailWord_3224195
  simp only [CollatzResearch.WordTrace]
  refine ⟨117596052554299638511730039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78397368369533092341153359 117596052554299638511730039)
  ·
    refine ⟨176394078831449457767595059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117596052554299638511730039 176394078831449457767595059)
    ·
      refine ⟨264591118247174186651392589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176394078831449457767595059 264591118247174186651392589)
      ·
        refine ⟨99221669342690319994272221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264591118247174186651392589 99221669342690319994272221)
        ·
          refine ⟨37208126003508869997852083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99221669342690319994272221 37208126003508869997852083)
          ·
            refine ⟨55812189005263304996778125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37208126003508869997852083 55812189005263304996778125)
            ·
              refine ⟨20929570876973739373791797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55812189005263304996778125 20929570876973739373791797)
              ·
                refine ⟨1962147269716288066292981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20929570876973739373791797 1962147269716288066292981)
                ·
                  refine ⟨183951306535902006214967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1962147269716288066292981 183951306535902006214967)
                  ·
                    rfl

theorem cell23_3224195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 5].length) (baseStart_3224195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224195 prefixEnd_3224195 := by exact prefixLift 3224195
  have htrace : WordTrace (prefixWord ++ tailWord_3224195) baseStart_3224195 baseEnd_3224195 := by
    simpa [prefixWord, tailWord_3224195, baseEnd_3224195] using wordTrace_append hprefix tailTrace_3224195
  have hstable : (prefixWord ++ tailWord_3224195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224195).length < 2 ^ (prefixWord ++ tailWord_3224195).sum := by decide
  have hdescent : baseEnd_3224195 < baseStart_3224195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224212 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 7]
def baseStart_3224212 : Nat := 118140960795 + 3224212 * 2 ^ 59
def prefixEnd_3224212 : Nat := 4983230072969 + 3 ^ 40 * 3224212 * 2
def baseEnd_3224212 : Nat := 183952276443804943269125

theorem tailTrace_3224212 : CollatzResearch.WordTrace tailWord_3224212 prefixEnd_3224212 183952276443804943269125 := by
  unfold tailWord_3224212
  simp only [CollatzResearch.WordTrace]
  refine ⟨58798336297619025207549445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78397781730158700276732593 58798336297619025207549445)
  ·
    refine ⟨11024688055803567226415521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58798336297619025207549445 11024688055803567226415521)
    ·
      refine ⟨8268516041852675419811641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11024688055803567226415521 8268516041852675419811641)
      ·
        refine ⟨6201387031389506564858731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8268516041852675419811641 6201387031389506564858731)
        ·
          refine ⟨9302080547084259847288097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6201387031389506564858731 9302080547084259847288097)
          ·
            refine ⟨6976560410313194885466073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9302080547084259847288097 6976560410313194885466073)
            ·
              refine ⟨5232420307734896164099555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6976560410313194885466073 5232420307734896164099555)
              ·
                refine ⟨7848630461602344246149333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232420307734896164099555 7848630461602344246149333)
                ·
                  refine ⟨183952276443804943269125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7848630461602344246149333 183952276443804943269125)
                  ·
                    rfl

theorem cell23_3224212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_3224212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224212 prefixEnd_3224212 := by exact prefixLift 3224212
  have htrace : WordTrace (prefixWord ++ tailWord_3224212) baseStart_3224212 baseEnd_3224212 := by
    simpa [prefixWord, tailWord_3224212, baseEnd_3224212] using wordTrace_append hprefix tailTrace_3224212
  have hstable : (prefixWord ++ tailWord_3224212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224212).length < 2 ^ (prefixWord ++ tailWord_3224212).sum := by decide
  have hdescent : baseEnd_3224212 < baseStart_3224212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224222 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3224222 : Nat := 118140960795 + 3224222 * 2 ^ 59
def prefixEnd_3224222 : Nat := 4983230072969 + 3 ^ 40 * 3224222 * 2
def baseEnd_3224222 : Nat := 1655575622800789450297079

theorem tailTrace_3224222 : CollatzResearch.WordTrace tailWord_3224222 prefixEnd_3224222 1655575622800789450297079 := by
  unfold tailWord_3224222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14699629665650227765370365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78398024883467881415308613 14699629665650227765370365)
  ·
    refine ⟨5512361124618835412013887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14699629665650227765370365 5512361124618835412013887)
    ·
      refine ⟨8268541686928253118020831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512361124618835412013887 8268541686928253118020831)
      ·
        refine ⟨12402812530392379677031247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268541686928253118020831 12402812530392379677031247)
        ·
          refine ⟨18604218795588569515546871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12402812530392379677031247 18604218795588569515546871)
          ·
            refine ⟨27906328193382854273320307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18604218795588569515546871 27906328193382854273320307)
            ·
              refine ⟨41859492290074281409980461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27906328193382854273320307 41859492290074281409980461)
              ·
                refine ⟨15697309608777855528742673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41859492290074281409980461 15697309608777855528742673)
                ·
                  refine ⟨11772982206583391646557005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15697309608777855528742673 11772982206583391646557005)
                  ·
                    refine ⟨4414868327468771867458877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11772982206583391646557005 4414868327468771867458877)
                    ·
                      refine ⟨1655575622800789450297079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4414868327468771867458877 1655575622800789450297079)
                      ·
                        rfl

theorem cell23_3224222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3224222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224222 prefixEnd_3224222 := by exact prefixLift 3224222
  have htrace : WordTrace (prefixWord ++ tailWord_3224222) baseStart_3224222 baseEnd_3224222 := by
    simpa [prefixWord, tailWord_3224222, baseEnd_3224222] using wordTrace_append hprefix tailTrace_3224222
  have hstable : (prefixWord ++ tailWord_3224222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224222).length < 2 ^ (prefixWord ++ tailWord_3224222).sum := by decide
  have hdescent : baseEnd_3224222 < baseStart_3224222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224248 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3224248 : Nat := 118140960795 + 3224248 * 2 ^ 59
def prefixEnd_3224248 : Nat := 4983230072969 + 3 ^ 40 * 3224248 * 2
def baseEnd_3224248 : Nat := 1655588973297806348571959

theorem tailTrace_3224248 : CollatzResearch.WordTrace tailWord_3224248 prefixEnd_3224248 1655588973297806348571959 := by
  unfold tailWord_3224248
  simp only [CollatzResearch.WordTrace]
  refine ⟨58798992811553814281704699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78398657082071752375606265 58798992811553814281704699)
  ·
    refine ⟨88198489217330721422557049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58798992811553814281704699 88198489217330721422557049)
    ·
      refine ⟨66148866912998041066917787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88198489217330721422557049 66148866912998041066917787)
      ·
        refine ⟨99223300369497061600376681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66148866912998041066917787 99223300369497061600376681)
        ·
          refine ⟨74417475277122796200282511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99223300369497061600376681 74417475277122796200282511)
          ·
            refine ⟨111626212915684194300423767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74417475277122796200282511 111626212915684194300423767)
            ·
              refine ⟨167439319373526291450635651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111626212915684194300423767 167439319373526291450635651)
              ·
                refine ⟨251158979060289437175953477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167439319373526291450635651 251158979060289437175953477)
                ·
                  refine ⟨47092308573804269470491277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251158979060289437175953477 47092308573804269470491277)
                  ·
                    refine ⟨17659615715176601051434229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47092308573804269470491277 17659615715176601051434229)
                    ·
                      refine ⟨1655588973297806348571959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17659615715176601051434229 1655588973297806348571959)
                      ·
                        rfl

theorem cell23_3224248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3224248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224248 prefixEnd_3224248 := by exact prefixLift 3224248
  have htrace : WordTrace (prefixWord ++ tailWord_3224248) baseStart_3224248 baseEnd_3224248 := by
    simpa [prefixWord, tailWord_3224248, baseEnd_3224248] using wordTrace_append hprefix tailTrace_3224248
  have hstable : (prefixWord ++ tailWord_3224248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224248).length < 2 ^ (prefixWord ++ tailWord_3224248).sum := by decide
  have hdescent : baseEnd_3224248 < baseStart_3224248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224269 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3224269 : Nat := 118140960795 + 3224269 * 2 ^ 59
def prefixEnd_3224269 : Nat := 4983230072969 + 3 ^ 40 * 3224269 * 2
def baseEnd_3224269 : Nat := 1655599756391550766409363

theorem tailTrace_3224269 : CollatzResearch.WordTrace tailWord_3224269 prefixEnd_3224269 1655599756391550766409363 := by
  unfold tailWord_3224269
  simp only [CollatzResearch.WordTrace]
  refine ⟨117598751556031549149923861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78399167704021032766615907 117598751556031549149923861)
  ·
    refine ⟨5512441479188978866402681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117598751556031549149923861 5512441479188978866402681)
    ·
      refine ⟨4134331109391734149802011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5512441479188978866402681 4134331109391734149802011)
      ·
        refine ⟨6201496664087601224703017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4134331109391734149802011 6201496664087601224703017)
        ·
          refine ⟨4651122498065700918527263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6201496664087601224703017 4651122498065700918527263)
          ·
            refine ⟨6976683747098551377790895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4651122498065700918527263 6976683747098551377790895)
            ·
              refine ⟨10465025620647827066686343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976683747098551377790895 10465025620647827066686343)
              ·
                refine ⟨15697538430971740600029515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10465025620647827066686343 15697538430971740600029515)
                ·
                  refine ⟨23546307646457610900044273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15697538430971740600029515 23546307646457610900044273)
                  ·
                    refine ⟨17659730734843208175033205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23546307646457610900044273 17659730734843208175033205)
                    ·
                      refine ⟨1655599756391550766409363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17659730734843208175033205 1655599756391550766409363)
                      ·
                        rfl

theorem cell23_3224269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3224269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224269 prefixEnd_3224269 := by exact prefixLift 3224269
  have htrace : WordTrace (prefixWord ++ tailWord_3224269) baseStart_3224269 baseEnd_3224269 := by
    simpa [prefixWord, tailWord_3224269, baseEnd_3224269] using wordTrace_append hprefix tailTrace_3224269
  have hstable : (prefixWord ++ tailWord_3224269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224269).length < 2 ^ (prefixWord ++ tailWord_3224269).sum := by decide
  have hdescent : baseEnd_3224269 < baseStart_3224269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224335 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_3224335 : Nat := 118140960795 + 3224335 * 2 ^ 59
def prefixEnd_3224335 : Nat := 4983230072969 + 3 ^ 40 * 3224335 * 2
def baseEnd_3224335 : Nat := 1655633646114747508184059

theorem tailTrace_3224335 : CollatzResearch.WordTrace tailWord_3224335 prefixEnd_3224335 1655633646114747508184059 := by
  unfold tailWord_3224335
  simp only [CollatzResearch.WordTrace]
  refine ⟨117601158773792442421826459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78400772515861628281217639 117601158773792442421826459)
  ·
    refine ⟨176401738160688663632739689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117601158773792442421826459 176401738160688663632739689)
    ·
      refine ⟨132301303620516497724554767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176401738160688663632739689 132301303620516497724554767)
      ·
        refine ⟨198451955430774746586832151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132301303620516497724554767 198451955430774746586832151)
        ·
          refine ⟨297677933146162119880248227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198451955430774746586832151 297677933146162119880248227)
          ·
            refine ⟨446516899719243179820372341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297677933146162119880248227 446516899719243179820372341)
            ·
              refine ⟨41860959348679048108159907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446516899719243179820372341 41860959348679048108159907)
              ·
                refine ⟨62791439023018572162239861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41860959348679048108159907 62791439023018572162239861)
                ·
                  refine ⟨5886697408407991140209987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62791439023018572162239861 5886697408407991140209987)
                  ·
                    refine ⟨8830046112611986710314981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886697408407991140209987 8830046112611986710314981)
                    ·
                      refine ⟨1655633646114747508184059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8830046112611986710314981 1655633646114747508184059)
                      ·
                        rfl

theorem cell23_3224335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_3224335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224335 prefixEnd_3224335 := by exact prefixLift 3224335
  have htrace : WordTrace (prefixWord ++ tailWord_3224335) baseStart_3224335 baseEnd_3224335 := by
    simpa [prefixWord, tailWord_3224335, baseEnd_3224335] using wordTrace_append hprefix tailTrace_3224335
  have hstable : (prefixWord ++ tailWord_3224335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224335).length < 2 ^ (prefixWord ++ tailWord_3224335).sum := by decide
  have hdescent : baseEnd_3224335 < baseStart_3224335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224352 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3224352 : Nat := 118140960795 + 3224352 * 2 ^ 59
def prefixEnd_3224352 : Nat := 4983230072969 + 3 ^ 40 * 3224352 * 2
def baseEnd_3224352 : Nat := 1655642375285873941671481

theorem tailTrace_3224352 : CollatzResearch.WordTrace tailWord_3224352 prefixEnd_3224352 1655642375285873941671481 := by
  unfold tailWord_3224352
  simp only [CollatzResearch.WordTrace]
  refine ⟨58800889407365427162597655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78401185876487236216796873 58800889407365427162597655)
  ·
    refine ⟨88201334111048140743896483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58800889407365427162597655 88201334111048140743896483)
    ·
      refine ⟨132302001166572211115844725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88201334111048140743896483 132302001166572211115844725)
      ·
        refine ⟨12403312609366144792110443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132302001166572211115844725 12403312609366144792110443)
        ·
          refine ⟨18604968914049217188165665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403312609366144792110443 18604968914049217188165665)
          ·
            refine ⟨13953726685536912891124249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18604968914049217188165665 13953726685536912891124249)
            ·
              refine ⟨10465295014152684668343187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13953726685536912891124249 10465295014152684668343187)
              ·
                refine ⟨15697942521229027002514781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10465295014152684668343187 15697942521229027002514781)
                ·
                  refine ⟨5886728445460885125943043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15697942521229027002514781 5886728445460885125943043)
                  ·
                    refine ⟨8830092668191327688914565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5886728445460885125943043 8830092668191327688914565)
                    ·
                      refine ⟨1655642375285873941671481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8830092668191327688914565 1655642375285873941671481)
                      ·
                        rfl

theorem cell23_3224352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3224352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224352 prefixEnd_3224352 := by exact prefixLift 3224352
  have htrace : WordTrace (prefixWord ++ tailWord_3224352) baseStart_3224352 baseEnd_3224352 := by
    simpa [prefixWord, tailWord_3224352, baseEnd_3224352] using wordTrace_append hprefix tailTrace_3224352
  have hstable : (prefixWord ++ tailWord_3224352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224352).length < 2 ^ (prefixWord ++ tailWord_3224352).sum := by decide
  have hdescent : baseEnd_3224352 < baseStart_3224352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224366 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3224366 : Nat := 118140960795 + 3224366 * 2 ^ 59
def prefixEnd_3224366 : Nat := 4983230072969 + 3 ^ 40 * 3224366 * 2
def baseEnd_3224366 : Nat := 551883188005012295632139

theorem tailTrace_3224366 : CollatzResearch.WordTrace tailWord_3224366 prefixEnd_3224366 551883188005012295632139 := by
  unfold tailWord_3224366
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700286179585016839525619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78401526291120089810803301 14700286179585016839525619)
  ·
    refine ⟨22050429269377525259288429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14700286179585016839525619 22050429269377525259288429)
    ·
      refine ⟨8268910976016571972233161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22050429269377525259288429 8268910976016571972233161)
      ·
        refine ⟨6201683232012428979174871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8268910976016571972233161 6201683232012428979174871)
        ·
          refine ⟨9302524848018643468762307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6201683232012428979174871 9302524848018643468762307)
          ·
            refine ⟨13953787272027965203143461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9302524848018643468762307 13953787272027965203143461)
            ·
              refine ⟨2616335113505243475589399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13953787272027965203143461 2616335113505243475589399)
              ·
                refine ⟨3924502670257865213384099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616335113505243475589399 3924502670257865213384099)
                ·
                  refine ⟨5886754005386797820076149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924502670257865213384099 5886754005386797820076149)
                  ·
                    refine ⟨551883188005012295632139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5886754005386797820076149 551883188005012295632139)
                    ·
                      rfl

theorem cell23_3224366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3224366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224366 prefixEnd_3224366 := by exact prefixLift 3224366
  have htrace : WordTrace (prefixWord ++ tailWord_3224366) baseStart_3224366 baseEnd_3224366 := by
    simpa [prefixWord, tailWord_3224366, baseEnd_3224366] using wordTrace_append hprefix tailTrace_3224366
  have hstable : (prefixWord ++ tailWord_3224366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224366).length < 2 ^ (prefixWord ++ tailWord_3224366).sum := by decide
  have hdescent : baseEnd_3224366 < baseStart_3224366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224369 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_3224369 : Nat := 118140960795 + 3224369 * 2 ^ 59
def prefixEnd_3224369 : Nat := 4983230072969 + 3 ^ 40 * 3224369 * 2
def baseEnd_3224369 : Nat := 1655651104457000375158903

theorem tailTrace_3224369 : CollatzResearch.WordTrace tailWord_3224369 prefixEnd_3224369 1655651104457000375158903 := by
  unfold tailWord_3224369
  simp only [CollatzResearch.WordTrace]
  refine ⟨117602398855669266228564161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78401599237112844152376107 117602398855669266228564161)
  ·
    refine ⟨88201799141751949671423121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117602398855669266228564161 88201799141751949671423121)
    ·
      refine ⟨66151349356313962253567341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88201799141751949671423121 66151349356313962253567341)
      ·
        refine ⟨24806756008617735845087753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66151349356313962253567341 24806756008617735845087753)
        ·
          refine ⟨18605067006463301883815815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24806756008617735845087753 18605067006463301883815815)
          ·
            refine ⟨27907600509694952825723723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18605067006463301883815815 27907600509694952825723723)
            ·
              refine ⟨41861400764542429238585585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27907600509694952825723723 41861400764542429238585585)
              ·
                refine ⟨31396050573406821928939189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41861400764542429238585585 31396050573406821928939189)
                ·
                  refine ⟨2943379741256889555838049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31396050573406821928939189 2943379741256889555838049)
                  ·
                    refine ⟨2207534805942667166878537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2943379741256889555838049 2207534805942667166878537)
                    ·
                      refine ⟨1655651104457000375158903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207534805942667166878537 1655651104457000375158903)
                      ·
                        rfl

theorem cell23_3224369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_3224369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224369 prefixEnd_3224369 := by exact prefixLift 3224369
  have htrace : WordTrace (prefixWord ++ tailWord_3224369) baseStart_3224369 baseEnd_3224369 := by
    simpa [prefixWord, tailWord_3224369, baseEnd_3224369] using wordTrace_append hprefix tailTrace_3224369
  have hstable : (prefixWord ++ tailWord_3224369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224369).length < 2 ^ (prefixWord ++ tailWord_3224369).sum := by decide
  have hdescent : baseEnd_3224369 < baseStart_3224369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224396 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_3224396 : Nat := 118140960795 + 3224396 * 2 ^ 59
def prefixEnd_3224396 : Nat := 4983230072969 + 3 ^ 40 * 3224396 * 2
def baseEnd_3224396 : Nat := 551888322811557256507093

theorem tailTrace_3224396 : CollatzResearch.WordTrace tailWord_3224396 prefixEnd_3224396 551888322811557256507093 := by
  unfold tailWord_3224396
  simp only [CollatzResearch.WordTrace]
  refine ⟨58801691813285724919898521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78402255751047633226531361 58801691813285724919898521)
  ·
    refine ⟨44101268859964293689923891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58801691813285724919898521 44101268859964293689923891)
    ·
      refine ⟨66151903289946440534885837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44101268859964293689923891 66151903289946440534885837)
      ·
        refine ⟨24806963733729915200582189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66151903289946440534885837 24806963733729915200582189)
        ·
          refine ⟨9302611400148718200218321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24806963733729915200582189 9302611400148718200218321)
          ·
            refine ⟨6976958550111538650163741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9302611400148718200218321 6976958550111538650163741)
            ·
              refine ⟨2616359456291826993811403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6976958550111538650163741 2616359456291826993811403)
              ·
                refine ⟨3924539184437740490717105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616359456291826993811403 3924539184437740490717105)
                ·
                  refine ⟨2943404388328305368037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924539184437740490717105 2943404388328305368037829)
                  ·
                    refine ⟨551888322811557256507093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943404388328305368037829 551888322811557256507093)
                    ·
                      rfl

theorem cell23_3224396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_3224396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224396 prefixEnd_3224396 := by exact prefixLift 3224396
  have htrace : WordTrace (prefixWord ++ tailWord_3224396) baseStart_3224396 baseEnd_3224396 := by
    simpa [prefixWord, tailWord_3224396, baseEnd_3224396] using wordTrace_append hprefix tailTrace_3224396
  have hstable : (prefixWord ++ tailWord_3224396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224396).length < 2 ^ (prefixWord ++ tailWord_3224396).sum := by decide
  have hdescent : baseEnd_3224396 < baseStart_3224396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224415 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3224415 : Nat := 118140960795 + 3224415 * 2 ^ 59
def prefixEnd_3224415 : Nat := 4983230072969 + 3 ^ 40 * 3224415 * 2
def baseEnd_3224415 : Nat := 1655674724567107195183691

theorem tailTrace_3224415 : CollatzResearch.WordTrace tailWord_3224415 prefixEnd_3224415 1655674724567107195183691 := by
  unfold tailWord_3224415
  simp only [CollatzResearch.WordTrace]
  refine ⟨117604076613502616084738699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78402717742335077389825799 117604076613502616084738699)
  ·
    refine ⟨176406114920253924127108049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117604076613502616084738699 176406114920253924127108049)
    ·
      refine ⟨132304586190190443095331037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176406114920253924127108049 132304586190190443095331037)
      ·
        refine ⟨49614219821321416160749139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132304586190190443095331037 49614219821321416160749139)
        ·
          refine ⟨74421329731982124241123709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49614219821321416160749139 74421329731982124241123709)
          ·
            refine ⟨27907998649493296590421391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74421329731982124241123709 27907998649493296590421391)
            ·
              refine ⟨41861997974239944885632087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27907998649493296590421391 41861997974239944885632087)
              ·
                refine ⟨62792996961359917328448131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41861997974239944885632087 62792996961359917328448131)
                ·
                  refine ⟨94189495442039875992672197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62792996961359917328448131 94189495442039875992672197)
                  ·
                    refine ⟨17660530395382476748626037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94189495442039875992672197 17660530395382476748626037)
                    ·
                      refine ⟨1655674724567107195183691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17660530395382476748626037 1655674724567107195183691)
                      ·
                        rfl

theorem cell23_3224415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3224415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224415 prefixEnd_3224415 := by exact prefixLift 3224415
  have htrace : WordTrace (prefixWord ++ tailWord_3224415) baseStart_3224415 baseEnd_3224415 := by
    simpa [prefixWord, tailWord_3224415, baseEnd_3224415] using wordTrace_append hprefix tailTrace_3224415
  have hstable : (prefixWord ++ tailWord_3224415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224415).length < 2 ^ (prefixWord ++ tailWord_3224415).sum := by decide
  have hdescent : baseEnd_3224415 < baseStart_3224415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224419 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3224419 : Nat := 118140960795 + 3224419 * 2 ^ 59
def prefixEnd_3224419 : Nat := 4983230072969 + 3 ^ 40 * 3224419 * 2
def baseEnd_3224419 : Nat := 1655676778489725179533673

theorem tailTrace_3224419 : CollatzResearch.WordTrace tailWord_3224419 prefixEnd_3224419 1655676778489725179533673 := by
  unfold tailWord_3224419
  simp only [CollatzResearch.WordTrace]
  refine ⟨117604222505488124767884311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78402815003658749845256207 117604222505488124767884311)
  ·
    refine ⟨176406333758232187151826467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117604222505488124767884311 176406333758232187151826467)
    ·
      refine ⟨264609500637348280727739701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176406333758232187151826467 264609500637348280727739701)
      ·
        refine ⟨24807140684751401318225597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264609500637348280727739701 24807140684751401318225597)
        ·
          refine ⟨9302677756781775494334599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24807140684751401318225597 9302677756781775494334599)
          ·
            refine ⟨13954016635172663241501899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9302677756781775494334599 13954016635172663241501899)
            ·
              refine ⟨20931024952758994862252849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954016635172663241501899 20931024952758994862252849)
              ·
                refine ⟨15698268714569246146689637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20931024952758994862252849 15698268714569246146689637)
                ·
                  refine ⟨2943425383981733652504307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15698268714569246146689637 2943425383981733652504307)
                  ·
                    refine ⟨4415138075972600478756461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943425383981733652504307 4415138075972600478756461)
                    ·
                      refine ⟨1655676778489725179533673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4415138075972600478756461 1655676778489725179533673)
                      ·
                        rfl

theorem cell23_3224419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3224419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224419 prefixEnd_3224419 := by exact prefixLift 3224419
  have htrace : WordTrace (prefixWord ++ tailWord_3224419) baseStart_3224419 baseEnd_3224419 := by
    simpa [prefixWord, tailWord_3224419, baseEnd_3224419] using wordTrace_append hprefix tailTrace_3224419
  have hstable : (prefixWord ++ tailWord_3224419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224419).length < 2 ^ (prefixWord ++ tailWord_3224419).sum := by decide
  have hdescent : baseEnd_3224419 < baseStart_3224419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224420 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_3224420 : Nat := 118140960795 + 3224420 * 2 ^ 59
def prefixEnd_3224420 : Nat := 4983230072969 + 3 ^ 40 * 3224420 * 2
def baseEnd_3224420 : Nat := 1655677291970379675621169

theorem tailTrace_3224420 : CollatzResearch.WordTrace tailWord_3224420 prefixEnd_3224420 1655677291970379675621169 := by
  unfold tailWord_3224420
  simp only [CollatzResearch.WordTrace]
  refine ⟨58802129489242250969335357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78402839318989667959113809 58802129489242250969335357)
  ·
    refine ⟨22050798558465844113500759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58802129489242250969335357 22050798558465844113500759)
    ·
      refine ⟨33076197837698766170251139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22050798558465844113500759 33076197837698766170251139)
      ·
        refine ⟨49614296756548149255376709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33076197837698766170251139 49614296756548149255376709)
        ·
          refine ⟨9302680641852777985383133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49614296756548149255376709 9302680641852777985383133)
          ·
            refine ⟨3488505240694791744518675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9302680641852777985383133 3488505240694791744518675)
            ·
              refine ⟨5232757861042187616778013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488505240694791744518675 5232757861042187616778013)
              ·
                refine ⟨1962284197890820356291755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5232757861042187616778013 1962284197890820356291755)
                ·
                  refine ⟨2943426296836230534437633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962284197890820356291755 2943426296836230534437633)
                  ·
                    refine ⟨2207569722627172900828225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2943426296836230534437633 2207569722627172900828225)
                    ·
                      refine ⟨1655677291970379675621169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207569722627172900828225 1655677291970379675621169)
                      ·
                        rfl

theorem cell23_3224420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_3224420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224420 prefixEnd_3224420 := by exact prefixLift 3224420
  have htrace : WordTrace (prefixWord ++ tailWord_3224420) baseStart_3224420 baseEnd_3224420 := by
    simpa [prefixWord, tailWord_3224420, baseEnd_3224420] using wordTrace_append hprefix tailTrace_3224420
  have hstable : (prefixWord ++ tailWord_3224420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224420).length < 2 ^ (prefixWord ++ tailWord_3224420).sum := by decide
  have hdescent : baseEnd_3224420 < baseStart_3224420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224425 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_3224425 : Nat := 118140960795 + 3224425 * 2 ^ 59
def prefixEnd_3224425 : Nat := 4983230072969 + 3 ^ 40 * 3224425 * 2
def baseEnd_3224425 : Nat := 1655679859373652156058645

theorem tailTrace_3224425 : CollatzResearch.WordTrace tailWord_3224425 prefixEnd_3224425 1655679859373652156058645 := by
  unfold tailWord_3224425
  simp only [CollatzResearch.WordTrace]
  refine ⟨117604441343466387792602729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78402960895644258528401819 117604441343466387792602729)
  ·
    refine ⟨88203331007599790844452047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117604441343466387792602729 88203331007599790844452047)
    ·
      refine ⟨132304996511399686266678071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88203331007599790844452047 132304996511399686266678071)
      ·
        refine ⟨198457494767099529400017107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132304996511399686266678071 198457494767099529400017107)
        ·
          refine ⟨297686242150649294100025661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198457494767099529400017107 297686242150649294100025661)
          ·
            refine ⟨111632340806493485287509623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297686242150649294100025661 111632340806493485287509623)
            ·
              refine ⟨167448511209740227931264435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111632340806493485287509623 167448511209740227931264435)
              ·
                refine ⟨251172766814610341896896653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167448511209740227931264435 251172766814610341896896653)
                ·
                  refine ⟨94189787555478878211336245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251172766814610341896896653 94189787555478878211336245)
                  ·
                    refine ⟨8830292583326144832312773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94189787555478878211336245 8830292583326144832312773)
                    ·
                      refine ⟨1655679859373652156058645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8830292583326144832312773 1655679859373652156058645)
                      ·
                        rfl

theorem cell23_3224425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_3224425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224425 prefixEnd_3224425 := by exact prefixLift 3224425
  have htrace : WordTrace (prefixWord ++ tailWord_3224425) baseStart_3224425 baseEnd_3224425 := by
    simpa [prefixWord, tailWord_3224425, baseEnd_3224425] using wordTrace_append hprefix tailTrace_3224425
  have hstable : (prefixWord ++ tailWord_3224425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224425).length < 2 ^ (prefixWord ++ tailWord_3224425).sum := by decide
  have hdescent : baseEnd_3224425 < baseStart_3224425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224429 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_3224429 : Nat := 118140960795 + 3224429 * 2 ^ 59
def prefixEnd_3224429 : Nat := 4983230072969 + 3 ^ 40 * 3224429 * 2
def baseEnd_3224429 : Nat := 1655681913296270140408627

theorem tailTrace_3224429 : CollatzResearch.WordTrace tailWord_3224429 prefixEnd_3224429 1655681913296270140408627 := by
  unfold tailWord_3224429
  simp only [CollatzResearch.WordTrace]
  refine ⟨117604587235451896475748341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78403058156967930983832227 117604587235451896475748341)
  ·
    refine ⟨11025430053323615294601407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117604587235451896475748341 11025430053323615294601407)
    ·
      refine ⟨16538145079985422941902111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11025430053323615294601407 16538145079985422941902111)
      ·
        refine ⟨24807217619978134412853167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16538145079985422941902111 24807217619978134412853167)
        ·
          refine ⟨37210826429967201619279751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24807217619978134412853167 37210826429967201619279751)
          ·
            refine ⟨55816239644950802428919627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37210826429967201619279751 55816239644950802428919627)
            ·
              refine ⟨83724359467426203643379441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55816239644950802428919627 83724359467426203643379441)
              ·
                refine ⟨62793269600569652732534581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83724359467426203643379441 62793269600569652732534581)
                ·
                  refine ⟨5886869025053404943675117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62793269600569652732534581 5886869025053404943675117)
                  ·
                    refine ⟨2207575884395026853878169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5886869025053404943675117 2207575884395026853878169)
                    ·
                      refine ⟨1655681913296270140408627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207575884395026853878169 1655681913296270140408627)
                      ·
                        rfl

theorem cell23_3224429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_3224429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224429 prefixEnd_3224429 := by exact prefixLift 3224429
  have htrace : WordTrace (prefixWord ++ tailWord_3224429) baseStart_3224429 baseEnd_3224429 := by
    simpa [prefixWord, tailWord_3224429, baseEnd_3224429] using wordTrace_append hprefix tailTrace_3224429
  have hstable : (prefixWord ++ tailWord_3224429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224429).length < 2 ^ (prefixWord ++ tailWord_3224429).sum := by decide
  have hdescent : baseEnd_3224429 < baseStart_3224429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224435 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 4, 6]
def baseStart_3224435 : Nat := 118140960795 + 3224435 * 2 ^ 59
def prefixEnd_3224435 : Nat := 4983230072969 + 3 ^ 40 * 3224435 * 2
def baseEnd_3224435 : Nat := 551894998060065705644533

theorem tailTrace_3224435 : CollatzResearch.WordTrace tailWord_3224435 prefixEnd_3224435 551894998060065705644533 := by
  unfold tailWord_3224435
  simp only [CollatzResearch.WordTrace]
  refine ⟨117604806073430159500466759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78403204048953439666977839 117604806073430159500466759)
  ·
    refine ⟨176407209110145239250700139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117604806073430159500466759 176407209110145239250700139)
    ·
      refine ⟨264610813665217858876050209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176407209110145239250700139 264610813665217858876050209)
      ·
        refine ⟨198458110248913394157037657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264610813665217858876050209 198458110248913394157037657)
        ·
          refine ⟨148843582686685045617778243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198458110248913394157037657 148843582686685045617778243)
          ·
            refine ⟨223265374030027568426667365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148843582686685045617778243 223265374030027568426667365)
            ·
              refine ⟨41862257630630169080000131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223265374030027568426667365 41862257630630169080000131)
              ·
                refine ⟨62793386445945253620000197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41862257630630169080000131 62793386445945253620000197)
                ·
                  refine ⟨11773759958614735053750037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62793386445945253620000197 11773759958614735053750037)
                  ·
                    refine ⟨551894998060065705644533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11773759958614735053750037 551894998060065705644533)
                    ·
                      rfl

theorem cell23_3224435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_3224435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224435 prefixEnd_3224435 := by exact prefixLift 3224435
  have htrace : WordTrace (prefixWord ++ tailWord_3224435) baseStart_3224435 baseEnd_3224435 := by
    simpa [prefixWord, tailWord_3224435, baseEnd_3224435] using wordTrace_append hprefix tailTrace_3224435
  have hstable : (prefixWord ++ tailWord_3224435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224435).length < 2 ^ (prefixWord ++ tailWord_3224435).sum := by decide
  have hdescent : baseEnd_3224435 < baseStart_3224435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224453 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_3224453 : Nat := 118140960795 + 3224453 * 2 ^ 59
def prefixEnd_3224453 : Nat := 4983230072969 + 3 ^ 40 * 3224453 * 2
def baseEnd_3224453 : Nat := 1655694236831978046508517

theorem tailTrace_3224453 : CollatzResearch.WordTrace tailWord_3224453 prefixEnd_3224453 1655694236831978046508517 := by
  unfold tailWord_3224453
  simp only [CollatzResearch.WordTrace]
  refine ⟨117605462587364948574622013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78403641724909965716414675 117605462587364948574622013)
  ·
    refine ⟨44102048470261855715483255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117605462587364948574622013 44102048470261855715483255)
    ·
      refine ⟨66153072705392783573224883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44102048470261855715483255 66153072705392783573224883)
      ·
        refine ⟨99229609058089175359837325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66153072705392783573224883 99229609058089175359837325)
        ·
          refine ⟨37211103396783440759938997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99229609058089175359837325 37211103396783440759938997)
          ·
            refine ⟨3488540943448447571244281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37211103396783440759938997 3488540943448447571244281)
            ·
              refine ⟨2616405707586335678433211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3488540943448447571244281 2616405707586335678433211)
              ·
                refine ⟨3924608561379503517649817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616405707586335678433211 3924608561379503517649817)
                ·
                  refine ⟨2943456421034627638237363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924608561379503517649817 2943456421034627638237363)
                  ·
                    refine ⟨4415184631551941457356045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943456421034627638237363 4415184631551941457356045)
                    ·
                      refine ⟨1655694236831978046508517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4415184631551941457356045 1655694236831978046508517)
                      ·
                        rfl

theorem cell23_3224453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_3224453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224453 prefixEnd_3224453 := by exact prefixLift 3224453
  have htrace : WordTrace (prefixWord ++ tailWord_3224453) baseStart_3224453 baseEnd_3224453 := by
    simpa [prefixWord, tailWord_3224453, baseEnd_3224453] using wordTrace_append hprefix tailTrace_3224453
  have hstable : (prefixWord ++ tailWord_3224453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224453).length < 2 ^ (prefixWord ++ tailWord_3224453).sum := by decide
  have hdescent : baseEnd_3224453 < baseStart_3224453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224465 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 9]
def baseStart_3224465 : Nat := 118140960795 + 3224465 * 2 ^ 59
def prefixEnd_3224465 : Nat := 4983230072969 + 3 ^ 40 * 3224465 * 2
def baseEnd_3224465 : Nat := 183966710955536888839829

theorem tailTrace_3224465 : CollatzResearch.WordTrace tailWord_3224465 prefixEnd_3224465 183966710955536888839829 := by
  unfold tailWord_3224465
  simp only [CollatzResearch.WordTrace]
  refine ⟨117605900263321474624058849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78403933508880983082705899 117605900263321474624058849)
  ·
    refine ⟨88204425197491105968044137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117605900263321474624058849 88204425197491105968044137)
    ·
      refine ⟨66153318898118329476033103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88204425197491105968044137 66153318898118329476033103)
      ·
        refine ⟨99229978347177494214049655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66153318898118329476033103 99229978347177494214049655)
        ·
          refine ⟨148844967520766241321074483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99229978347177494214049655 148844967520766241321074483)
          ·
            refine ⟨223267451281149361981611725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148844967520766241321074483 223267451281149361981611725)
            ·
              refine ⟨83725294230431010743104397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223267451281149361981611725 83725294230431010743104397)
              ·
                refine ⟨31396985336411629028664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83725294230431010743104397 31396985336411629028664149)
                ·
                  refine ⟨183966710955536888839829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31396985336411629028664149 183966710955536888839829)
                  ·
                    rfl

theorem cell23_3224465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_3224465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224465 prefixEnd_3224465 := by exact prefixLift 3224465
  have htrace : WordTrace (prefixWord ++ tailWord_3224465) baseStart_3224465 baseEnd_3224465 := by
    simpa [prefixWord, tailWord_3224465, baseEnd_3224465] using wordTrace_append hprefix tailTrace_3224465
  have hstable : (prefixWord ++ tailWord_3224465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224465).length < 2 ^ (prefixWord ++ tailWord_3224465).sum := by decide
  have hdescent : baseEnd_3224465 < baseStart_3224465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224492 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_3224492 : Nat := 118140960795 + 3224492 * 2 ^ 59
def prefixEnd_3224492 : Nat := 4983230072969 + 3 ^ 40 * 3224492 * 2
def baseEnd_3224492 : Nat := 1655714262577503393920837

theorem tailTrace_3224492 : CollatzResearch.WordTrace tailWord_3224492 prefixEnd_3224492 1655714262577503393920837 := by
  unfold tailWord_3224492
  simp only [CollatzResearch.WordTrace]
  refine ⟨58803442517111829117645865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78404590022815772156861153 58803442517111829117645865)
  ·
    refine ⟨44102581887833871838234399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58803442517111829117645865 44102581887833871838234399)
    ·
      refine ⟨66153872831750807757351599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44102581887833871838234399 66153872831750807757351599)
      ·
        refine ⟨99230809247626211636027399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66153872831750807757351599 99230809247626211636027399)
        ·
          refine ⟨148846213871439317454041099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99230809247626211636027399 148846213871439317454041099)
          ·
            refine ⟨223269320807158976181061649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148846213871439317454041099 223269320807158976181061649)
            ·
              refine ⟨167451990605369232135796237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223269320807158976181061649 167451990605369232135796237)
              ·
                refine ⟨62794496477013462050923589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167451990605369232135796237 62794496477013462050923589)
                ·
                  refine ⟨11773968089440024134548173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62794496477013462050923589 11773968089440024134548173)
                  ·
                    refine ⟨4415238033540009050455565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11773968089440024134548173 4415238033540009050455565)
                    ·
                      refine ⟨1655714262577503393920837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4415238033540009050455565 1655714262577503393920837)
                      ·
                        rfl

theorem cell23_3224492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_3224492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224492 prefixEnd_3224492 := by exact prefixLift 3224492
  have htrace : WordTrace (prefixWord ++ tailWord_3224492) baseStart_3224492 baseEnd_3224492 := by
    simpa [prefixWord, tailWord_3224492, baseEnd_3224492] using wordTrace_append hprefix tailTrace_3224492
  have hstable : (prefixWord ++ tailWord_3224492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224492).length < 2 ^ (prefixWord ++ tailWord_3224492).sum := by decide
  have hdescent : baseEnd_3224492 < baseStart_3224492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224516 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 7]
def baseStart_3224516 : Nat := 118140960795 + 3224516 * 2 ^ 59
def prefixEnd_3224516 : Nat := 4983230072969 + 3 ^ 40 * 3224516 * 2
def baseEnd_3224516 : Nat := 183969620679245700002303

theorem tailTrace_3224516 : CollatzResearch.WordTrace tailWord_3224516 prefixEnd_3224516 183969620679245700002303 := by
  unfold tailWord_3224516
  simp only [CollatzResearch.WordTrace]
  refine ⟨58803880193068355167082701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78405173590757806889443601 58803880193068355167082701)
  ·
    refine ⟨22051455072400633187656013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58803880193068355167082701 22051455072400633187656013)
    ·
      refine ⟨8269295652150237445371005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22051455072400633187656013 8269295652150237445371005)
      ·
        refine ⟨3100985869556339042014127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8269295652150237445371005 3100985869556339042014127)
        ·
          refine ⟨4651478804334508563021191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100985869556339042014127 4651478804334508563021191)
          ·
            refine ⟨6977218206501762844531787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4651478804334508563021191 6977218206501762844531787)
            ·
              refine ⟨10465827309752644266797681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6977218206501762844531787 10465827309752644266797681)
              ·
                refine ⟨7849370482314483200098261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465827309752644266797681 7849370482314483200098261)
                ·
                  refine ⟨183969620679245700002303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7849370482314483200098261 183969620679245700002303)
                  ·
                    rfl

theorem cell23_3224516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_3224516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224516 prefixEnd_3224516 := by exact prefixLift 3224516
  have htrace : WordTrace (prefixWord ++ tailWord_3224516) baseStart_3224516 baseEnd_3224516 := by
    simpa [prefixWord, tailWord_3224516, baseEnd_3224516] using wordTrace_append hprefix tailTrace_3224516
  have hstable : (prefixWord ++ tailWord_3224516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224516).length < 2 ^ (prefixWord ++ tailWord_3224516).sum := by decide
  have hdescent : baseEnd_3224516 < baseStart_3224516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224552 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3224552 : Nat := 118140960795 + 3224552 * 2 ^ 59
def prefixEnd_3224552 : Nat := 4983230072969 + 3 ^ 40 * 3224552 * 2
def baseEnd_3224552 : Nat := 1655745071416773159170561

theorem tailTrace_3224552 : CollatzResearch.WordTrace tailWord_3224552 prefixEnd_3224552 1655745071416773159170561 := by
  unfold tailWord_3224552
  simp only [CollatzResearch.WordTrace]
  refine ⟨58804536707003144241237955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78406048942670858988317273 58804536707003144241237955)
  ·
    refine ⟨88206805060504716361856933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58804536707003144241237955 88206805060504716361856933)
    ·
      refine ⟨16538775948844634317848175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88206805060504716361856933 16538775948844634317848175)
      ·
        refine ⟨24808163923266951476772263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16538775948844634317848175 24808163923266951476772263)
        ·
          refine ⟨37212245884900427215158395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24808163923266951476772263 37212245884900427215158395)
          ·
            refine ⟨55818368827350640822737593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37212245884900427215158395 55818368827350640822737593)
            ·
              refine ⟨41863776620512980617053195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55818368827350640822737593 41863776620512980617053195)
              ·
                refine ⟨62795664930769470925579793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41863776620512980617053195 62795664930769470925579793)
                ·
                  refine ⟨47096748698077103194184845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62795664930769470925579793 47096748698077103194184845)
                  ·
                    refine ⟨17661280761778913697819317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47096748698077103194184845 17661280761778913697819317)
                    ·
                      refine ⟨1655745071416773159170561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17661280761778913697819317 1655745071416773159170561)
                      ·
                        rfl

theorem cell23_3224552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3224552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224552 prefixEnd_3224552 := by exact prefixLift 3224552
  have htrace : WordTrace (prefixWord ++ tailWord_3224552) baseStart_3224552 baseEnd_3224552 := by
    simpa [prefixWord, tailWord_3224552, baseEnd_3224552] using wordTrace_append hprefix tailTrace_3224552
  have hstable : (prefixWord ++ tailWord_3224552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224552).length < 2 ^ (prefixWord ++ tailWord_3224552).sum := by decide
  have hdescent : baseEnd_3224552 < baseStart_3224552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224559 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 3, 4]
def baseStart_3224559 : Nat := 118140960795 + 3224559 * 2 ^ 59
def prefixEnd_3224559 : Nat := 4983230072969 + 3 ^ 40 * 3224559 * 2
def baseEnd_3224559 : Nat := 551916221927118210594343

theorem tailTrace_3224559 : CollatzResearch.WordTrace tailWord_3224559 prefixEnd_3224559 551916221927118210594343 := by
  unfold tailWord_3224559
  simp only [CollatzResearch.WordTrace]
  refine ⟨117609328724980928677980731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78406219149987285785320487 117609328724980928677980731)
  ·
    refine ⟨176413993087471393016971097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117609328724980928677980731 176413993087471393016971097)
    ·
      refine ⟨132310494815603544762728323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176413993087471393016971097 132310494815603544762728323)
      ·
        refine ⟨198465742223405317144092485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132310494815603544762728323 198465742223405317144092485)
        ·
          refine ⟨37212326666888496964517341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198465742223405317144092485 37212326666888496964517341)
          ·
            refine ⟨13954622500083186361694003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37212326666888496964517341 13954622500083186361694003)
            ·
              refine ⟨20931933750124779542541005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13954622500083186361694003 20931933750124779542541005)
              ·
                refine ⟨7849475156296792328452877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20931933750124779542541005 7849475156296792328452877)
                ·
                  refine ⟨2943553183611297123169829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7849475156296792328452877 2943553183611297123169829)
                  ·
                    refine ⟨551916221927118210594343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943553183611297123169829 551916221927118210594343)
                    ·
                      rfl

theorem cell23_3224559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_3224559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224559 prefixEnd_3224559 := by exact prefixLift 3224559
  have htrace : WordTrace (prefixWord ++ tailWord_3224559) baseStart_3224559 baseEnd_3224559 := by
    simpa [prefixWord, tailWord_3224559, baseEnd_3224559] using wordTrace_append hprefix tailTrace_3224559
  have hstable : (prefixWord ++ tailWord_3224559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224559).length < 2 ^ (prefixWord ++ tailWord_3224559).sum := by decide
  have hdescent : baseEnd_3224559 < baseStart_3224559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224610 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3224610 : Nat := 118140960795 + 3224610 * 2 ^ 59
def prefixEnd_3224610 : Nat := 4983230072969 + 3 ^ 40 * 3224610 * 2
def baseEnd_3224610 : Nat := 551924951098244644081765

theorem tailTrace_3224610 : CollatzResearch.WordTrace tailWord_3224610 prefixEnd_3224610 551924951098244644081765 := by
  unfold tailWord_3224610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29402797211949041097021821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78407459231864109592058189 29402797211949041097021821)
  ·
    refine ⟨11026048954480890411383183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29402797211949041097021821 11026048954480890411383183)
    ·
      refine ⟨16539073431721335617074775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026048954480890411383183 16539073431721335617074775)
      ·
        refine ⟨24808610147582003425612163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16539073431721335617074775 24808610147582003425612163)
        ·
          refine ⟨37212915221373005138418245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24808610147582003425612163 37212915221373005138418245)
          ·
            refine ⟨6977421604007438463453421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37212915221373005138418245 6977421604007438463453421)
            ·
              refine ⟨2616533101502789423795033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6977421604007438463453421 2616533101502789423795033)
              ·
                refine ⟨1962399826127092067846275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616533101502789423795033 1962399826127092067846275)
                ·
                  refine ⟨2943599739190638101769413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962399826127092067846275 2943599739190638101769413)
                  ·
                    refine ⟨551924951098244644081765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943599739190638101769413 551924951098244644081765)
                    ·
                      rfl

theorem cell23_3224610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3224610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224610 prefixEnd_3224610 := by exact prefixLift 3224610
  have htrace : WordTrace (prefixWord ++ tailWord_3224610) baseStart_3224610 baseEnd_3224610 := by
    simpa [prefixWord, tailWord_3224610, baseEnd_3224610] using wordTrace_append hprefix tailTrace_3224610
  have hstable : (prefixWord ++ tailWord_3224610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224610).length < 2 ^ (prefixWord ++ tailWord_3224610).sum := by decide
  have hdescent : baseEnd_3224610 < baseStart_3224610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224626 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_3224626 : Nat := 118140960795 + 3224626 * 2 ^ 59
def prefixEnd_3224626 : Nat := 4983230072969 + 3 ^ 40 * 3224626 * 2
def baseEnd_3224626 : Nat := 1655783068985205869645221

theorem tailTrace_3224626 : CollatzResearch.WordTrace tailWord_3224626 prefixEnd_3224626 1655783068985205869645221 := by
  unfold tailWord_3224626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29402943103934549780167433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78407848277158799413779821 29402943103934549780167433)
  ·
    refine ⟨22052207327950912335125575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29402943103934549780167433 22052207327950912335125575)
    ·
      refine ⟨33078310991926368502688363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22052207327950912335125575 33078310991926368502688363)
      ·
        refine ⟨49617466487889552754032545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33078310991926368502688363 49617466487889552754032545)
        ·
          refine ⟨37213099865917164565524409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49617466487889552754032545 37213099865917164565524409)
          ·
            refine ⟨27909824899437873424143307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37213099865917164565524409 27909824899437873424143307)
            ·
              refine ⟨41864737349156810136214961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27909824899437873424143307 41864737349156810136214961)
              ·
                refine ⟨31398553011867607602161221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41864737349156810136214961 31398553011867607602161221)
                ·
                  refine ⟨5887228689725176425405229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31398553011867607602161221 5887228689725176425405229)
                  ·
                    refine ⟨2207710758646941159526961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5887228689725176425405229 2207710758646941159526961)
                    ·
                      refine ⟨1655783068985205869645221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207710758646941159526961 1655783068985205869645221)
                      ·
                        rfl

theorem cell23_3224626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_3224626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224626 prefixEnd_3224626 := by exact prefixLift 3224626
  have htrace : WordTrace (prefixWord ++ tailWord_3224626) baseStart_3224626 baseEnd_3224626 := by
    simpa [prefixWord, tailWord_3224626, baseEnd_3224626] using wordTrace_append hprefix tailTrace_3224626
  have hstable : (prefixWord ++ tailWord_3224626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224626).length < 2 ^ (prefixWord ++ tailWord_3224626).sum := by decide
  have hdescent : baseEnd_3224626 < baseStart_3224626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224636 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_3224636 : Nat := 118140960795 + 3224636 * 2 ^ 59
def prefixEnd_3224636 : Nat := 4983230072969 + 3 ^ 40 * 3224636 * 2
def baseEnd_3224636 : Nat := 551929401263916943506725

theorem tailTrace_3224636 : CollatzResearch.WordTrace tailWord_3224636 prefixEnd_3224636 551929401263916943506725 := by
  unfold tailWord_3224636
  simp only [CollatzResearch.WordTrace]
  refine ⟨58806068572850985414266881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78408091430467980552355841 58806068572850985414266881)
  ·
    refine ⟨44104551429638239060700161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58806068572850985414266881 44104551429638239060700161)
    ·
      refine ⟨33078413572228679295525121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44104551429638239060700161 33078413572228679295525121)
      ·
        refine ⟨24808810179171509471643841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33078413572228679295525121 24808810179171509471643841)
        ·
          refine ⟨18606607634378632103732881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24808810179171509471643841 18606607634378632103732881)
          ·
            refine ⟨13954955725783974077799661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18606607634378632103732881 13954955725783974077799661)
            ·
              refine ⟨5233108397168990279174873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13954955725783974077799661 5233108397168990279174873)
              ·
                refine ⟨3924831297876742709381155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233108397168990279174873 3924831297876742709381155)
                ·
                  refine ⟨5887246946815114064071733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924831297876742709381155 5887246946815114064071733)
                  ·
                    refine ⟨551929401263916943506725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5887246946815114064071733 551929401263916943506725)
                    ·
                      rfl

theorem cell23_3224636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_3224636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224636 prefixEnd_3224636 := by exact prefixLift 3224636
  have htrace : WordTrace (prefixWord ++ tailWord_3224636) baseStart_3224636 baseEnd_3224636 := by
    simpa [prefixWord, tailWord_3224636, baseEnd_3224636] using wordTrace_append hprefix tailTrace_3224636
  have hstable : (prefixWord ++ tailWord_3224636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224636).length < 2 ^ (prefixWord ++ tailWord_3224636).sum := by decide
  have hdescent : baseEnd_3224636 < baseStart_3224636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224649 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_3224649 : Nat := 118140960795 + 3224649 * 2 ^ 59
def prefixEnd_3224649 : Nat := 4983230072969 + 3 ^ 40 * 3224649 * 2
def baseEnd_3224649 : Nat := 551931626346753093219205

theorem tailTrace_3224649 : CollatzResearch.WordTrace tailWord_3224649 prefixEnd_3224649 551931626346753093219205 := by
  unfold tailWord_3224649
  simp only [CollatzResearch.WordTrace]
  refine ⟨117612611294654874048757001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78408407529769916032504667 117612611294654874048757001)
  ·
    refine ⟨88209458470991155536567751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117612611294654874048757001 88209458470991155536567751)
    ·
      refine ⟨132314187706486733304851627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88209458470991155536567751 132314187706486733304851627)
      ·
        refine ⟨198471281559730099957277441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132314187706486733304851627 198471281559730099957277441)
        ·
          refine ⟨148853461169797574967958081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198471281559730099957277441 148853461169797574967958081)
          ·
            refine ⟨111640095877348181225968561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148853461169797574967958081 111640095877348181225968561)
            ·
              refine ⟨83730071908011135919476421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111640095877348181225968561 83730071908011135919476421)
              ·
                refine ⟨15699388482752087984901829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83730071908011135919476421 15699388482752087984901829)
                ·
                  refine ⟨2943635340516016497169093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15699388482752087984901829 2943635340516016497169093)
                  ·
                    refine ⟨551931626346753093219205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943635340516016497169093 551931626346753093219205)
                    ·
                      rfl

theorem cell23_3224649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_3224649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224649 prefixEnd_3224649 := by exact prefixLift 3224649
  have htrace : WordTrace (prefixWord ++ tailWord_3224649) baseStart_3224649 baseEnd_3224649 := by
    simpa [prefixWord, tailWord_3224649, baseEnd_3224649] using wordTrace_append hprefix tailTrace_3224649
  have hstable : (prefixWord ++ tailWord_3224649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224649).length < 2 ^ (prefixWord ++ tailWord_3224649).sum := by decide
  have hdescent : baseEnd_3224649 < baseStart_3224649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224659 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3]
def baseStart_3224659 : Nat := 118140960795 + 3224659 * 2 ^ 59
def prefixEnd_3224659 : Nat := 4983230072969 + 3 ^ 40 * 3224659 * 2
def baseEnd_3224659 : Nat := 1655800013846804240532569

theorem tailTrace_3224659 : CollatzResearch.WordTrace tailWord_3224659 prefixEnd_3224659 1655800013846804240532569 := by
  unfold tailWord_3224659
  simp only [CollatzResearch.WordTrace]
  refine ⟨117612976024618645756621031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78408650683079097171080687 117612976024618645756621031)
  ·
    refine ⟨176419464036927968634931547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117612976024618645756621031 176419464036927968634931547)
    ·
      refine ⟨264629196055391952952397321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176419464036927968634931547 264629196055391952952397321)
      ·
        refine ⟨198471897041543964714297991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264629196055391952952397321 198471897041543964714297991)
        ·
          refine ⟨297707845562315947071446987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198471897041543964714297991 297707845562315947071446987)
          ·
            refine ⟨446561768343473920607170481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297707845562315947071446987 446561768343473920607170481)
            ·
              refine ⟨334921326257605440455377861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446561768343473920607170481 334921326257605440455377861)
              ·
                refine ⟨62797748673301020085383349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334921326257605440455377861 62797748673301020085383349)
                ·
                  refine ⟨5887288938121970633004689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62797748673301020085383349 5887288938121970633004689)
                  ·
                    refine ⟨4415466703591477974753517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887288938121970633004689 4415466703591477974753517)
                    ·
                      refine ⟨1655800013846804240532569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4415466703591477974753517 1655800013846804240532569)
                      ·
                        rfl

theorem cell23_3224659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_3224659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224659 prefixEnd_3224659 := by exact prefixLift 3224659
  have htrace : WordTrace (prefixWord ++ tailWord_3224659) baseStart_3224659 baseEnd_3224659 := by
    simpa [prefixWord, tailWord_3224659, baseEnd_3224659] using wordTrace_append hprefix tailTrace_3224659
  have hstable : (prefixWord ++ tailWord_3224659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224659).length < 2 ^ (prefixWord ++ tailWord_3224659).sum := by decide
  have hdescent : baseEnd_3224659 < baseStart_3224659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224679 : List Nat := [1, 1, 5, 1, 1, 3, 3, 8]
def baseStart_3224679 : Nat := 118140960795 + 3224679 * 2 ^ 59
def prefixEnd_3224679 : Nat := 4983230072969 + 3 ^ 40 * 3224679 * 2
def baseEnd_3224679 : Nat := 61326306794810894899351

theorem tailTrace_3224679 : CollatzResearch.WordTrace tailWord_3224679 prefixEnd_3224679 61326306794810894899351 := by
  unfold tailWord_3224679
  simp only [CollatzResearch.WordTrace]
  refine ⟨117613705484546189172349091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78409136989697459448232727 117613705484546189172349091)
  ·
    refine ⟨176420558226819283758523637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117613705484546189172349091 176420558226819283758523637)
    ·
      refine ⟨16539427333764307852361591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176420558226819283758523637 16539427333764307852361591)
      ·
        refine ⟨24809141000646461778542387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16539427333764307852361591 24809141000646461778542387)
        ·
          refine ⟨37213711500969692667813581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24809141000646461778542387 37213711500969692667813581)
          ·
            refine ⟨13955141812863634750430093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37213711500969692667813581 13955141812863634750430093)
            ·
              refine ⟨5233178179823863031411285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13955141812863634750430093 5233178179823863031411285)
              ·
                refine ⟨61326306794810894899351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5233178179823863031411285 61326306794810894899351)
                ·
                  rfl

theorem cell23_3224679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 8].length) (baseStart_3224679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224679 prefixEnd_3224679 := by exact prefixLift 3224679
  have htrace : WordTrace (prefixWord ++ tailWord_3224679) baseStart_3224679 baseEnd_3224679 := by
    simpa [prefixWord, tailWord_3224679, baseEnd_3224679] using wordTrace_append hprefix tailTrace_3224679
  have hstable : (prefixWord ++ tailWord_3224679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224679).length < 2 ^ (prefixWord ++ tailWord_3224679).sum := by decide
  have hdescent : baseEnd_3224679 < baseStart_3224679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224686 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3224686 : Nat := 118140960795 + 3224686 * 2 ^ 59
def prefixEnd_3224686 : Nat := 4983230072969 + 3 ^ 40 * 3224686 * 2
def baseEnd_3224686 : Nat := 1655813877824475634894945

theorem tailTrace_3224686 : CollatzResearch.WordTrace tailWord_3224686 prefixEnd_3224686 1655813877824475634894945 := by
  unfold tailWord_3224686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701745099440103670981739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78409307197013886245235941 14701745099440103670981739)
  ·
    refine ⟨22052617649160155506472609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14701745099440103670981739 22052617649160155506472609)
    ·
      refine ⟨16539463236870116629854457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22052617649160155506472609 16539463236870116629854457)
      ·
        refine ⟨12404597427652587472390843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16539463236870116629854457 12404597427652587472390843)
        ·
          refine ⟨18606896141478881208586265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12404597427652587472390843 18606896141478881208586265)
          ·
            refine ⟨13955172106109160906439699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18606896141478881208586265 13955172106109160906439699)
            ·
              refine ⟨20932758159163741359659549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13955172106109160906439699 20932758159163741359659549)
              ·
                refine ⟨7849784309686403009872331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20932758159163741359659549 7849784309686403009872331)
                ·
                  refine ⟨11774676464529604514808497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7849784309686403009872331 11774676464529604514808497)
                  ·
                    refine ⟨8831007348397203386106373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11774676464529604514808497 8831007348397203386106373)
                    ·
                      refine ⟨1655813877824475634894945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8831007348397203386106373 1655813877824475634894945)
                      ·
                        rfl

theorem cell23_3224686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3224686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224686 prefixEnd_3224686 := by exact prefixLift 3224686
  have htrace : WordTrace (prefixWord ++ tailWord_3224686) baseStart_3224686 baseEnd_3224686 := by
    simpa [prefixWord, tailWord_3224686, baseEnd_3224686] using wordTrace_append hprefix tailTrace_3224686
  have hstable : (prefixWord ++ tailWord_3224686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224686).length < 2 ^ (prefixWord ++ tailWord_3224686).sum := by decide
  have hdescent : baseEnd_3224686 < baseStart_3224686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224723 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 3]
def baseStart_3224723 : Nat := 118140960795 + 3224723 * 2 ^ 59
def prefixEnd_3224723 : Nat := 4983230072969 + 3 ^ 40 * 3224723 * 2
def baseEnd_3224723 : Nat := 1655832876608691990132275

theorem tailTrace_3224723 : CollatzResearch.WordTrace tailWord_3224723 prefixEnd_3224723 1655832876608691990132275 := by
  unfold tailWord_3224723
  simp only [CollatzResearch.WordTrace]
  refine ⟨117615310296386784686950823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78410206864257856457967215 117615310296386784686950823)
  ·
    refine ⟨176422965444580177030426235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117615310296386784686950823 176422965444580177030426235)
    ·
      refine ⟨264634448166870265545639353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176422965444580177030426235 264634448166870265545639353)
      ·
        refine ⟨198475836125152699159229515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264634448166870265545639353 198475836125152699159229515)
        ·
          refine ⟨297713754187729048738844273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198475836125152699159229515 297713754187729048738844273)
          ·
            refine ⟨223285315640796786554133205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297713754187729048738844273 223285315640796786554133205)
            ·
              refine ⟨5233249585331174684862497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223285315640796786554133205 5233249585331174684862497)
              ·
                refine ⟨3924937188998381013646873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233249585331174684862497 3924937188998381013646873)
                ·
                  refine ⟨2943702891748785760235155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924937188998381013646873 2943702891748785760235155)
                  ·
                    refine ⟨4415554337623178640352733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943702891748785760235155 4415554337623178640352733)
                    ·
                      refine ⟨1655832876608691990132275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4415554337623178640352733 1655832876608691990132275)
                      ·
                        rfl

theorem cell23_3224723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_3224723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224723 prefixEnd_3224723 := by exact prefixLift 3224723
  have htrace : WordTrace (prefixWord ++ tailWord_3224723) baseStart_3224723 baseEnd_3224723 := by
    simpa [prefixWord, tailWord_3224723, baseEnd_3224723] using wordTrace_append hprefix tailTrace_3224723
  have hstable : (prefixWord ++ tailWord_3224723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224723).length < 2 ^ (prefixWord ++ tailWord_3224723).sum := by decide
  have hdescent : baseEnd_3224723 < baseStart_3224723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224758 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3224758 : Nat := 118140960795 + 3224758 * 2 ^ 59
def prefixEnd_3224758 : Nat := 4983230072969 + 3 ^ 40 * 3224758 * 2
def baseEnd_3224758 : Nat := 1655850848431599353194615

theorem tailTrace_3224758 : CollatzResearch.WordTrace tailWord_3224758 prefixEnd_3224758 1655850848431599353194615 := by
  unfold tailWord_3224758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351036678203749104029683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78411057900839990442983285 7351036678203749104029683)
  ·
    refine ⟨11026555017305623656044525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351036678203749104029683 11026555017305623656044525)
    ·
      refine ⟨4134958131489608871016697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11026555017305623656044525 4134958131489608871016697)
      ·
        refine ⟨3101218598617206653262523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4134958131489608871016697 3101218598617206653262523)
        ·
          refine ⟨4651827897925809979893785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101218598617206653262523 4651827897925809979893785)
          ·
            refine ⟨3488870923444357484920339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651827897925809979893785 3488870923444357484920339)
            ·
              refine ⟨5233306385166536227380509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488870923444357484920339 5233306385166536227380509)
              ·
                refine ⟨1962489894437451085267691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5233306385166536227380509 1962489894437451085267691)
                ·
                  refine ⟨2943734841656176627901537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962489894437451085267691 2943734841656176627901537)
                  ·
                    refine ⟨2207801131242132470926153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2943734841656176627901537 2207801131242132470926153)
                    ·
                      refine ⟨1655850848431599353194615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207801131242132470926153 1655850848431599353194615)
                      ·
                        rfl

theorem cell23_3224758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3224758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224758 prefixEnd_3224758 := by exact prefixLift 3224758
  have htrace : WordTrace (prefixWord ++ tailWord_3224758) baseStart_3224758 baseEnd_3224758 := by
    simpa [prefixWord, tailWord_3224758, baseEnd_3224758] using wordTrace_append hprefix tailTrace_3224758
  have hstable : (prefixWord ++ tailWord_3224758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224758).length < 2 ^ (prefixWord ++ tailWord_3224758).sum := by decide
  have hdescent : baseEnd_3224758 < baseStart_3224758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224766 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3224766 : Nat := 118140960795 + 3224766 * 2 ^ 59
def prefixEnd_3224766 : Nat := 4983230072969 + 3 ^ 40 * 3224766 * 2
def baseEnd_3224766 : Nat := 1655854956276835321894577

theorem tailTrace_3224766 : CollatzResearch.WordTrace tailWord_3224766 prefixEnd_3224766 1655854956276835321894577 := by
  unfold tailWord_3224766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702109829403875378845769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78411252423487335353844101 14702109829403875378845769)
  ·
    refine ⟨11026582372052906534134327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14702109829403875378845769 11026582372052906534134327)
    ·
      refine ⟨16539873558079359801201491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026582372052906534134327 16539873558079359801201491)
      ·
        refine ⟨24809810337119039701802237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16539873558079359801201491 24809810337119039701802237)
        ·
          refine ⟨9303678876419639888175839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24809810337119039701802237 9303678876419639888175839)
          ·
            refine ⟨13955518314629459832263759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303678876419639888175839 13955518314629459832263759)
            ·
              refine ⟨20933277471944189748395639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13955518314629459832263759 20933277471944189748395639)
              ·
                refine ⟨31399916207916284622593459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20933277471944189748395639 31399916207916284622593459)
                ·
                  refine ⟨47099874311874426933890189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31399916207916284622593459 47099874311874426933890189)
                  ·
                    refine ⟨17662452866952910100208821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47099874311874426933890189 17662452866952910100208821)
                    ·
                      refine ⟨1655854956276835321894577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17662452866952910100208821 1655854956276835321894577)
                      ·
                        rfl

theorem cell23_3224766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3224766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224766 prefixEnd_3224766 := by exact prefixLift 3224766
  have htrace : WordTrace (prefixWord ++ tailWord_3224766) baseStart_3224766 baseEnd_3224766 := by
    simpa [prefixWord, tailWord_3224766, baseEnd_3224766] using wordTrace_append hprefix tailTrace_3224766
  have hstable : (prefixWord ++ tailWord_3224766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224766).length < 2 ^ (prefixWord ++ tailWord_3224766).sum := by decide
  have hdescent : baseEnd_3224766 < baseStart_3224766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224799 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 7]
def baseStart_3224799 : Nat := 118140960795 + 3224799 * 2 ^ 59
def prefixEnd_3224799 : Nat := 4983230072969 + 3 ^ 40 * 3224799 * 2
def baseEnd_3224799 : Nat := 551957300379477897593975

theorem tailTrace_3224799 : CollatzResearch.WordTrace tailWord_3224799 prefixEnd_3224799 551957300379477897593975 := by
  unfold tailWord_3224799
  simp only [CollatzResearch.WordTrace]
  refine ⟨117618082244111449666717451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78412054829407633111144967 117618082244111449666717451)
  ·
    refine ⟨176427123366167174500076177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117618082244111449666717451 176427123366167174500076177)
    ·
      refine ⟨132320342524625380875057133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176427123366167174500076177 132320342524625380875057133)
      ·
        refine ⟨49620128446734517828146425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132320342524625380875057133 49620128446734517828146425)
        ·
          refine ⟨37215096335050888371109819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49620128446734517828146425 37215096335050888371109819)
          ·
            refine ⟨55822644502576332556664729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37215096335050888371109819 55822644502576332556664729)
            ·
              refine ⟨41866983376932249417498547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55822644502576332556664729 41866983376932249417498547)
              ·
                refine ⟨62800475065398374126247821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41866983376932249417498547 62800475065398374126247821)
                ·
                  refine ⟨23550178149524390297342933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62800475065398374126247821 23550178149524390297342933)
                  ·
                    refine ⟨551957300379477897593975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23550178149524390297342933 551957300379477897593975)
                    ·
                      rfl

theorem cell23_3224799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_3224799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224799 prefixEnd_3224799 := by exact prefixLift 3224799
  have htrace : WordTrace (prefixWord ++ tailWord_3224799) baseStart_3224799 baseEnd_3224799 := by
    simpa [prefixWord, tailWord_3224799, baseEnd_3224799] using wordTrace_append hprefix tailTrace_3224799
  have hstable : (prefixWord ++ tailWord_3224799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224799).length < 2 ^ (prefixWord ++ tailWord_3224799).sum := by decide
  have hdescent : baseEnd_3224799 < baseStart_3224799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224809 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3224809 : Nat := 118140960795 + 3224809 * 2 ^ 59
def prefixEnd_3224809 : Nat := 4983230072969 + 3 ^ 40 * 3224809 * 2
def baseEnd_3224809 : Nat := 1655877035944978653656879

theorem tailTrace_3224809 : CollatzResearch.WordTrace tailWord_3224809 prefixEnd_3224809 1655877035944978653656879 := by
  unfold tailWord_3224809
  simp only [CollatzResearch.WordTrace]
  refine ⟨117618446974075221374581481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78412297982716814249720987 117618446974075221374581481)
  ·
    refine ⟨88213835230556416030936111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117618446974075221374581481 88213835230556416030936111)
    ·
      refine ⟨132320752845834624046404167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88213835230556416030936111 132320752845834624046404167)
      ·
        refine ⟨198481129268751936069606251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132320752845834624046404167 198481129268751936069606251)
        ·
          refine ⟨297721693903127904104409377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198481129268751936069606251 297721693903127904104409377)
          ·
            refine ⟨223291270427345928078307033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297721693903127904104409377 223291270427345928078307033)
            ·
              refine ⟨167468452820509446058730275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223291270427345928078307033 167468452820509446058730275)
              ·
                refine ⟨251202679230764169088095413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167468452820509446058730275 251202679230764169088095413)
                ·
                  refine ⟨23550251177884140852008945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251202679230764169088095413 23550251177884140852008945)
                  ·
                    refine ⟨17662688383413105639006709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23550251177884140852008945 17662688383413105639006709)
                    ·
                      refine ⟨1655877035944978653656879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17662688383413105639006709 1655877035944978653656879)
                      ·
                        rfl

theorem cell23_3224809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3224809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224809 prefixEnd_3224809 := by exact prefixLift 3224809
  have htrace : WordTrace (prefixWord ++ tailWord_3224809) baseStart_3224809 baseEnd_3224809 := by
    simpa [prefixWord, tailWord_3224809, baseEnd_3224809] using wordTrace_append hprefix tailTrace_3224809
  have hstable : (prefixWord ++ tailWord_3224809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224809).length < 2 ^ (prefixWord ++ tailWord_3224809).sum := by decide
  have hdescent : baseEnd_3224809 < baseStart_3224809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224859 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 10]
def baseStart_3224859 : Nat := 118140960795 + 3224859 * 2 ^ 59
def prefixEnd_3224859 : Nat := 4983230072969 + 3 ^ 40 * 3224859 * 2
def baseEnd_3224859 : Nat := 183989189997522606447961

theorem tailTrace_3224859 : CollatzResearch.WordTrace tailWord_3224859 prefixEnd_3224859 183989189997522606447961 := by
  unfold tailWord_3224859
  simp only [CollatzResearch.WordTrace]
  refine ⟨117620270623894079913901631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78413513749262719942601087 117620270623894079913901631)
  ·
    refine ⟨176430405935841119870852447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117620270623894079913901631 176430405935841119870852447)
    ·
      refine ⟨264645608903761679806278671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176430405935841119870852447 264645608903761679806278671)
      ·
        refine ⟨396968413355642519709418007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264645608903761679806278671 396968413355642519709418007)
        ·
          refine ⟨595452620033463779564127011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396968413355642519709418007 595452620033463779564127011)
          ·
            refine ⟨893178930050195669346190517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595452620033463779564127011 893178930050195669346190517)
            ·
              refine ⟨83735524692205844001205361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 893178930050195669346190517 83735524692205844001205361)
              ·
                refine ⟨62801643519154383000904021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83735524692205844001205361 62801643519154383000904021)
                ·
                  refine ⟨183989189997522606447961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 62801643519154383000904021 183989189997522606447961)
                  ·
                    rfl

theorem cell23_3224859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 10].length) (baseStart_3224859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224859 prefixEnd_3224859 := by exact prefixLift 3224859
  have htrace : WordTrace (prefixWord ++ tailWord_3224859) baseStart_3224859 baseEnd_3224859 := by
    simpa [prefixWord, tailWord_3224859, baseEnd_3224859] using wordTrace_append hprefix tailTrace_3224859
  have hstable : (prefixWord ++ tailWord_3224859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224859).length < 2 ^ (prefixWord ++ tailWord_3224859).sum := by decide
  have hdescent : baseEnd_3224859 < baseStart_3224859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224880 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 1, 4]
def baseStart_3224880 : Nat := 118140960795 + 3224880 * 2 ^ 59
def prefixEnd_3224880 : Nat := 4983230072969 + 3 ^ 40 * 3224880 * 2
def baseEnd_3224880 : Nat := 551971164357149291956351

theorem tailTrace_3224880 : CollatzResearch.WordTrace tailWord_3224880 prefixEnd_3224880 551971164357149291956351 := by
  unfold tailWord_3224880
  simp only [CollatzResearch.WordTrace]
  refine ⟨58810518278409000250208047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78414024371212000333610729 58810518278409000250208047)
  ·
    refine ⟨88215777417613500375312071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58810518278409000250208047 88215777417613500375312071)
    ·
      refine ⟨132323666126420250562968107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88215777417613500375312071 132323666126420250562968107)
      ·
        refine ⟨198485499189630375844452161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132323666126420250562968107 198485499189630375844452161)
        ·
          refine ⟨148864124392222781883339121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198485499189630375844452161 148864124392222781883339121)
          ·
            refine ⟨111648093294167086412504341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148864124392222781883339121 111648093294167086412504341)
            ·
              refine ⟨5233504373164082175586141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111648093294167086412504341 5233504373164082175586141)
              ·
                refine ⟨1962564139936530815844803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5233504373164082175586141 1962564139936530815844803)
                ·
                  refine ⟨2943846209904796223767205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962564139936530815844803 2943846209904796223767205)
                  ·
                    refine ⟨551971164357149291956351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943846209904796223767205 551971164357149291956351)
                    ·
                      rfl

theorem cell23_3224880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 4].length) (baseStart_3224880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224880 prefixEnd_3224880 := by exact prefixLift 3224880
  have htrace : WordTrace (prefixWord ++ tailWord_3224880) baseStart_3224880 baseEnd_3224880 := by
    simpa [prefixWord, tailWord_3224880, baseEnd_3224880] using wordTrace_append hprefix tailTrace_3224880
  have hstable : (prefixWord ++ tailWord_3224880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224880).length < 2 ^ (prefixWord ++ tailWord_3224880).sum := by decide
  have hdescent : baseEnd_3224880 < baseStart_3224880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224897 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3224897 : Nat := 118140960795 + 3224897 * 2 ^ 59
def prefixEnd_3224897 : Nat := 4983230072969 + 3 ^ 40 * 3224897 * 2
def baseEnd_3224897 : Nat := 551974074080858103118825

theorem tailTrace_3224897 : CollatzResearch.WordTrace tailWord_3224897 prefixEnd_3224897 551974074080858103118825 := by
  unfold tailWord_3224897
  simp only [CollatzResearch.WordTrace]
  refine ⟨117621656597756412403784945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78414437731837608269189963 117621656597756412403784945)
  ·
    refine ⟨88216242448317309302838709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117621656597756412403784945 88216242448317309302838709)
    ·
      refine ⟨8270272729529747747141129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88216242448317309302838709 8270272729529747747141129)
      ·
        refine ⟨6202704547147310810355847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8270272729529747747141129 6202704547147310810355847)
        ·
          refine ⟨9304056820720966215533771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202704547147310810355847 9304056820720966215533771)
          ·
            refine ⟨13956085231081449323300657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304056820720966215533771 13956085231081449323300657)
            ·
              refine ⟨10467063923311086992475493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13956085231081449323300657 10467063923311086992475493)
              ·
                refine ⟨1962574485620828811089155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10467063923311086992475493 1962574485620828811089155)
                ·
                  refine ⟨2943861728431243216633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962574485620828811089155 2943861728431243216633733)
                  ·
                    refine ⟨551974074080858103118825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943861728431243216633733 551974074080858103118825)
                    ·
                      rfl

theorem cell23_3224897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3224897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224897 prefixEnd_3224897 := by exact prefixLift 3224897
  have htrace : WordTrace (prefixWord ++ tailWord_3224897) baseStart_3224897 baseEnd_3224897 := by
    simpa [prefixWord, tailWord_3224897, baseEnd_3224897] using wordTrace_append hprefix tailTrace_3224897
  have hstable : (prefixWord ++ tailWord_3224897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224897).length < 2 ^ (prefixWord ++ tailWord_3224897).sum := by decide
  have hdescent : baseEnd_3224897 < baseStart_3224897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224906 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3224906 : Nat := 118140960795 + 3224906 * 2 ^ 59
def prefixEnd_3224906 : Nat := 4983230072969 + 3 ^ 40 * 3224906 * 2
def baseEnd_3224906 : Nat := 551975614522821591381311

theorem tailTrace_3224906 : CollatzResearch.WordTrace tailWord_3224906 prefixEnd_3224906 551975614522821591381311 := by
  unfold tailWord_3224906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29405496213680951735215643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78414656569815871293908381 29405496213680951735215643)
  ·
    refine ⟨44108244320521427602823465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29405496213680951735215643 44108244320521427602823465)
    ·
      refine ⟨33081183240391070702117599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44108244320521427602823465 33081183240391070702117599)
      ·
        refine ⟨49621774860586606053176399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33081183240391070702117599 49621774860586606053176399)
        ·
          refine ⟨74432662290879909079764599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49621774860586606053176399 74432662290879909079764599)
          ·
            refine ⟨111648993436319863619646899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74432662290879909079764599 111648993436319863619646899)
            ·
              refine ⟨167473490154479795429470349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111648993436319863619646899 167473490154479795429470349)
              ·
                refine ⟨62802558807929923286051381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167473490154479795429470349 62802558807929923286051381)
                ·
                  refine ⟨5887739888243430308067317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62802558807929923286051381 5887739888243430308067317)
                  ·
                    refine ⟨551975614522821591381311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5887739888243430308067317 551975614522821591381311)
                    ·
                      rfl

theorem cell23_3224906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3224906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224906 prefixEnd_3224906 := by exact prefixLift 3224906
  have htrace : WordTrace (prefixWord ++ tailWord_3224906) baseStart_3224906 baseEnd_3224906 := by
    simpa [prefixWord, tailWord_3224906, baseEnd_3224906] using wordTrace_append hprefix tailTrace_3224906
  have hstable : (prefixWord ++ tailWord_3224906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224906).length < 2 ^ (prefixWord ++ tailWord_3224906).sum := by decide
  have hdescent : baseEnd_3224906 < baseStart_3224906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224913 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_3224913 : Nat := 118140960795 + 3224913 * 2 ^ 59
def prefixEnd_3224913 : Nat := 4983230072969 + 3 ^ 40 * 3224913 * 2
def baseEnd_3224913 : Nat := 1655930437933046246756401

theorem tailTrace_3224913 : CollatzResearch.WordTrace tailWord_3224913 prefixEnd_3224913 1655930437933046246756401 := by
  unfold tailWord_3224913
  simp only [CollatzResearch.WordTrace]
  refine ⟨117622240165698447136367393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78414826777132298090911595 117622240165698447136367393)
  ·
    refine ⟨88216680124273835352275545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117622240165698447136367393 88216680124273835352275545)
    ·
      refine ⟨66162510093205376514206659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88216680124273835352275545 66162510093205376514206659)
      ·
        refine ⟨99243765139808064771309989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66162510093205376514206659 99243765139808064771309989)
        ·
          refine ⟨18608205963714012144620623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99243765139808064771309989 18608205963714012144620623)
          ·
            refine ⟨27912308945571018216930935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18608205963714012144620623 27912308945571018216930935)
            ·
              refine ⟨41868463418356527325396403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27912308945571018216930935 41868463418356527325396403)
              ·
                refine ⟨62802695127534790988094605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41868463418356527325396403 62802695127534790988094605)
                ·
                  refine ⟨23551010672825546620535477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62802695127534790988094605 23551010672825546620535477)
                  ·
                    refine ⟨2207907250577394995675201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23551010672825546620535477 2207907250577394995675201)
                    ·
                      refine ⟨1655930437933046246756401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207907250577394995675201 1655930437933046246756401)
                      ·
                        rfl

theorem cell23_3224913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_3224913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224913 prefixEnd_3224913 := by exact prefixLift 3224913
  have htrace : WordTrace (prefixWord ++ tailWord_3224913) baseStart_3224913 baseEnd_3224913 := by
    simpa [prefixWord, tailWord_3224913, baseEnd_3224913] using wordTrace_append hprefix tailTrace_3224913
  have hstable : (prefixWord ++ tailWord_3224913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224913).length < 2 ^ (prefixWord ++ tailWord_3224913).sum := by decide
  have hdescent : baseEnd_3224913 < baseStart_3224913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224930 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3224930 : Nat := 118140960795 + 3224930 * 2 ^ 59
def prefixEnd_3224930 : Nat := 4983230072969 + 3 ^ 40 * 3224930 * 2
def baseEnd_3224930 : Nat := 1655939167104172680243823

theorem tailTrace_3224930 : CollatzResearch.WordTrace tailWord_3224930 prefixEnd_3224930 1655939167104172680243823 := by
  unfold tailWord_3224930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29405715051659214759934061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78415240137757906026490829 29405715051659214759934061)
  ·
    refine ⟨11027143144372205534975273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29405715051659214759934061 11027143144372205534975273)
    ·
      refine ⟨8270357358279154151231455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11027143144372205534975273 8270357358279154151231455)
      ·
        refine ⟨12405536037418731226847183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8270357358279154151231455 12405536037418731226847183)
        ·
          refine ⟨18608304056128096840270775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12405536037418731226847183 18608304056128096840270775)
          ·
            refine ⟨27912456084192145260406163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18608304056128096840270775 27912456084192145260406163)
            ·
              refine ⟨41868684126288217890609245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27912456084192145260406163 41868684126288217890609245)
              ·
                refine ⟨15700756547358081708978467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41868684126288217890609245 15700756547358081708978467)
                ·
                  refine ⟨23551134821037122563467701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15700756547358081708978467 23551134821037122563467701)
                  ·
                    refine ⟨2207918889472230240325097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23551134821037122563467701 2207918889472230240325097)
                    ·
                      refine ⟨1655939167104172680243823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207918889472230240325097 1655939167104172680243823)
                      ·
                        rfl

theorem cell23_3224930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3224930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224930 prefixEnd_3224930 := by exact prefixLift 3224930
  have htrace : WordTrace (prefixWord ++ tailWord_3224930) baseStart_3224930 baseEnd_3224930 := by
    simpa [prefixWord, tailWord_3224930, baseEnd_3224930] using wordTrace_append hprefix tailTrace_3224930
  have hstable : (prefixWord ++ tailWord_3224930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224930).length < 2 ^ (prefixWord ++ tailWord_3224930).sum := by decide
  have hdescent : baseEnd_3224930 < baseStart_3224930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224943 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_3224943 : Nat := 118140960795 + 3224943 * 2 ^ 59
def prefixEnd_3224943 : Nat := 4983230072969 + 3 ^ 40 * 3224943 * 2
def baseEnd_3224943 : Nat := 1655945842352681129381263

theorem tailTrace_3224943 : CollatzResearch.WordTrace tailWord_3224943 prefixEnd_3224943 1655945842352681129381263 := by
  unfold tailWord_3224943
  simp only [CollatzResearch.WordTrace]
  refine ⟨117623334355589762259959483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78415556237059841506639655 117623334355589762259959483)
  ·
    refine ⟨176435001533384643389939225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117623334355589762259959483 176435001533384643389939225)
    ·
      refine ⟨132326251150038482542454419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176435001533384643389939225 132326251150038482542454419)
      ·
        refine ⟨198489376725057723813681629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132326251150038482542454419 198489376725057723813681629)
        ·
          refine ⟨74433516271896646430130611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198489376725057723813681629 74433516271896646430130611)
          ·
            refine ⟨111650274407844969645195917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74433516271896646430130611 111650274407844969645195917)
            ·
              refine ⟨41868852902941863616948469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111650274407844969645195917 41868852902941863616948469)
              ·
                refine ⟨3925204959650799714088919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41868852902941863616948469 3925204959650799714088919)
                ·
                  refine ⟨5887807439476199571133379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925204959650799714088919 5887807439476199571133379)
                  ·
                    refine ⟨8831711159214299356700069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5887807439476199571133379 8831711159214299356700069)
                    ·
                      refine ⟨1655945842352681129381263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8831711159214299356700069 1655945842352681129381263)
                      ·
                        rfl

theorem cell23_3224943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_3224943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224943 prefixEnd_3224943 := by exact prefixLift 3224943
  have htrace : WordTrace (prefixWord ++ tailWord_3224943) baseStart_3224943 baseEnd_3224943 := by
    simpa [prefixWord, tailWord_3224943, baseEnd_3224943] using wordTrace_append hprefix tailTrace_3224943
  have hstable : (prefixWord ++ tailWord_3224943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224943).length < 2 ^ (prefixWord ++ tailWord_3224943).sum := by decide
  have hdescent : baseEnd_3224943 < baseStart_3224943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224953 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_3224953 : Nat := 118140960795 + 3224953 * 2 ^ 59
def prefixEnd_3224953 : Nat := 4983230072969 + 3 ^ 40 * 3224953 * 2
def baseEnd_3224953 : Nat := 551983659053075363418739

theorem tailTrace_3224953 : CollatzResearch.WordTrace tailWord_3224953 prefixEnd_3224953 551983659053075363418739 := by
  unfold tailWord_3224953
  simp only [CollatzResearch.WordTrace]
  refine ⟨117623699085553533967823513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78415799390369022645215675 117623699085553533967823513)
  ·
    refine ⟨88217774314165150475867635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117623699085553533967823513 88217774314165150475867635)
    ·
      refine ⟨132326661471247725713801453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88217774314165150475867635 132326661471247725713801453)
      ·
        refine ⟨49622498051717897142675545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132326661471247725713801453 49622498051717897142675545)
        ·
          refine ⟨37216873538788422857006659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49622498051717897142675545 37216873538788422857006659)
          ·
            refine ⟨55825310308182634285509989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37216873538788422857006659 55825310308182634285509989)
            ·
              refine ⟨10467245682784243928533123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55825310308182634285509989 10467245682784243928533123)
              ·
                refine ⟨15700868524176365892799685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467245682784243928533123 15700868524176365892799685)
                ·
                  refine ⟨2943912848283068604899941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15700868524176365892799685 2943912848283068604899941)
                  ·
                    refine ⟨551983659053075363418739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2943912848283068604899941 551983659053075363418739)
                    ·
                      rfl

theorem cell23_3224953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_3224953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224953 prefixEnd_3224953 := by exact prefixLift 3224953
  have htrace : WordTrace (prefixWord ++ tailWord_3224953) baseStart_3224953 baseEnd_3224953 := by
    simpa [prefixWord, tailWord_3224953, baseEnd_3224953] using wordTrace_append hprefix tailTrace_3224953
  have hstable : (prefixWord ++ tailWord_3224953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224953).length < 2 ^ (prefixWord ++ tailWord_3224953).sum := by decide
  have hdescent : baseEnd_3224953 < baseStart_3224953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224956 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3224956 : Nat := 118140960795 + 3224956 * 2 ^ 59
def prefixEnd_3224956 : Nat := 4983230072969 + 3 ^ 40 * 3224956 * 2
def baseEnd_3224956 : Nat := 1655952517601189578518703

theorem tailTrace_3224956 : CollatzResearch.WordTrace tailWord_3224956 prefixEnd_3224956 1655952517601189578518703 := by
  unfold tailWord_3224956
  simp only [CollatzResearch.WordTrace]
  refine ⟨58811904252271332740091361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78415872336361776986788481 58811904252271332740091361)
  ·
    refine ⟨44108928189203499555068521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58811904252271332740091361 44108928189203499555068521)
    ·
      refine ⟨33081696141902624666301391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44108928189203499555068521 33081696141902624666301391)
      ·
        refine ⟨49622544212853936999452087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33081696141902624666301391 49622544212853936999452087)
        ·
          refine ⟨74433816319280905499178131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49622544212853936999452087 74433816319280905499178131)
          ·
            refine ⟨111650724478921358248767197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74433816319280905499178131 111650724478921358248767197)
            ·
              refine ⟨41869021679595509343287699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111650724478921358248767197 41869021679595509343287699)
              ·
                refine ⟨62803532519393264014931549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41869021679595509343287699 62803532519393264014931549)
                ·
                  refine ⟨23551324694772474005599331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62803532519393264014931549 23551324694772474005599331)
                  ·
                    refine ⟨35326987042158711008398997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23551324694772474005599331 35326987042158711008398997)
                    ·
                      refine ⟨1655952517601189578518703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35326987042158711008398997 1655952517601189578518703)
                      ·
                        rfl

theorem cell23_3224956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3224956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224956 prefixEnd_3224956 := by exact prefixLift 3224956
  have htrace : WordTrace (prefixWord ++ tailWord_3224956) baseStart_3224956 baseEnd_3224956 := by
    simpa [prefixWord, tailWord_3224956, baseEnd_3224956] using wordTrace_append hprefix tailTrace_3224956
  have hstable : (prefixWord ++ tailWord_3224956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224956).length < 2 ^ (prefixWord ++ tailWord_3224956).sum := by decide
  have hdescent : baseEnd_3224956 < baseStart_3224956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224963 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5]
def baseStart_3224963 : Nat := 118140960795 + 3224963 * 2 ^ 59
def prefixEnd_3224963 : Nat := 4983230072969 + 3 ^ 40 * 3224963 * 2
def baseEnd_3224963 : Nat := 1655956111965771051131171

theorem tailTrace_3224963 : CollatzResearch.WordTrace tailWord_3224963 prefixEnd_3224963 1655956111965771051131171 := by
  unfold tailWord_3224963
  simp only [CollatzResearch.WordTrace]
  refine ⟨117624063815517305675687543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78416042543678203783791695 117624063815517305675687543)
  ·
    refine ⟨176436095723275958513531315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117624063815517305675687543 176436095723275958513531315)
    ·
      refine ⟨264654143584913937770296973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176436095723275958513531315 264654143584913937770296973)
      ·
        refine ⟨99245303844342726663861365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264654143584913937770296973 99245303844342726663861365)
        ·
          refine ⟨9304247235407130624737003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99245303844342726663861365 9304247235407130624737003)
          ·
            refine ⟨13956370853110695937105505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304247235407130624737003 13956370853110695937105505)
            ·
              refine ⟨10467278139833021952829129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13956370853110695937105505 10467278139833021952829129)
              ·
                refine ⟨7850458604874766464621847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10467278139833021952829129 7850458604874766464621847)
                ·
                  refine ⟨11775687907312149696932771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850458604874766464621847 11775687907312149696932771)
                  ·
                    refine ⟨17663531860968224545399157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11775687907312149696932771 17663531860968224545399157)
                    ·
                      refine ⟨1655956111965771051131171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17663531860968224545399157 1655956111965771051131171)
                      ·
                        rfl

theorem cell23_3224963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_3224963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224963 prefixEnd_3224963 := by exact prefixLift 3224963
  have htrace : WordTrace (prefixWord ++ tailWord_3224963) baseStart_3224963 baseEnd_3224963 := by
    simpa [prefixWord, tailWord_3224963, baseEnd_3224963] using wordTrace_append hprefix tailTrace_3224963
  have hstable : (prefixWord ++ tailWord_3224963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224963).length < 2 ^ (prefixWord ++ tailWord_3224963).sum := by decide
  have hdescent : baseEnd_3224963 < baseStart_3224963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3224974 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3224974 : Nat := 118140960795 + 3224974 * 2 ^ 59
def prefixEnd_3224974 : Nat := 4983230072969 + 3 ^ 40 * 3224974 * 2
def baseEnd_3224974 : Nat := 551987253417656836031207

theorem tailTrace_3224974 : CollatzResearch.WordTrace tailWord_3224974 prefixEnd_3224974 551987253417656836031207 := by
  unfold tailWord_3224974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703058127309681819292247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78416310012318303036225317 14703058127309681819292247)
  ·
    refine ⟨22054587190964522728938371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14703058127309681819292247 22054587190964522728938371)
    ·
      refine ⟨33081880786446784093407557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22054587190964522728938371 33081880786446784093407557)
      ·
        refine ⟨6202852647458772017513917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33081880786446784093407557 6202852647458772017513917)
        ·
          refine ⟨2326069742797039506567719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6202852647458772017513917 2326069742797039506567719)
          ·
            refine ⟨3489104614195559259851579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326069742797039506567719 3489104614195559259851579)
            ·
              refine ⟨5233656921293338889777369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489104614195559259851579 5233656921293338889777369)
              ·
                refine ⟨3925242690970004167333027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233656921293338889777369 3925242690970004167333027)
                ·
                  refine ⟨5887864036455006250999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925242690970004167333027 5887864036455006250999541)
                  ·
                    refine ⟨551987253417656836031207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5887864036455006250999541 551987253417656836031207)
                    ·
                      rfl

theorem cell23_3224974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3224974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3224974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3224974 prefixEnd_3224974 := by exact prefixLift 3224974
  have htrace : WordTrace (prefixWord ++ tailWord_3224974) baseStart_3224974 baseEnd_3224974 := by
    simpa [prefixWord, tailWord_3224974, baseEnd_3224974] using wordTrace_append hprefix tailTrace_3224974
  have hstable : (prefixWord ++ tailWord_3224974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3224974).length < 2 ^ (prefixWord ++ tailWord_3224974).sum := by decide
  have hdescent : baseEnd_3224974 < baseStart_3224974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3224974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225000 : List Nat := [2, 1, 6, 1, 3, 10]
def baseStart_3225000 : Nat := 118140960795 + 3225000 * 2 ^ 59
def prefixEnd_3225000 : Nat := 4983230072969 + 3 ^ 40 * 3225000 * 2
def baseEnd_3225000 : Nat := 6814712389917643647607

theorem tailTrace_3225000 : CollatzResearch.WordTrace tailWord_3225000 prefixEnd_3225000 6814712389917643647607 := by
  unfold tailWord_3225000
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812706658191630497392227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78416942210922173996522969 58812706658191630497392227)
  ·
    refine ⟨88219059987287445746088341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58812706658191630497392227 88219059987287445746088341)
    ·
      refine ⟨4135268436904099019347891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88219059987287445746088341 4135268436904099019347891)
      ·
        refine ⟨6202902655356148529021837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135268436904099019347891 6202902655356148529021837)
        ·
          refine ⟨2326088495758555698383189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6202902655356148529021837 2326088495758555698383189)
          ·
            refine ⟨6814712389917643647607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2326088495758555698383189 6814712389917643647607)
            ·
              rfl

theorem cell23_3225000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 10].length) (baseStart_3225000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225000 prefixEnd_3225000 := by exact prefixLift 3225000
  have htrace : WordTrace (prefixWord ++ tailWord_3225000) baseStart_3225000 baseEnd_3225000 := by
    simpa [prefixWord, tailWord_3225000, baseEnd_3225000] using wordTrace_append hprefix tailTrace_3225000
  have hstable : (prefixWord ++ tailWord_3225000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225000).length < 2 ^ (prefixWord ++ tailWord_3225000).sum := by decide
  have hdescent : baseEnd_3225000 < baseStart_3225000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 7, 2]
def baseStart_3225003 : Nat := 118140960795 + 3225003 * 2 ^ 59
def prefixEnd_3225003 : Nat := 4983230072969 + 3 ^ 40 * 3225003 * 2
def baseEnd_3225003 : Nat := 1655976651191950894630987

theorem tailTrace_3225003 : CollatzResearch.WordTrace tailWord_3225003 prefixEnd_3225003 1655976651191950894630987 := by
  unfold tailWord_3225003
  simp only [CollatzResearch.WordTrace]
  refine ⟨117625522735372392507143663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78417015156914928338095775 117625522735372392507143663)
  ·
    refine ⟨176438284103058588760715495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117625522735372392507143663 176438284103058588760715495)
    ·
      refine ⟨264657426154587883141073243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176438284103058588760715495 264657426154587883141073243)
      ·
        refine ⟨396986139231881824711609865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264657426154587883141073243 396986139231881824711609865)
        ·
          refine ⟨297739604423911368533707399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396986139231881824711609865 297739604423911368533707399)
          ·
            refine ⟨446609406635867052800561099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297739604423911368533707399 446609406635867052800561099)
            ·
              refine ⟨669914109953800579200841649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446609406635867052800561099 669914109953800579200841649)
              ·
                refine ⟨502435582465350434400631237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669914109953800579200841649 502435582465350434400631237)
                ·
                  refine ⟨94206671712253206450118357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502435582465350434400631237 94206671712253206450118357)
                  ·
                    refine ⟨2207968868255934526174649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94206671712253206450118357 2207968868255934526174649)
                    ·
                      refine ⟨1655976651191950894630987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2207968868255934526174649 1655976651191950894630987)
                      ·
                        rfl

theorem cell23_3225003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7, 2].length) (baseStart_3225003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225003 prefixEnd_3225003 := by exact prefixLift 3225003
  have htrace : WordTrace (prefixWord ++ tailWord_3225003) baseStart_3225003 baseEnd_3225003 := by
    simpa [prefixWord, tailWord_3225003, baseEnd_3225003] using wordTrace_append hprefix tailTrace_3225003
  have hstable : (prefixWord ++ tailWord_3225003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225003).length < 2 ^ (prefixWord ++ tailWord_3225003).sum := by decide
  have hdescent : baseEnd_3225003 < baseStart_3225003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225013 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3225013 : Nat := 118140960795 + 3225013 * 2 ^ 59
def prefixEnd_3225013 : Nat := 4983230072969 + 3 ^ 40 * 3225013 * 2
def baseEnd_3225013 : Nat := 551993928666165285168647

theorem tailTrace_3225013 : CollatzResearch.WordTrace tailWord_3225013 prefixEnd_3225013 551993928666165285168647 := by
  unfold tailWord_3225013
  simp only [CollatzResearch.WordTrace]
  refine ⟨117625887465336164215007693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78417258310224109476671795 117625887465336164215007693)
  ·
    refine ⟨44109707799501061580627885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117625887465336164215007693 44109707799501061580627885)
    ·
      refine ⟨16541140424812898092735457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44109707799501061580627885 16541140424812898092735457)
      ·
        refine ⟨12405855318609673569551593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16541140424812898092735457 12405855318609673569551593)
        ·
          refine ⟨9304391488957255177163695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12405855318609673569551593 9304391488957255177163695)
          ·
            refine ⟨13956587233435882765745543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304391488957255177163695 13956587233435882765745543)
            ·
              refine ⟨20934880850153824148618315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13956587233435882765745543 20934880850153824148618315)
              ·
                refine ⟨31402321275230736222927473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20934880850153824148618315 31402321275230736222927473)
                ·
                  refine ⟨23551740956423052167195605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31402321275230736222927473 23551740956423052167195605)
                  ·
                    refine ⟨551993928666165285168647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23551740956423052167195605 551993928666165285168647)
                    ·
                      rfl

theorem cell23_3225013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3225013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225013 prefixEnd_3225013 := by exact prefixLift 3225013
  have htrace : WordTrace (prefixWord ++ tailWord_3225013) baseStart_3225013 baseEnd_3225013 := by
    simpa [prefixWord, tailWord_3225013, baseEnd_3225013] using wordTrace_append hprefix tailTrace_3225013
  have hstable : (prefixWord ++ tailWord_3225013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225013).length < 2 ^ (prefixWord ++ tailWord_3225013).sum := by decide
  have hdescent : baseEnd_3225013 < baseStart_3225013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225067 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 2, 2, 2]
def baseStart_3225067 : Nat := 118140960795 + 3225067 * 2 ^ 59
def prefixEnd_3225067 : Nat := 4983230072969 + 3 ^ 40 * 3225067 * 2
def baseEnd_3225067 : Nat := 1656009513953838644230693

theorem tailTrace_3225067 : CollatzResearch.WordTrace tailWord_3225067 prefixEnd_3225067 1656009513953838644230693 := by
  unfold tailWord_3225067
  simp only [CollatzResearch.WordTrace]
  refine ⟨117627857007140531437473455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78418571338093687624982303 117627857007140531437473455)
  ·
    refine ⟨176441785510710797156210183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117627857007140531437473455 176441785510710797156210183)
    ·
      refine ⟨264662678266066195734315275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176441785510710797156210183 264662678266066195734315275)
      ·
        refine ⟨396994017399099293601472913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264662678266066195734315275 396994017399099293601472913)
        ·
          refine ⟨297745513049324470201104685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396994017399099293601472913 297745513049324470201104685)
          ·
            refine ⟨111654567393496676325414257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297745513049324470201104685 111654567393496676325414257)
            ·
              refine ⟨83740925545122507244060693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111654567393496676325414257 83740925545122507244060693)
              ·
                refine ⟨3925355884927617527065345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83740925545122507244060693 3925355884927617527065345)
                ·
                  refine ⟨2944016913695713145299009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3925355884927617527065345 2944016913695713145299009)
                  ·
                    refine ⟨2208012685271784858974257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944016913695713145299009 2208012685271784858974257)
                    ·
                      refine ⟨1656009513953838644230693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208012685271784858974257 1656009513953838644230693)
                      ·
                        rfl

theorem cell23_3225067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 2, 2].length) (baseStart_3225067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225067 prefixEnd_3225067 := by exact prefixLift 3225067
  have htrace : WordTrace (prefixWord ++ tailWord_3225067) baseStart_3225067 baseEnd_3225067 := by
    simpa [prefixWord, tailWord_3225067, baseEnd_3225067] using wordTrace_append hprefix tailTrace_3225067
  have hstable : (prefixWord ++ tailWord_3225067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225067).length < 2 ^ (prefixWord ++ tailWord_3225067).sum := by decide
  have hdescent : baseEnd_3225067 < baseStart_3225067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225073 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 7]
def baseStart_3225073 : Nat := 118140960795 + 3225073 * 2 ^ 59
def prefixEnd_3225073 : Nat := 4983230072969 + 3 ^ 40 * 3225073 * 2
def baseEnd_3225073 : Nat := 184001399426418402306185

theorem tailTrace_3225073 : CollatzResearch.WordTrace tailWord_3225073 prefixEnd_3225073 184001399426418402306185 := by
  unfold tailWord_3225073
  simp only [CollatzResearch.WordTrace]
  refine ⟨117628075845118794462191873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78418717230079196308127915 117628075845118794462191873)
  ·
    refine ⟨88221056883839095846643905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117628075845118794462191873 88221056883839095846643905)
    ·
      refine ⟨66165792662879321884982929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88221056883839095846643905 66165792662879321884982929)
      ·
        refine ⟨49624344497159491413737197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66165792662879321884982929 49624344497159491413737197)
        ·
          refine ⟨18609129186434809280151449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49624344497159491413737197 18609129186434809280151449)
          ·
            refine ⟨13956846889826106960113587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18609129186434809280151449 13956846889826106960113587)
            ·
              refine ⟨20935270334739160440170381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13956846889826106960113587 20935270334739160440170381)
              ·
                refine ⟨7850726375527185165063893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20935270334739160440170381 7850726375527185165063893)
                ·
                  refine ⟨184001399426418402306185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7850726375527185165063893 184001399426418402306185)
                  ·
                    rfl

theorem cell23_3225073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_3225073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225073 prefixEnd_3225073 := by exact prefixLift 3225073
  have htrace : WordTrace (prefixWord ++ tailWord_3225073) baseStart_3225073 baseEnd_3225073 := by
    simpa [prefixWord, tailWord_3225073, baseEnd_3225073] using wordTrace_append hprefix tailTrace_3225073
  have hstable : (prefixWord ++ tailWord_3225073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225073).length < 2 ^ (prefixWord ++ tailWord_3225073).sum := by decide
  have hdescent : baseEnd_3225073 < baseStart_3225073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225107 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 5]
def baseStart_3225107 : Nat := 118140960795 + 3225107 * 2 ^ 59
def prefixEnd_3225107 : Nat := 4983230072969 + 3 ^ 40 * 3225107 * 2
def baseEnd_3225107 : Nat := 184003339242224276414501

theorem tailTrace_3225107 : CollatzResearch.WordTrace tailWord_3225107 prefixEnd_3225107 184003339242224276414501 := by
  unfold tailWord_3225107
  simp only [CollatzResearch.WordTrace]
  refine ⟨117629315926995618268929575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78419543951330412179286383 117629315926995618268929575)
  ·
    refine ⟨176443973890493427403394363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117629315926995618268929575 176443973890493427403394363)
    ·
      refine ⟨264665960835740141105091545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176443973890493427403394363 264665960835740141105091545)
      ·
        refine ⟨198499470626805105828818659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264665960835740141105091545 198499470626805105828818659)
        ·
          refine ⟨297749205940207658743227989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198499470626805105828818659 297749205940207658743227989)
          ·
            refine ⟨3489248507111808500897203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 297749205940207658743227989 3489248507111808500897203)
            ·
              refine ⟨5233872760667712751345805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489248507111808500897203 5233872760667712751345805)
              ·
                refine ⟨1962702285250392281754677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5233872760667712751345805 1962702285250392281754677)
                ·
                  refine ⟨184003339242224276414501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1962702285250392281754677 184003339242224276414501)
                  ·
                    rfl

theorem cell23_3225107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 5].length) (baseStart_3225107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225107 prefixEnd_3225107 := by exact prefixLift 3225107
  have htrace : WordTrace (prefixWord ++ tailWord_3225107) baseStart_3225107 baseEnd_3225107 := by
    simpa [prefixWord, tailWord_3225107, baseEnd_3225107] using wordTrace_append hprefix tailTrace_3225107
  have hstable : (prefixWord ++ tailWord_3225107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225107).length < 2 ^ (prefixWord ++ tailWord_3225107).sum := by decide
  have hdescent : baseEnd_3225107 < baseStart_3225107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225120 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_3225120 : Nat := 118140960795 + 3225120 * 2 ^ 59
def prefixEnd_3225120 : Nat := 4983230072969 + 3 ^ 40 * 3225120 * 2
def baseEnd_3225120 : Nat := 552012242809508978955983

theorem tailTrace_3225120 : CollatzResearch.WordTrace tailWord_3225120 prefixEnd_3225120 552012242809508978955983 := by
  unfold tailWord_3225120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58814895037974260744576407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78419860050632347659435209 58814895037974260744576407)
  ·
    refine ⟨88222342556961391116864611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58814895037974260744576407 88222342556961391116864611)
    ·
      refine ⟨132333513835442086675296917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88222342556961391116864611 132333513835442086675296917)
      ·
        refine ⟨6203133461036347812904543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132333513835442086675296917 6203133461036347812904543)
        ·
          refine ⟨9304700191554521719356815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203133461036347812904543 9304700191554521719356815)
          ·
            refine ⟨13957050287331782579035223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304700191554521719356815 13957050287331782579035223)
            ·
              refine ⟨20935575430997673868552835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957050287331782579035223 20935575430997673868552835)
              ·
                refine ⟨31403363146496510802829253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20935575430997673868552835 31403363146496510802829253)
                ·
                  refine ⟨5888130589968095775530485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31403363146496510802829253 5888130589968095775530485)
                  ·
                    refine ⟨552012242809508978955983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5888130589968095775530485 552012242809508978955983)
                    ·
                      rfl

theorem cell23_3225120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_3225120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225120 prefixEnd_3225120 := by exact prefixLift 3225120
  have htrace : WordTrace (prefixWord ++ tailWord_3225120) baseStart_3225120 baseEnd_3225120 := by
    simpa [prefixWord, tailWord_3225120, baseEnd_3225120] using wordTrace_append hprefix tailTrace_3225120
  have hstable : (prefixWord ++ tailWord_3225120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225120).length < 2 ^ (prefixWord ++ tailWord_3225120).sum := by decide
  have hdescent : baseEnd_3225120 < baseStart_3225120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225130 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3225130 : Nat := 118140960795 + 3225130 * 2 ^ 59
def prefixEnd_3225130 : Nat := 4983230072969 + 3 ^ 40 * 3225130 * 2
def baseEnd_3225130 : Nat := 1656041863235071897742903

theorem tailTrace_3225130 : CollatzResearch.WordTrace tailWord_3225130 prefixEnd_3225130 1656041863235071897742903 := by
  unfold tailWord_3225130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407538701478073299254211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78420103203941528798011229 29407538701478073299254211)
  ·
    refine ⟨44111308052217109948881317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407538701478073299254211 44111308052217109948881317)
    ·
      refine ⟨8270870259790708115415247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44111308052217109948881317 8270870259790708115415247)
      ·
        refine ⟨12406305389686062173122871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8270870259790708115415247 12406305389686062173122871)
        ·
          refine ⟨18609458084529093259684307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406305389686062173122871 18609458084529093259684307)
          ·
            refine ⟨27914187126793639889526461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18609458084529093259684307 27914187126793639889526461)
            ·
              refine ⟨10467820172547614958572423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27914187126793639889526461 10467820172547614958572423)
              ·
                refine ⟨15701730258821422437858635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467820172547614958572423 15701730258821422437858635)
                ·
                  refine ⟨23552595388232133656787953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15701730258821422437858635 23552595388232133656787953)
                  ·
                    refine ⟨17664446541174100242590965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23552595388232133656787953 17664446541174100242590965)
                    ·
                      refine ⟨1656041863235071897742903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17664446541174100242590965 1656041863235071897742903)
                      ·
                        rfl

theorem cell23_3225130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3225130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225130 prefixEnd_3225130 := by exact prefixLift 3225130
  have htrace : WordTrace (prefixWord ++ tailWord_3225130) baseStart_3225130 baseEnd_3225130 := by
    simpa [prefixWord, tailWord_3225130, baseEnd_3225130] using wordTrace_append hprefix tailTrace_3225130
  have hstable : (prefixWord ++ tailWord_3225130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225130).length < 2 ^ (prefixWord ++ tailWord_3225130).sum := by decide
  have hdescent : baseEnd_3225130 < baseStart_3225130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225167 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 1, 4]
def baseStart_3225167 : Nat := 118140960795 + 3225167 * 2 ^ 59
def prefixEnd_3225167 : Nat := 4983230072969 + 3 ^ 40 * 3225167 * 2
def baseEnd_3225167 : Nat := 552020287339762750993411

theorem tailTrace_3225167 : CollatzResearch.WordTrace tailWord_3225167 prefixEnd_3225167 552020287339762750993411 := by
  unfold tailWord_3225167
  simp only [CollatzResearch.WordTrace]
  refine ⟨117631504306778248516113755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78421002871185499010742503 117631504306778248516113755)
  ·
    refine ⟨176447256460167372774170633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117631504306778248516113755 176447256460167372774170633)
    ·
      refine ⟨132335442345125529580627975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176447256460167372774170633 132335442345125529580627975)
      ·
        refine ⟨198503163517688294370941963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132335442345125529580627975 198503163517688294370941963)
        ·
          refine ⟨297754745276532441556412945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198503163517688294370941963 297754745276532441556412945)
          ·
            refine ⟨223316058957399331167309709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297754745276532441556412945 223316058957399331167309709)
            ·
              refine ⟨83743522109024749187741141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223316058957399331167309709 83743522109024749187741141)
              ·
                refine ⟨1962738799430267559087683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83743522109024749187741141 1962738799430267559087683)
                ·
                  refine ⟨2944108199145401338631525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962738799430267559087683 2944108199145401338631525)
                  ·
                    refine ⟨552020287339762750993411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944108199145401338631525 552020287339762750993411)
                    ·
                      rfl

theorem cell23_3225167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 4].length) (baseStart_3225167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225167 prefixEnd_3225167 := by exact prefixLift 3225167
  have htrace : WordTrace (prefixWord ++ tailWord_3225167) baseStart_3225167 baseEnd_3225167 := by
    simpa [prefixWord, tailWord_3225167, baseEnd_3225167] using wordTrace_append hprefix tailTrace_3225167
  have hstable : (prefixWord ++ tailWord_3225167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225167).length < 2 ^ (prefixWord ++ tailWord_3225167).sum := by decide
  have hdescent : baseEnd_3225167 < baseStart_3225167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225203 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_3225203 : Nat := 118140960795 + 3225203 * 2 ^ 59
def prefixEnd_3225203 : Nat := 4983230072969 + 3 ^ 40 * 3225203 * 2
def baseEnd_3225203 : Nat := 1656079347322850112130067

theorem tailTrace_3225203 : CollatzResearch.WordTrace tailWord_3225203 prefixEnd_3225203 1656079347322850112130067 := by
  unfold tailWord_3225203
  simp only [CollatzResearch.WordTrace]
  refine ⟨117632817334647826664424263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78421878223098551109616175 117632817334647826664424263)
  ·
    refine ⟨176449226001971739996636395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117632817334647826664424263 176449226001971739996636395)
    ·
      refine ⟨264673839002957609994954593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176449226001971739996636395 264673839002957609994954593)
      ·
        refine ⟨198505379252218207496215945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264673839002957609994954593 198505379252218207496215945)
        ·
          refine ⟨148879034439163655622161959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198505379252218207496215945 148879034439163655622161959)
          ·
            refine ⟨223318551658745483433242939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148879034439163655622161959 223318551658745483433242939)
            ·
              refine ⟨334977827488118225149864409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223318551658745483433242939 334977827488118225149864409)
              ·
                refine ⟨251233370616088668862398307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334977827488118225149864409 251233370616088668862398307)
                ·
                  refine ⟨376850055924133003293597461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251233370616088668862398307 376850055924133003293597461)
                  ·
                    refine ⟨17664846371443734529387381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 376850055924133003293597461 17664846371443734529387381)
                    ·
                      refine ⟨1656079347322850112130067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17664846371443734529387381 1656079347322850112130067)
                      ·
                        rfl

theorem cell23_3225203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_3225203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225203 prefixEnd_3225203 := by exact prefixLift 3225203
  have htrace : WordTrace (prefixWord ++ tailWord_3225203) baseStart_3225203 baseEnd_3225203 := by
    simpa [prefixWord, tailWord_3225203, baseEnd_3225203] using wordTrace_append hprefix tailTrace_3225203
  have hstable : (prefixWord ++ tailWord_3225203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225203).length < 2 ^ (prefixWord ++ tailWord_3225203).sum := by decide
  have hdescent : baseEnd_3225203 < baseStart_3225203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225264 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2]
def baseStart_3225264 : Nat := 118140960795 + 3225264 * 2 ^ 59
def prefixEnd_3225264 : Nat := 4983230072969 + 3 ^ 40 * 3225264 * 2
def baseEnd_3225264 : Nat := 1656110669642774373467287

theorem tailTrace_3225264 : CollatzResearch.WordTrace tailWord_3225264 prefixEnd_3225264 1656110669642774373467287 := by
  unfold tailWord_3225264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58817521093713417041197423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78423361458284556054929897 58817521093713417041197423)
  ·
    refine ⟨88226281640570125561796135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58817521093713417041197423 88226281640570125561796135)
    ·
      refine ⟨132339422460855188342694203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88226281640570125561796135 132339422460855188342694203)
      ·
        refine ⟨198509133691282782514041305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132339422460855188342694203 198509133691282782514041305)
        ·
          refine ⟨148881850268462086885530979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198509133691282782514041305 148881850268462086885530979)
          ·
            refine ⟨223322775402693130328296469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148881850268462086885530979 223322775402693130328296469)
            ·
              refine ⟨10468255097001240484138897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223322775402693130328296469 10468255097001240484138897)
              ·
                refine ⟨7851191322750930363104173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10468255097001240484138897 7851191322750930363104173)
                ·
                  refine ⟨2944196746031598886164065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7851191322750930363104173 2944196746031598886164065)
                  ·
                    refine ⟨2208147559523699164623049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944196746031598886164065 2208147559523699164623049)
                    ·
                      refine ⟨1656110669642774373467287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208147559523699164623049 1656110669642774373467287)
                      ·
                        rfl

theorem cell23_3225264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2].length) (baseStart_3225264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225264 prefixEnd_3225264 := by exact prefixLift 3225264
  have htrace : WordTrace (prefixWord ++ tailWord_3225264) baseStart_3225264 baseEnd_3225264 := by
    simpa [prefixWord, tailWord_3225264, baseEnd_3225264] using wordTrace_append hprefix tailTrace_3225264
  have hstable : (prefixWord ++ tailWord_3225264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225264).length < 2 ^ (prefixWord ++ tailWord_3225264).sum := by decide
  have hdescent : baseEnd_3225264 < baseStart_3225264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225284 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3225284 : Nat := 118140960795 + 3225284 * 2 ^ 59
def prefixEnd_3225284 : Nat := 4983230072969 + 3 ^ 40 * 3225284 * 2
def baseEnd_3225284 : Nat := 1656120939255864295217195

theorem tailTrace_3225284 : CollatzResearch.WordTrace tailWord_3225284 prefixEnd_3225284 1656120939255864295217195 := by
  unfold tailWord_3225284
  simp only [CollatzResearch.WordTrace]
  refine ⟨58817885823677188749061453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78423847764902918332081937 58817885823677188749061453)
  ·
    refine ⟨22056707183878945780898045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58817885823677188749061453 22056707183878945780898045)
    ·
      refine ⟨8271265193954604667836767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22056707183878945780898045 8271265193954604667836767)
      ·
        refine ⟨12406897790931907001755151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271265193954604667836767 12406897790931907001755151)
        ·
          refine ⟨18610346686397860502632727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12406897790931907001755151 18610346686397860502632727)
          ·
            refine ⟨27915520029596790753949091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18610346686397860502632727 27915520029596790753949091)
            ·
              refine ⟨41873280044395186130923637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27915520029596790753949091 41873280044395186130923637)
              ·
                refine ⟨3925620004162048699774091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41873280044395186130923637 3925620004162048699774091)
                ·
                  refine ⟨5888430006243073049661137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925620004162048699774091 5888430006243073049661137)
                  ·
                    refine ⟨4416322504682304787245853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888430006243073049661137 4416322504682304787245853)
                    ·
                      refine ⟨1656120939255864295217195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4416322504682304787245853 1656120939255864295217195)
                      ·
                        rfl

theorem cell23_3225284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3225284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225284 prefixEnd_3225284 := by exact prefixLift 3225284
  have htrace : WordTrace (prefixWord ++ tailWord_3225284) baseStart_3225284 baseEnd_3225284 := by
    simpa [prefixWord, tailWord_3225284, baseEnd_3225284] using wordTrace_append hprefix tailTrace_3225284
  have hstable : (prefixWord ++ tailWord_3225284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225284).length < 2 ^ (prefixWord ++ tailWord_3225284).sum := by decide
  have hdescent : baseEnd_3225284 < baseStart_3225284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225298 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3225298 : Nat := 118140960795 + 3225298 * 2 ^ 59
def prefixEnd_3225298 : Nat := 4983230072969 + 3 ^ 40 * 3225298 * 2
def baseEnd_3225298 : Nat := 1656128127985027240442131

theorem tailTrace_3225298 : CollatzResearch.WordTrace tailWord_3225298 prefixEnd_3225298 1656128127985027240442131 := by
  unfold tailWord_3225298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29409070567325914472283137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78424188179535771926088365 29409070567325914472283137)
  ·
    refine ⟨22056802925494435854212353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29409070567325914472283137 22056802925494435854212353)
    ·
      refine ⟨16542602194120826890659265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22056802925494435854212353 16542602194120826890659265)
      ·
        refine ⟨12406951645590620167994449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16542602194120826890659265 12406951645590620167994449)
        ·
          refine ⟨9305213734192965125995837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12406951645590620167994449 9305213734192965125995837)
          ·
            refine ⟨3489455150322361922248439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9305213734192965125995837 3489455150322361922248439)
            ·
              refine ⟨5234182725483542883372659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489455150322361922248439 5234182725483542883372659)
              ·
                refine ⟨7851274088225314325058989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234182725483542883372659 7851274088225314325058989)
                ·
                  refine ⟨2944227783084492871897121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7851274088225314325058989 2944227783084492871897121)
                  ·
                    refine ⟨2208170837313369653922841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944227783084492871897121 2208170837313369653922841)
                    ·
                      refine ⟨1656128127985027240442131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208170837313369653922841 1656128127985027240442131)
                      ·
                        rfl

theorem cell23_3225298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3225298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225298 prefixEnd_3225298 := by exact prefixLift 3225298
  have htrace : WordTrace (prefixWord ++ tailWord_3225298) baseStart_3225298 baseEnd_3225298 := by
    simpa [prefixWord, tailWord_3225298, baseEnd_3225298] using wordTrace_append hprefix tailTrace_3225298
  have hstable : (prefixWord ++ tailWord_3225298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225298).length < 2 ^ (prefixWord ++ tailWord_3225298).sum := by decide
  have hdescent : baseEnd_3225298 < baseStart_3225298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225367 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3225367 : Nat := 118140960795 + 3225367 * 2 ^ 59
def prefixEnd_3225367 : Nat := 4983230072969 + 3 ^ 40 * 3225367 * 2
def baseEnd_3225367 : Nat := 1656163558150187470479313

theorem tailTrace_3225367 : CollatzResearch.WordTrace tailWord_3225367 prefixEnd_3225367 1656163558150187470479313 := by
  unfold tailWord_3225367
  simp only [CollatzResearch.WordTrace]
  refine ⟨117638798906053682673394355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78425865937369121782262903 117638798906053682673394355)
  ·
    refine ⟨176458198359080524010091533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117638798906053682673394355 176458198359080524010091533)
    ·
      refine ⟨66171824384655196503784325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176458198359080524010091533 66171824384655196503784325)
      ·
        refine ⟨12407217072122849344459561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66171824384655196503784325 12407217072122849344459561)
        ·
          refine ⟨9305412804092137008344671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12407217072122849344459561 9305412804092137008344671)
          ·
            refine ⟨13958119206138205512517007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305412804092137008344671 13958119206138205512517007)
            ·
              refine ⟨20937178809207308268775511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958119206138205512517007 20937178809207308268775511)
              ·
                refine ⟨31405768213810962403163267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20937178809207308268775511 31405768213810962403163267)
                ·
                  refine ⟨47108652320716443604744901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31405768213810962403163267 47108652320716443604744901)
                  ·
                    refine ⟨8832872310134333175889669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47108652320716443604744901 8832872310134333175889669)
                    ·
                      refine ⟨1656163558150187470479313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8832872310134333175889669 1656163558150187470479313)
                      ·
                        rfl

theorem cell23_3225367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3225367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225367 prefixEnd_3225367 := by exact prefixLift 3225367
  have htrace : WordTrace (prefixWord ++ tailWord_3225367) baseStart_3225367 baseEnd_3225367 := by
    simpa [prefixWord, tailWord_3225367, baseEnd_3225367] using wordTrace_append hprefix tailTrace_3225367
  have hstable : (prefixWord ++ tailWord_3225367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225367).length < 2 ^ (prefixWord ++ tailWord_3225367).sum := by decide
  have hdescent : baseEnd_3225367 < baseStart_3225367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225377 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 7]
def baseStart_3225377 : Nat := 118140960795 + 3225377 * 2 ^ 59
def prefixEnd_3225377 : Nat := 4983230072969 + 3 ^ 40 * 3225377 * 2
def baseEnd_3225377 : Nat := 184018743661859159039363

theorem tailTrace_3225377 : CollatzResearch.WordTrace tailWord_3225377 prefixEnd_3225377 184018743661859159039363 := by
  unfold tailWord_3225377
  simp only [CollatzResearch.WordTrace]
  refine ⟨117639163636017454381258385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78426109090678302920838923 117639163636017454381258385)
  ·
    refine ⟨88229372727013090785943789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117639163636017454381258385 88229372727013090785943789)
    ·
      refine ⟨33086014772629909044728921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88229372727013090785943789 33086014772629909044728921)
      ·
        refine ⟨24814511079472431783546691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33086014772629909044728921 24814511079472431783546691)
        ·
          refine ⟨37221766619208647675320037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24814511079472431783546691 37221766619208647675320037)
          ·
            refine ⟨6979081241101621439122507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37221766619208647675320037 6979081241101621439122507)
            ·
              refine ⟨10468621861652432158683761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979081241101621439122507 10468621861652432158683761)
              ·
                refine ⟨7851466396239324119012821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10468621861652432158683761 7851466396239324119012821)
                ·
                  refine ⟨184018743661859159039363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7851466396239324119012821 184018743661859159039363)
                  ·
                    rfl

theorem cell23_3225377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_3225377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225377 prefixEnd_3225377 := by exact prefixLift 3225377
  have htrace : WordTrace (prefixWord ++ tailWord_3225377) baseStart_3225377 baseEnd_3225377 := by
    simpa [prefixWord, tailWord_3225377, baseEnd_3225377] using wordTrace_append hprefix tailTrace_3225377
  have hstable : (prefixWord ++ tailWord_3225377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225377).length < 2 ^ (prefixWord ++ tailWord_3225377).sum := by decide
  have hdescent : baseEnd_3225377 < baseStart_3225377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225394 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3225394 : Nat := 118140960795 + 3225394 * 2 ^ 59
def prefixEnd_3225394 : Nat := 4983230072969 + 3 ^ 40 * 3225394 * 2
def baseEnd_3225394 : Nat := 184019713569762096093521

theorem tailTrace_3225394 : CollatzResearch.WordTrace tailWord_3225394 prefixEnd_3225394 184019713569762096093521 := by
  unfold tailWord_3225394
  simp only [CollatzResearch.WordTrace]
  refine ⟨29409945919238966571156809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78426522451303910856418157 29409945919238966571156809)
  ·
    refine ⟨22057459439429224928367607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29409945919238966571156809 22057459439429224928367607)
    ·
      refine ⟨33086189159143837392551411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22057459439429224928367607 33086189159143837392551411)
      ·
        refine ⟨49629283738715756088827117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33086189159143837392551411 49629283738715756088827117)
        ·
          refine ⟨18610981402018408533310169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49629283738715756088827117 18610981402018408533310169)
          ·
            refine ⟨13958236051513806399982627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18610981402018408533310169 13958236051513806399982627)
            ·
              refine ⟨20937354077270709599973941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958236051513806399982627 20937354077270709599973941)
              ·
                refine ⟨1962876944744129024997557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20937354077270709599973941 1962876944744129024997557)
                ·
                  refine ⟨184019713569762096093521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1962876944744129024997557 184019713569762096093521)
                  ·
                    rfl

theorem cell23_3225394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3225394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225394 prefixEnd_3225394 := by exact prefixLift 3225394
  have htrace : WordTrace (prefixWord ++ tailWord_3225394) baseStart_3225394 baseEnd_3225394 := by
    simpa [prefixWord, tailWord_3225394, baseEnd_3225394] using wordTrace_append hprefix tailTrace_3225394
  have hstable : (prefixWord ++ tailWord_3225394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225394).length < 2 ^ (prefixWord ++ tailWord_3225394).sum := by decide
  have hdescent : baseEnd_3225394 < baseStart_3225394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225405 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3225405 : Nat := 118140960795 + 3225405 * 2 ^ 59
def prefixEnd_3225405 : Nat := 4983230072969 + 3 ^ 40 * 3225405 * 2
def baseEnd_3225405 : Nat := 1656183070415058321804139

theorem tailTrace_3225405 : CollatzResearch.WordTrace tailWord_3225405 prefixEnd_3225405 1656183070415058321804139 := by
  unfold tailWord_3225405
  simp only [CollatzResearch.WordTrace]
  refine ⟨117640184879916015163277669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78426789919944010108851779 117640184879916015163277669)
  ·
    refine ⟨22057534664984252843114563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117640184879916015163277669 22057534664984252843114563)
    ·
      refine ⟨33086301997476379264671845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22057534664984252843114563 33086301997476379264671845)
      ·
        refine ⟨6203681624526821112125971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33086301997476379264671845 6203681624526821112125971)
        ·
          refine ⟨9305522436790231668188957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203681624526821112125971 9305522436790231668188957)
          ·
            refine ⟨3489570913796336875570859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9305522436790231668188957 3489570913796336875570859)
            ·
              refine ⟨5234356370694505313356289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489570913796336875570859 5234356370694505313356289)
              ·
                refine ⟨3925767278020878985017217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234356370694505313356289 3925767278020878985017217)
                ·
                  refine ⟨2944325458515659238762913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3925767278020878985017217 2944325458515659238762913)
                  ·
                    refine ⟨2208244093886744429072185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944325458515659238762913 2208244093886744429072185)
                    ·
                      refine ⟨1656183070415058321804139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208244093886744429072185 1656183070415058321804139)
                      ·
                        rfl

theorem cell23_3225405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3225405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225405 prefixEnd_3225405 := by exact prefixLift 3225405
  have htrace : WordTrace (prefixWord ++ tailWord_3225405) baseStart_3225405 baseEnd_3225405 := by
    simpa [prefixWord, tailWord_3225405, baseEnd_3225405] using wordTrace_append hprefix tailTrace_3225405
  have hstable : (prefixWord ++ tailWord_3225405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225405).length < 2 ^ (prefixWord ++ tailWord_3225405).sum := by decide
  have hdescent : baseEnd_3225405 < baseStart_3225405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225421 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3225421 : Nat := 118140960795 + 3225421 * 2 ^ 59
def prefixEnd_3225421 : Nat := 4983230072969 + 3 ^ 40 * 3225421 * 2
def baseEnd_3225421 : Nat := 1656191286105530259204065

theorem tailTrace_3225421 : CollatzResearch.WordTrace tailWord_3225421 prefixEnd_3225421 1656191286105530259204065 := by
  unfold tailWord_3225421
  simp only [CollatzResearch.WordTrace]
  refine ⟨117640768447858049895860117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78427178965238699930573411 117640768447858049895860117)
  ·
    refine ⟨5514411020993346088868443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117640768447858049895860117 5514411020993346088868443)
    ·
      refine ⟨8271616531490019133302665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5514411020993346088868443 8271616531490019133302665)
      ·
        refine ⟨6203712398617514349976999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8271616531490019133302665 6203712398617514349976999)
        ·
          refine ⟨9305568597926271524965499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203712398617514349976999 9305568597926271524965499)
          ·
            refine ⟨13958352896889407287448249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305568597926271524965499 13958352896889407287448249)
            ·
              refine ⟨10468764672667055465586187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13958352896889407287448249 10468764672667055465586187)
              ·
                refine ⟨15703147009000583198379281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10468764672667055465586187 15703147009000583198379281)
                ·
                  refine ⟨11777360256750437398784461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15703147009000583198379281 11777360256750437398784461)
                  ·
                    refine ⟨4416510096281414024544173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11777360256750437398784461 4416510096281414024544173)
                    ·
                      refine ⟨1656191286105530259204065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4416510096281414024544173 1656191286105530259204065)
                      ·
                        rfl

theorem cell23_3225421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3225421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225421 prefixEnd_3225421 := by exact prefixLift 3225421
  have htrace : WordTrace (prefixWord ++ tailWord_3225421) baseStart_3225421 baseEnd_3225421 := by
    simpa [prefixWord, tailWord_3225421, baseEnd_3225421] using wordTrace_append hprefix tailTrace_3225421
  have hstable : (prefixWord ++ tailWord_3225421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225421).length < 2 ^ (prefixWord ++ tailWord_3225421).sum := by decide
  have hdescent : baseEnd_3225421 < baseStart_3225421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225467 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 6]
def baseStart_3225467 : Nat := 118140960795 + 3225467 * 2 ^ 59
def prefixEnd_3225467 : Nat := 4983230072969 + 3 ^ 40 * 3225467 * 2
def baseEnd_3225467 : Nat := 184023878468404119914317

theorem tailTrace_3225467 : CollatzResearch.WordTrace tailWord_3225467 prefixEnd_3225467 184023878468404119914317 := by
  unfold tailWord_3225467
  simp only [CollatzResearch.WordTrace]
  refine ⟨117642446205691399752034655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78428297470460933168023103 117642446205691399752034655)
  ·
    refine ⟨176463669308537099628051983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117642446205691399752034655 176463669308537099628051983)
    ·
      refine ⟨264695503962805649442077975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176463669308537099628051983 264695503962805649442077975)
      ·
        refine ⟨397043255944208474163116963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264695503962805649442077975 397043255944208474163116963)
        ·
          refine ⟨595564883916312711244675445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397043255944208474163116963 595564883916312711244675445)
          ·
            refine ⟨55834207867154316679188323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 595564883916312711244675445 55834207867154316679188323)
            ·
              refine ⟨83751311800731475018782485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55834207867154316679188323 83751311800731475018782485)
              ·
                refine ⟨3925842740659287891505429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83751311800731475018782485 3925842740659287891505429)
                ·
                  refine ⟨184023878468404119914317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3925842740659287891505429 184023878468404119914317)
                  ·
                    rfl

theorem cell23_3225467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 6].length) (baseStart_3225467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225467 prefixEnd_3225467 := by exact prefixLift 3225467
  have htrace : WordTrace (prefixWord ++ tailWord_3225467) baseStart_3225467 baseEnd_3225467 := by
    simpa [prefixWord, tailWord_3225467, baseEnd_3225467] using wordTrace_append hprefix tailTrace_3225467
  have hstable : (prefixWord ++ tailWord_3225467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225467).length < 2 ^ (prefixWord ++ tailWord_3225467).sum := by decide
  have hdescent : baseEnd_3225467 < baseStart_3225467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225527 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 5, 6]
def baseStart_3225527 : Nat := 118140960795 + 3225527 * 2 ^ 59
def prefixEnd_3225527 : Nat := 4983230072969 + 3 ^ 40 * 3225527 * 2
def baseEnd_3225527 : Nat := 552081905018302281492859

theorem tailTrace_3225527 : CollatzResearch.WordTrace tailWord_3225527 prefixEnd_3225527 552081905018302281492859 := by
  unfold tailWord_3225527
  simp only [CollatzResearch.WordTrace]
  refine ⟨117644634585474029999218835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78429756390316019999479223 117644634585474029999218835)
  ·
    refine ⟨176466951878211044998828253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117644634585474029999218835 176466951878211044998828253)
    ·
      refine ⟨66175106954329141874560595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176466951878211044998828253 66175106954329141874560595)
      ·
        refine ⟨99262660431493712811840893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66175106954329141874560595 99262660431493712811840893)
        ·
          refine ⟨37223497661810142304440335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99262660431493712811840893 37223497661810142304440335)
          ·
            refine ⟨55835246492715213456660503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37223497661810142304440335 55835246492715213456660503)
            ·
              refine ⟨83752869739072820184990755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55835246492715213456660503 83752869739072820184990755)
              ·
                refine ⟨125629304608609230277486133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83752869739072820184990755 125629304608609230277486133)
                ·
                  refine ⟨11777747307057115338514325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125629304608609230277486133 11777747307057115338514325)
                  ·
                    refine ⟨552081905018302281492859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11777747307057115338514325 552081905018302281492859)
                    ·
                      rfl

theorem cell23_3225527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_3225527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225527 prefixEnd_3225527 := by exact prefixLift 3225527
  have htrace : WordTrace (prefixWord ++ tailWord_3225527) baseStart_3225527 baseEnd_3225527 := by
    simpa [prefixWord, tailWord_3225527, baseEnd_3225527] using wordTrace_append hprefix tailTrace_3225527
  have hstable : (prefixWord ++ tailWord_3225527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225527).length < 2 ^ (prefixWord ++ tailWord_3225527).sum := by decide
  have hdescent : baseEnd_3225527 < baseStart_3225527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225528 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 1, 1, 3]
def baseStart_3225528 : Nat := 118140960795 + 3225528 * 2 ^ 59
def prefixEnd_3225528 : Nat := 4983230072969 + 3 ^ 40 * 3225528 * 2
def baseEnd_3225528 : Nat := 1656246228535561340566073

theorem tailTrace_3225528 : CollatzResearch.WordTrace tailWord_3225528 prefixEnd_3225528 1656246228535561340566073 := by
  unfold tailWord_3225528
  simp only [CollatzResearch.WordTrace]
  refine ⟨58822335529235203585002619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78429780705646938113336825 58822335529235203585002619)
  ·
    refine ⟨88233503293852805377503929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58822335529235203585002619 88233503293852805377503929)
    ·
      refine ⟨66175127470389604033127947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88233503293852805377503929 66175127470389604033127947)
      ·
        refine ⟨99262691205584406049691921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66175127470389604033127947 99262691205584406049691921)
        ·
          refine ⟨74447018404188304537268941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99262691205584406049691921 74447018404188304537268941)
          ·
            refine ⟨27917631901570614201475853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74447018404188304537268941 27917631901570614201475853)
            ·
              refine ⟨10469111963088980325553445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27917631901570614201475853 10469111963088980325553445)
              ·
                refine ⟨1962958493079183811041271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10469111963088980325553445 1962958493079183811041271)
                ·
                  refine ⟨2944437739618775716561907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962958493079183811041271 2944437739618775716561907)
                  ·
                    refine ⟨4416656609428163574842861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2944437739618775716561907 4416656609428163574842861)
                    ·
                      refine ⟨1656246228535561340566073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4416656609428163574842861 1656246228535561340566073)
                      ·
                        rfl

theorem cell23_3225528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 1, 3].length) (baseStart_3225528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225528 prefixEnd_3225528 := by exact prefixLift 3225528
  have htrace : WordTrace (prefixWord ++ tailWord_3225528) baseStart_3225528 baseEnd_3225528 := by
    simpa [prefixWord, tailWord_3225528, baseEnd_3225528] using wordTrace_append hprefix tailTrace_3225528
  have hstable : (prefixWord ++ tailWord_3225528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225528).length < 2 ^ (prefixWord ++ tailWord_3225528).sum := by decide
  have hdescent : baseEnd_3225528 < baseStart_3225528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225544 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3225544 : Nat := 118140960795 + 3225544 * 2 ^ 59
def prefixEnd_3225544 : Nat := 4983230072969 + 3 ^ 40 * 3225544 * 2
def baseEnd_3225544 : Nat := 552084814742011092655333

theorem tailTrace_3225544 : CollatzResearch.WordTrace tailWord_3225544 prefixEnd_3225544 552084814742011092655333 := by
  unfold tailWord_3225544
  simp only [CollatzResearch.WordTrace]
  refine ⟨58822627313206220951293843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78430169750941627935058457 58822627313206220951293843)
  ·
    refine ⟨88233940969809331426940765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58822627313206220951293843 88233940969809331426940765)
    ·
      refine ⟨33087727863678499285102787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88233940969809331426940765 33087727863678499285102787)
      ·
        refine ⟨49631591795517748927654181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33087727863678499285102787 49631591795517748927654181)
        ·
          refine ⟨9305923461659577923935159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49631591795517748927654181 9305923461659577923935159)
          ·
            refine ⟨13958885192489366885902739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305923461659577923935159 13958885192489366885902739)
            ·
              refine ⟨20938327788734050328854109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13958885192489366885902739 20938327788734050328854109)
              ·
                refine ⟨7851872920775268873320291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20938327788734050328854109 7851872920775268873320291)
                ·
                  refine ⟨11777809381162903309980437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851872920775268873320291 11777809381162903309980437)
                  ·
                    refine ⟨552084814742011092655333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11777809381162903309980437 552084814742011092655333)
                    ·
                      rfl

theorem cell23_3225544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3225544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225544 prefixEnd_3225544 := by exact prefixLift 3225544
  have htrace : WordTrace (prefixWord ++ tailWord_3225544) baseStart_3225544 baseEnd_3225544 := by
    simpa [prefixWord, tailWord_3225544, baseEnd_3225544] using wordTrace_append hprefix tailTrace_3225544
  have hstable : (prefixWord ++ tailWord_3225544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225544).length < 2 ^ (prefixWord ++ tailWord_3225544).sum := by decide
  have hdescent : baseEnd_3225544 < baseStart_3225544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225565 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_3225565 : Nat := 118140960795 + 3225565 * 2 ^ 59
def prefixEnd_3225565 : Nat := 4983230072969 + 3 ^ 40 * 3225565 * 2
def baseEnd_3225565 : Nat := 552088409106592565267801

theorem tailTrace_3225565 : CollatzResearch.WordTrace tailWord_3225565 prefixEnd_3225565 552088409106592565267801 := by
  unfold tailWord_3225565
  simp only [CollatzResearch.WordTrace]
  refine ⟨117646020559336362489102149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78430680372890908326068099 117646020559336362489102149)
  ·
    refine ⟨22058628854875567966706653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117646020559336362489102149 22058628854875567966706653)
    ·
      refine ⟨8271985820578337987514995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22058628854875567966706653 8271985820578337987514995)
      ·
        refine ⟨12407978730867506981272493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271985820578337987514995 12407978730867506981272493)
        ·
          refine ⟨4652992024075315117977185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12407978730867506981272493 4652992024075315117977185)
          ·
            refine ⟨3489744018056486338482889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652992024075315117977185 3489744018056486338482889)
            ·
              refine ⟨2617308013542364753862167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3489744018056486338482889 2617308013542364753862167)
              ·
                refine ⟨3925962020313547130793251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617308013542364753862167 3925962020313547130793251)
                ·
                  refine ⟨5888943030470320696189877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925962020313547130793251 5888943030470320696189877)
                  ·
                    refine ⟨552088409106592565267801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5888943030470320696189877 552088409106592565267801)
                    ·
                      rfl

theorem cell23_3225565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_3225565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225565 prefixEnd_3225565 := by exact prefixLift 3225565
  have htrace : WordTrace (prefixWord ++ tailWord_3225565) baseStart_3225565 baseEnd_3225565 := by
    simpa [prefixWord, tailWord_3225565, baseEnd_3225565] using wordTrace_append hprefix tailTrace_3225565
  have hstable : (prefixWord ++ tailWord_3225565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225565).length < 2 ^ (prefixWord ++ tailWord_3225565).sum := by decide
  have hdescent : baseEnd_3225565 < baseStart_3225565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225584 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_3225584 : Nat := 118140960795 + 3225584 * 2 ^ 59
def prefixEnd_3225584 : Nat := 4983230072969 + 3 ^ 40 * 3225584 * 2
def baseEnd_3225584 : Nat := 1656274983452213121465815

theorem tailTrace_3225584 : CollatzResearch.WordTrace tailWord_3225584 prefixEnd_3225584 1656274983452213121465815 := by
  unfold tailWord_3225584
  simp only [CollatzResearch.WordTrace]
  refine ⟨58823356773133764367021903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78431142364178352489362537 58823356773133764367021903)
  ·
    refine ⟨88235035159700646550532855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58823356773133764367021903 88235035159700646550532855)
    ·
      refine ⟨132352552739550969825799283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88235035159700646550532855 132352552739550969825799283)
      ·
        refine ⟨198528829109326454738698925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132352552739550969825799283 198528829109326454738698925)
        ·
          refine ⟨74448310915997420527012097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198528829109326454738698925 74448310915997420527012097)
          ·
            refine ⟨55836233186998065395259073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74448310915997420527012097 55836233186998065395259073)
            ·
              refine ⟨41877174890248549046444305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55836233186998065395259073 41877174890248549046444305)
              ·
                refine ⟨31407881167686411784833229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41877174890248549046444305 31407881167686411784833229)
                ·
                  refine ⟨11777955437882404419312461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31407881167686411784833229 11777955437882404419312461)
                  ·
                    refine ⟨4416733289205901657242173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11777955437882404419312461 4416733289205901657242173)
                    ·
                      refine ⟨1656274983452213121465815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4416733289205901657242173 1656274983452213121465815)
                      ·
                        rfl

theorem cell23_3225584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_3225584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225584 prefixEnd_3225584 := by exact prefixLift 3225584
  have htrace : WordTrace (prefixWord ++ tailWord_3225584) baseStart_3225584 baseEnd_3225584 := by
    simpa [prefixWord, tailWord_3225584, baseEnd_3225584] using wordTrace_append hprefix tailTrace_3225584
  have hstable : (prefixWord ++ tailWord_3225584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225584).length < 2 ^ (prefixWord ++ tailWord_3225584).sum := by decide
  have hdescent : baseEnd_3225584 < baseStart_3225584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225585 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_3225585 : Nat := 118140960795 + 3225585 * 2 ^ 59
def prefixEnd_3225585 : Nat := 4983230072969 + 3 ^ 40 * 3225585 * 2
def baseEnd_3225585 : Nat := 1656275496932867617553311

theorem tailTrace_3225585 : CollatzResearch.WordTrace tailWord_3225585 prefixEnd_3225585 1656275496932867617553311 := by
  unfold tailWord_3225585
  simp only [CollatzResearch.WordTrace]
  refine ⟨117646750019263905904830209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78431166679509270603220139 117646750019263905904830209)
  ·
    refine ⟨88235062514447929428622657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117646750019263905904830209 88235062514447929428622657)
    ·
      refine ⟨66176296885835947071466993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88235062514447929428622657 66176296885835947071466993)
      ·
        refine ⟨49632222664376960303600245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66176296885835947071466993 49632222664376960303600245)
        ·
          refine ⟨4653020874785340028462523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49632222664376960303600245 4653020874785340028462523)
          ·
            refine ⟨6979531312178010042693785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653020874785340028462523 6979531312178010042693785)
            ·
              refine ⟨5234648484133507532020339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979531312178010042693785 5234648484133507532020339)
              ·
                refine ⟨7851972726200261298030509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234648484133507532020339 7851972726200261298030509)
                ·
                  refine ⟨2944489772325097986761441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7851972726200261298030509 2944489772325097986761441)
                  ·
                    refine ⟨2208367329243823490071081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944489772325097986761441 2208367329243823490071081)
                    ·
                      refine ⟨1656275496932867617553311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208367329243823490071081 1656275496932867617553311)
                      ·
                        rfl

theorem cell23_3225585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_3225585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225585 prefixEnd_3225585 := by exact prefixLift 3225585
  have htrace : WordTrace (prefixWord ++ tailWord_3225585) baseStart_3225585 baseEnd_3225585 := by
    simpa [prefixWord, tailWord_3225585, baseEnd_3225585] using wordTrace_append hprefix tailTrace_3225585
  have hstable : (prefixWord ++ tailWord_3225585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225585).length < 2 ^ (prefixWord ++ tailWord_3225585).sum := by decide
  have hdescent : baseEnd_3225585 < baseStart_3225585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225587 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 9]
def baseStart_3225587 : Nat := 118140960795 + 3225587 * 2 ^ 59
def prefixEnd_3225587 : Nat := 4983230072969 + 3 ^ 40 * 3225587 * 2
def baseEnd_3225587 : Nat := 552092174631392203242767

theorem tailTrace_3225587 : CollatzResearch.WordTrace tailWord_3225587 prefixEnd_3225587 552092174631392203242767 := by
  unfold tailWord_3225587
  simp only [CollatzResearch.WordTrace]
  refine ⟨117646822965256660246403015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78431215310171106830935343 117646822965256660246403015)
  ·
    refine ⟨176470234447884990369604523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117646822965256660246403015 176470234447884990369604523)
    ·
      refine ⟨264705351671827485554406785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176470234447884990369604523 264705351671827485554406785)
      ·
        refine ⟨198529013753870614165805089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264705351671827485554406785 198529013753870614165805089)
        ·
          refine ⟨148896760315402960624353817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198529013753870614165805089 148896760315402960624353817)
          ·
            refine ⟨111672570236552220468265363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148896760315402960624353817 111672570236552220468265363)
            ·
              refine ⟨167508855354828330702398045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111672570236552220468265363 167508855354828330702398045)
              ·
                refine ⟨62815820758060624013399267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167508855354828330702398045 62815820758060624013399267)
                ·
                  refine ⟨94223731137090936020098901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62815820758060624013399267 94223731137090936020098901)
                  ·
                    refine ⟨552092174631392203242767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94223731137090936020098901 552092174631392203242767)
                    ·
                      rfl

theorem cell23_3225587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_3225587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225587 prefixEnd_3225587 := by exact prefixLift 3225587
  have htrace : WordTrace (prefixWord ++ tailWord_3225587) baseStart_3225587 baseEnd_3225587 := by
    simpa [prefixWord, tailWord_3225587, baseEnd_3225587] using wordTrace_append hprefix tailTrace_3225587
  have hstable : (prefixWord ++ tailWord_3225587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225587).length < 2 ^ (prefixWord ++ tailWord_3225587).sum := by decide
  have hdescent : baseEnd_3225587 < baseStart_3225587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225598 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3225598 : Nat := 118140960795 + 3225598 * 2 ^ 59
def prefixEnd_3225598 : Nat := 4983230072969 + 3 ^ 40 * 3225598 * 2
def baseEnd_3225598 : Nat := 1656282172181376066690751

theorem tailTrace_3225598 : CollatzResearch.WordTrace tailWord_3225598 prefixEnd_3225598 1656282172181376066690751 := by
  unfold tailWord_3225598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14705903021027101140631681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78431482778811206083368965 14705903021027101140631681)
  ·
    refine ⟨11029427265770325855473761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14705903021027101140631681 11029427265770325855473761)
    ·
      refine ⟨8272070449327744391605321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11029427265770325855473761 8272070449327744391605321)
      ·
        refine ⟨6204052836995808293703991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8272070449327744391605321 6204052836995808293703991)
        ·
          refine ⟨9306079255493712440555987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204052836995808293703991 9306079255493712440555987)
          ·
            refine ⟨13959118883240568660833981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9306079255493712440555987 13959118883240568660833981)
            ·
              refine ⟨5234669581215213247812743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13959118883240568660833981 5234669581215213247812743)
              ·
                refine ⟨7852004371822819871719115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234669581215213247812743 7852004371822819871719115)
                ·
                  refine ⟨11778006557734229807578673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852004371822819871719115 11778006557734229807578673)
                  ·
                    refine ⟨8833504918300672355684005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11778006557734229807578673 8833504918300672355684005)
                    ·
                      refine ⟨1656282172181376066690751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8833504918300672355684005 1656282172181376066690751)
                      ·
                        rfl

theorem cell23_3225598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3225598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225598 prefixEnd_3225598 := by exact prefixLift 3225598
  have htrace : WordTrace (prefixWord ++ tailWord_3225598) baseStart_3225598 baseEnd_3225598 := by
    simpa [prefixWord, tailWord_3225598, baseEnd_3225598] using wordTrace_append hprefix tailTrace_3225598
  have hstable : (prefixWord ++ tailWord_3225598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225598).length < 2 ^ (prefixWord ++ tailWord_3225598).sum := by decide
  have hdescent : baseEnd_3225598 < baseStart_3225598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225613 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3225613 : Nat := 118140960795 + 3225613 * 2 ^ 59
def prefixEnd_3225613 : Nat := 4983230072969 + 3 ^ 40 * 3225613 * 2
def baseEnd_3225613 : Nat := 1656289874391193508003183

theorem tailTrace_3225613 : CollatzResearch.WordTrace tailWord_3225613 prefixEnd_3225613 1656289874391193508003183 := by
  unfold tailWord_3225613
  simp only [CollatzResearch.WordTrace]
  refine ⟨117647771263162466686849493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78431847508774977791232995 117647771263162466686849493)
  ·
    refine ⟨2757369638980370312973035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 117647771263162466686849493 2757369638980370312973035)
    ·
      refine ⟨4136054458470555469459553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757369638980370312973035 4136054458470555469459553)
      ·
        refine ⟨3102040843852916602094665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136054458470555469459553 3102040843852916602094665)
        ·
          refine ⟨2326530632889687451570999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102040843852916602094665 2326530632889687451570999)
          ·
            refine ⟨3489795949334531177356499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326530632889687451570999 3489795949334531177356499)
            ·
              refine ⟨5234693924001796766034749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489795949334531177356499 5234693924001796766034749)
              ·
                refine ⟨1963010221500673787263031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5234693924001796766034749 1963010221500673787263031)
                ·
                  refine ⟨2944515332251010680894547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963010221500673787263031 2944515332251010680894547)
                  ·
                    refine ⟨4416772998376516021341821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2944515332251010680894547 4416772998376516021341821)
                    ·
                      refine ⟨1656289874391193508003183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4416772998376516021341821 1656289874391193508003183)
                      ·
                        rfl

theorem cell23_3225613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3225613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225613 prefixEnd_3225613 := by exact prefixLift 3225613
  have htrace : WordTrace (prefixWord ++ tailWord_3225613) baseStart_3225613 baseEnd_3225613 := by
    simpa [prefixWord, tailWord_3225613, baseEnd_3225613] using wordTrace_append hprefix tailTrace_3225613
  have hstable : (prefixWord ++ tailWord_3225613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225613).length < 2 ^ (prefixWord ++ tailWord_3225613).sum := by decide
  have hdescent : baseEnd_3225613 < baseStart_3225613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225614 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3225614 : Nat := 118140960795 + 3225614 * 2 ^ 59
def prefixEnd_3225614 : Nat := 4983230072969 + 3 ^ 40 * 3225614 * 2
def baseEnd_3225614 : Nat := 1656290387871848004090677

theorem tailTrace_3225614 : CollatzResearch.WordTrace tailWord_3225614 prefixEnd_3225614 1656290387871848004090677 := by
  unfold tailWord_3225614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14705975967019855482204487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78431871824105895905090597 14705975967019855482204487)
  ·
    refine ⟨22058963950529783223306731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14705975967019855482204487 22058963950529783223306731)
    ·
      refine ⟨33088445925794674834960097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22058963950529783223306731 33088445925794674834960097)
      ·
        refine ⟨24816334444346006126220073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33088445925794674834960097 24816334444346006126220073)
        ·
          refine ⟨18612250833259504594665055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24816334444346006126220073 18612250833259504594665055)
          ·
            refine ⟨27918376249889256891997583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18612250833259504594665055 27918376249889256891997583)
            ·
              refine ⟨41877564374833885337996375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27918376249889256891997583 41877564374833885337996375)
              ·
                refine ⟨62816346562250828006994563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41877564374833885337996375 62816346562250828006994563)
                ·
                  refine ⟨94224519843376242010491845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62816346562250828006994563 94224519843376242010491845)
                  ·
                    refine ⟨17667097470633045376967221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94224519843376242010491845 17667097470633045376967221)
                    ·
                      refine ⟨1656290387871848004090677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17667097470633045376967221 1656290387871848004090677)
                      ·
                        rfl

theorem cell23_3225614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3225614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225614 prefixEnd_3225614 := by exact prefixLift 3225614
  have htrace : WordTrace (prefixWord ++ tailWord_3225614) baseStart_3225614 baseEnd_3225614 := by
    simpa [prefixWord, tailWord_3225614, baseEnd_3225614] using wordTrace_append hprefix tailTrace_3225614
  have hstable : (prefixWord ++ tailWord_3225614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225614).length < 2 ^ (prefixWord ++ tailWord_3225614).sum := by decide
  have hdescent : baseEnd_3225614 < baseStart_3225614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225652 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3225652 : Nat := 118140960795 + 3225652 * 2 ^ 59
def prefixEnd_3225652 : Nat := 4983230072969 + 3 ^ 40 * 3225652 * 2
def baseEnd_3225652 : Nat := 1656309900136718855415503

theorem tailTrace_3225652 : CollatzResearch.WordTrace tailWord_3225652 prefixEnd_3225652 1656309900136718855415503 := by
  unfold tailWord_3225652
  simp only [CollatzResearch.WordTrace]
  refine ⟨58824596855010588173759605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78432795806680784231679473 58824596855010588173759605)
  ·
    refine ⟨5514805955157242641289963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58824596855010588173759605 5514805955157242641289963)
    ·
      refine ⟨8272208932735863961934945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5514805955157242641289963 8272208932735863961934945)
      ·
        refine ⟨6204156699551897971451209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8272208932735863961934945 6204156699551897971451209)
        ·
          refine ⟨4653117524663923478588407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6204156699551897971451209 4653117524663923478588407)
          ·
            refine ⟨6979676286995885217882611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653117524663923478588407 6979676286995885217882611)
            ·
              refine ⟨10469514430493827826823917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979676286995885217882611 10469514430493827826823917)
              ·
                refine ⟨3926067911435185435058969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10469514430493827826823917 3926067911435185435058969)
                ·
                  refine ⟨2944550933576389076294227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926067911435185435058969 2944550933576389076294227)
                  ·
                    refine ⟨4416826400364583614441341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2944550933576389076294227 4416826400364583614441341)
                    ·
                      refine ⟨1656309900136718855415503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4416826400364583614441341 1656309900136718855415503)
                      ·
                        rfl

theorem cell23_3225652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3225652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225652 prefixEnd_3225652 := by exact prefixLift 3225652
  have htrace : WordTrace (prefixWord ++ tailWord_3225652) baseStart_3225652 baseEnd_3225652 := by
    simpa [prefixWord, tailWord_3225652, baseEnd_3225652] using wordTrace_append hprefix tailTrace_3225652
  have hstable : (prefixWord ++ tailWord_3225652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225652).length < 2 ^ (prefixWord ++ tailWord_3225652).sum := by decide
  have hdescent : baseEnd_3225652 < baseStart_3225652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225681 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 5]
def baseStart_3225681 : Nat := 118140960795 + 3225681 * 2 ^ 59
def prefixEnd_3225681 : Nat := 4983230072969 + 3 ^ 40 * 3225681 * 2
def baseEnd_3225681 : Nat := 184036087897299915772541

theorem tailTrace_3225681 : CollatzResearch.WordTrace tailWord_3225681 prefixEnd_3225681 184036087897299915772541 := by
  unfold tailWord_3225681
  simp only [CollatzResearch.WordTrace]
  refine ⟨117650251426916114300324897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78433500951277409533549931 117650251426916114300324897)
  ·
    refine ⟨88237688570187085725243673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117650251426916114300324897 88237688570187085725243673)
    ·
      refine ⟨66178266427640314293932755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88237688570187085725243673 66178266427640314293932755)
      ·
        refine ⟨99267399641460471440899133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66178266427640314293932755 99267399641460471440899133)
        ·
          refine ⟨37225274865547676790337175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99267399641460471440899133 37225274865547676790337175)
          ·
            refine ⟨55837912298321515185505763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37225274865547676790337175 55837912298321515185505763)
            ·
              refine ⟨83756868447482272778258645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55837912298321515185505763 83756868447482272778258645)
              ·
                refine ⟨1963051604237865768240437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83756868447482272778258645 1963051604237865768240437)
                ·
                  refine ⟨184036087897299915772541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1963051604237865768240437 184036087897299915772541)
                  ·
                    rfl

theorem cell23_3225681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 5].length) (baseStart_3225681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225681 prefixEnd_3225681 := by exact prefixLift 3225681
  have htrace : WordTrace (prefixWord ++ tailWord_3225681) baseStart_3225681 baseEnd_3225681 := by
    simpa [prefixWord, tailWord_3225681, baseEnd_3225681] using wordTrace_append hprefix tailTrace_3225681
  have hstable : (prefixWord ++ tailWord_3225681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225681).length < 2 ^ (prefixWord ++ tailWord_3225681).sum := by decide
  have hdescent : baseEnd_3225681 < baseStart_3225681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225692 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_3225692 : Nat := 118140960795 + 3225692 * 2 ^ 59
def prefixEnd_3225692 : Nat := 4983230072969 + 3 ^ 40 * 3225692 * 2
def baseEnd_3225692 : Nat := 1656330439362898698915319

theorem tailTrace_3225692 : CollatzResearch.WordTrace tailWord_3225692 prefixEnd_3225692 1656330439362898698915319 := by
  unfold tailWord_3225692
  simp only [CollatzResearch.WordTrace]
  refine ⟨58825326314938131589487665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78433768419917508785983553 58825326314938131589487665)
  ·
    refine ⟨44118994736203598692115749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58825326314938131589487665 44118994736203598692115749)
    ·
      refine ⟨8272311513038174754771703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44118994736203598692115749 8272311513038174754771703)
      ·
        refine ⟨12408467269557262132157555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272311513038174754771703 12408467269557262132157555)
        ·
          refine ⟨18612700904335893198236333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12408467269557262132157555 18612700904335893198236333)
          ·
            refine ⟨6979762839125959949338625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18612700904335893198236333 6979762839125959949338625)
            ·
              refine ⟨5234822129344469962003969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979762839125959949338625 5234822129344469962003969)
              ·
                refine ⟨3926116597008352471502977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5234822129344469962003969 3926116597008352471502977)
                ·
                  refine ⟨2944587447756264353627233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926116597008352471502977 2944587447756264353627233)
                  ·
                    refine ⟨2208440585817198265220425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944587447756264353627233 2208440585817198265220425)
                    ·
                      refine ⟨1656330439362898698915319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208440585817198265220425 1656330439362898698915319)
                      ·
                        rfl

theorem cell23_3225692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_3225692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225692 prefixEnd_3225692 := by exact prefixLift 3225692
  have htrace : WordTrace (prefixWord ++ tailWord_3225692) baseStart_3225692 baseEnd_3225692 := by
    simpa [prefixWord, tailWord_3225692, baseEnd_3225692] using wordTrace_append hprefix tailTrace_3225692
  have hstable : (prefixWord ++ tailWord_3225692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225692).length < 2 ^ (prefixWord ++ tailWord_3225692).sum := by decide
  have hdescent : baseEnd_3225692 < baseStart_3225692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225731 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4]
def baseStart_3225731 : Nat := 118140960795 + 3225731 * 2 ^ 59
def prefixEnd_3225731 : Nat := 4983230072969 + 3 ^ 40 * 3225731 * 2
def baseEnd_3225731 : Nat := 1656350465108424046327639

theorem tailTrace_3225731 : CollatzResearch.WordTrace tailWord_3225731 prefixEnd_3225731 1656350465108424046327639 := by
  unfold tailWord_3225731
  simp only [CollatzResearch.WordTrace]
  refine ⟨117652075076734972839645047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78434716717823315226430031 117652075076734972839645047)
  ·
    refine ⟨176478112615102459259467571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117652075076734972839645047 176478112615102459259467571)
    ·
      refine ⟨264717168922653688889201357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176478112615102459259467571 264717168922653688889201357)
      ·
        refine ⟨99268938345995133333450509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264717168922653688889201357 99268938345995133333450509)
        ·
          refine ⟨37225851879748175000043941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99268938345995133333450509 37225851879748175000043941)
          ·
            refine ⟨6979847227452782812508239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37225851879748175000043941 6979847227452782812508239)
            ·
              refine ⟨10469770841179174218762359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6979847227452782812508239 10469770841179174218762359)
              ·
                refine ⟨15704656261768761328143539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10469770841179174218762359 15704656261768761328143539)
                ·
                  refine ⟨23556984392653141992215309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15704656261768761328143539 23556984392653141992215309)
                  ·
                    refine ⟨8833869147244928247080741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23556984392653141992215309 8833869147244928247080741)
                    ·
                      refine ⟨1656350465108424046327639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8833869147244928247080741 1656350465108424046327639)
                      ·
                        rfl

theorem cell23_3225731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_3225731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225731 prefixEnd_3225731 := by exact prefixLift 3225731
  have htrace : WordTrace (prefixWord ++ tailWord_3225731) baseStart_3225731 baseEnd_3225731 := by
    simpa [prefixWord, tailWord_3225731, baseEnd_3225731] using wordTrace_append hprefix tailTrace_3225731
  have hstable : (prefixWord ++ tailWord_3225731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225731).length < 2 ^ (prefixWord ++ tailWord_3225731).sum := by decide
  have hdescent : baseEnd_3225731 < baseStart_3225731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225744 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_3225744 : Nat := 118140960795 + 3225744 * 2 ^ 59
def prefixEnd_3225744 : Nat := 4983230072969 + 3 ^ 40 * 3225744 * 2
def baseEnd_3225744 : Nat := 1656357140356932495465079

theorem tailTrace_3225744 : CollatzResearch.WordTrace tailWord_3225744 prefixEnd_3225744 1656357140356932495465079 := by
  unfold tailWord_3225744
  simp only [CollatzResearch.WordTrace]
  refine ⟨58826274612843938029934143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78435032817125250706578857 58826274612843938029934143)
  ·
    refine ⟨88239411919265907044901215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58826274612843938029934143 88239411919265907044901215)
    ·
      refine ⟨132359117878898860567351823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88239411919265907044901215 132359117878898860567351823)
      ·
        refine ⟨198538676818348290851027735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132359117878898860567351823 198538676818348290851027735)
        ·
          refine ⟨297808015227522436276541603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198538676818348290851027735 297808015227522436276541603)
          ·
            refine ⟨446712022841283654414812405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297808015227522436276541603 446712022841283654414812405)
            ·
              refine ⟨41879252141370342601388663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 446712022841283654414812405 41879252141370342601388663)
              ·
                refine ⟨62818878212055513902082995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41879252141370342601388663 62818878212055513902082995)
                ·
                  refine ⟨94228317318083270853124493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62818878212055513902082995 94228317318083270853124493)
                  ·
                    refine ⟨35335618994281226569921685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94228317318083270853124493 35335618994281226569921685)
                    ·
                      refine ⟨1656357140356932495465079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35335618994281226569921685 1656357140356932495465079)
                      ·
                        rfl

theorem cell23_3225744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_3225744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225744 prefixEnd_3225744 := by exact prefixLift 3225744
  have htrace : WordTrace (prefixWord ++ tailWord_3225744) baseStart_3225744 baseEnd_3225744 := by
    simpa [prefixWord, tailWord_3225744, baseEnd_3225744] using wordTrace_append hprefix tailTrace_3225744
  have hstable : (prefixWord ++ tailWord_3225744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225744).length < 2 ^ (prefixWord ++ tailWord_3225744).sum := by decide
  have hdescent : baseEnd_3225744 < baseStart_3225744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225792 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 1, 4]
def baseStart_3225792 : Nat := 118140960795 + 3225792 * 2 ^ 59
def prefixEnd_3225792 : Nat := 4983230072969 + 3 ^ 40 * 3225792 * 2
def baseEnd_3225792 : Nat := 552127262476116102554953

theorem tailTrace_3225792 : CollatzResearch.WordTrace tailWord_3225792 prefixEnd_3225792 552127262476116102554953 := by
  unfold tailWord_3225792
  simp only [CollatzResearch.WordTrace]
  refine ⟨58827149964756990128807815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78436199953009320171743753 58827149964756990128807815)
  ·
    refine ⟨88240724947135485193211723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58827149964756990128807815 88240724947135485193211723)
    ·
      refine ⟨132361087420703227789817585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88240724947135485193211723 132361087420703227789817585)
      ·
        refine ⟨99270815565527420842363189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132361087420703227789817585 99270815565527420842363189)
        ·
          refine ⟨9306638959268195703971549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99270815565527420842363189 9306638959268195703971549)
          ·
            refine ⟨3489989609725573388989331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9306638959268195703971549 3489989609725573388989331)
            ·
              refine ⟨5234984414588360083483997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489989609725573388989331 5234984414588360083483997)
              ·
                refine ⟨1963119155470635031306499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5234984414588360083483997 1963119155470635031306499)
                ·
                  refine ⟨2944678733205952546959749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963119155470635031306499 2944678733205952546959749)
                  ·
                    refine ⟨552127262476116102554953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944678733205952546959749 552127262476116102554953)
                    ·
                      rfl

theorem cell23_3225792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 4].length) (baseStart_3225792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225792 prefixEnd_3225792 := by exact prefixLift 3225792
  have htrace : WordTrace (prefixWord ++ tailWord_3225792) baseStart_3225792 baseEnd_3225792 := by
    simpa [prefixWord, tailWord_3225792, baseEnd_3225792] using wordTrace_append hprefix tailTrace_3225792
  have hstable : (prefixWord ++ tailWord_3225792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225792).length < 2 ^ (prefixWord ++ tailWord_3225792).sum := by decide
  have hdescent : baseEnd_3225792 < baseStart_3225792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225841 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3225841 : Nat := 118140960795 + 3225841 * 2 ^ 59
def prefixEnd_3225841 : Nat := 4983230072969 + 3 ^ 40 * 3225841 * 2
def baseEnd_3225841 : Nat := 1656406947980418615952133

theorem tailTrace_3225841 : CollatzResearch.WordTrace tailWord_3225841 prefixEnd_3225841 1656406947980418615952133 := by
  unfold tailWord_3225841
  simp only [CollatzResearch.WordTrace]
  refine ⟨117656087106336461626149377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78437391404224307750766251 117656087106336461626149377)
  ·
    refine ⟨88242065329752346219612033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117656087106336461626149377 88242065329752346219612033)
    ·
      refine ⟨66181548997314259664709025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88242065329752346219612033 66181548997314259664709025)
      ·
        refine ⟨49636161747985694748531769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66181548997314259664709025 49636161747985694748531769)
        ·
          refine ⟨37227121310989271061398827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49636161747985694748531769 37227121310989271061398827)
          ·
            refine ⟨55840681966483906592098241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37227121310989271061398827 55840681966483906592098241)
            ·
              refine ⟨41880511474862929944073681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55840681966483906592098241 41880511474862929944073681)
              ·
                refine ⟨31410383606147197458055261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41880511474862929944073681 31410383606147197458055261)
                ·
                  refine ⟨11778893852305199046770723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31410383606147197458055261 11778893852305199046770723)
                  ·
                    refine ⟨17668340778457798570156085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11778893852305199046770723 17668340778457798570156085)
                    ·
                      refine ⟨1656406947980418615952133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17668340778457798570156085 1656406947980418615952133)
                      ·
                        rfl

theorem cell23_3225841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3225841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225841 prefixEnd_3225841 := by exact prefixLift 3225841
  have htrace : WordTrace (prefixWord ++ tailWord_3225841) baseStart_3225841 baseEnd_3225841 := by
    simpa [prefixWord, tailWord_3225841, baseEnd_3225841] using wordTrace_append hprefix tailTrace_3225841
  have hstable : (prefixWord ++ tailWord_3225841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225841).length < 2 ^ (prefixWord ++ tailWord_3225841).sum := by decide
  have hdescent : baseEnd_3225841 < baseStart_3225841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225842 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3225842 : Nat := 118140960795 + 3225842 * 2 ^ 59
def prefixEnd_3225842 : Nat := 4983230072969 + 3 ^ 40 * 3225842 * 2
def baseEnd_3225842 : Nat := 1656407461461073112039629

theorem tailTrace_3225842 : CollatzResearch.WordTrace tailWord_3225842 prefixEnd_3225842 1656407461461073112039629 := by
  unfold tailWord_3225842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29414030894833209699233945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78437415719555225864623853 29414030894833209699233945)
  ·
    refine ⟨22060523171124907274425459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29414030894833209699233945 22060523171124907274425459)
    ·
      refine ⟨33090784756687360911638189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22060523171124907274425459 33090784756687360911638189)
      ·
        refine ⟨12409044283757760341864321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33090784756687360911638189 12409044283757760341864321)
        ·
          refine ⟨9306783212818320256398241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12409044283757760341864321 9306783212818320256398241)
          ·
            refine ⟨6980087409613740192298681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306783212818320256398241 6980087409613740192298681)
            ·
              refine ⟨5235065557210305144224011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980087409613740192298681 5235065557210305144224011)
              ·
                refine ⟨7852598335815457716336017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235065557210305144224011 7852598335815457716336017)
                ·
                  refine ⟨5889448751861593287252013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7852598335815457716336017 5889448751861593287252013)
                  ·
                    refine ⟨2208543281948097482719505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5889448751861593287252013 2208543281948097482719505)
                    ·
                      refine ⟨1656407461461073112039629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208543281948097482719505 1656407461461073112039629)
                      ·
                        rfl

theorem cell23_3225842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3225842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225842 prefixEnd_3225842 := by exact prefixLift 3225842
  have htrace : WordTrace (prefixWord ++ tailWord_3225842) baseStart_3225842 baseEnd_3225842 := by
    simpa [prefixWord, tailWord_3225842, baseEnd_3225842] using wordTrace_append hprefix tailTrace_3225842
  have hstable : (prefixWord ++ tailWord_3225842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225842).length < 2 ^ (prefixWord ++ tailWord_3225842).sum := by decide
  have hdescent : baseEnd_3225842 < baseStart_3225842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225855 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 1, 1, 4]
def baseStart_3225855 : Nat := 118140960795 + 3225855 * 2 ^ 59
def prefixEnd_3225855 : Nat := 4983230072969 + 3 ^ 40 * 3225855 * 2
def baseEnd_3225855 : Nat := 1656414136709581561177069

theorem tailTrace_3225855 : CollatzResearch.WordTrace tailWord_3225855 prefixEnd_3225855 1656414136709581561177069 := by
  unfold tailWord_3225855
  simp only [CollatzResearch.WordTrace]
  refine ⟨117656597728285742017159019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78437731818857161344772679 117656597728285742017159019)
  ·
    refine ⟨176484896592428613025738529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117656597728285742017159019 176484896592428613025738529)
    ·
      refine ⟨132363672444321459769303897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176484896592428613025738529 132363672444321459769303897)
      ·
        refine ⟨99272754333241094826977923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132363672444321459769303897 99272754333241094826977923)
        ·
          refine ⟨148909131499861642240466885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99272754333241094826977923 148909131499861642240466885)
          ·
            refine ⟨27920462156224057920087541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148909131499861642240466885 27920462156224057920087541)
            ·
              refine ⟨2617543327146005430008207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27920462156224057920087541 2617543327146005430008207)
              ·
                refine ⟨3926314990719008145012311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617543327146005430008207 3926314990719008145012311)
                ·
                  refine ⟨5889472486078512217518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926314990719008145012311 5889472486078512217518467)
                  ·
                    refine ⟨8834208729117768326277701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5889472486078512217518467 8834208729117768326277701)
                    ·
                      refine ⟨1656414136709581561177069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8834208729117768326277701 1656414136709581561177069)
                      ·
                        rfl

theorem cell23_3225855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_3225855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225855 prefixEnd_3225855 := by exact prefixLift 3225855
  have htrace : WordTrace (prefixWord ++ tailWord_3225855) baseStart_3225855 baseEnd_3225855 := by
    simpa [prefixWord, tailWord_3225855, baseEnd_3225855] using wordTrace_append hprefix tailTrace_3225855
  have hstable : (prefixWord ++ tailWord_3225855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225855).length < 2 ^ (prefixWord ++ tailWord_3225855).sum := by decide
  have hdescent : baseEnd_3225855 < baseStart_3225855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225865 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_3225865 : Nat := 118140960795 + 3225865 * 2 ^ 59
def prefixEnd_3225865 : Nat := 4983230072969 + 3 ^ 40 * 3225865 * 2
def baseEnd_3225865 : Nat := 552139757172042174017341

theorem tailTrace_3225865 : CollatzResearch.WordTrace tailWord_3225865 prefixEnd_3225865 552139757172042174017341 := by
  unfold tailWord_3225865
  simp only [CollatzResearch.WordTrace]
  refine ⟨117656962458249513725023049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78437974972166342483348699 117656962458249513725023049)
  ·
    refine ⟨88242721843687135293767287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117656962458249513725023049 88242721843687135293767287)
    ·
      refine ⟨132364082765530702940650931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88242721843687135293767287 132364082765530702940650931)
      ·
        refine ⟨198546124148296054410976397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132364082765530702940650931 198546124148296054410976397)
        ·
          refine ⟨74454796555611020404116149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198546124148296054410976397 74454796555611020404116149)
          ·
            refine ⟨6980137177088533162885889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74454796555611020404116149 6980137177088533162885889)
            ·
              refine ⟨5235102882816399872164417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980137177088533162885889 5235102882816399872164417)
              ·
                refine ⟨3926327162112299904123313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5235102882816399872164417 3926327162112299904123313)
                ·
                  refine ⟨2944745371584224928092485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926327162112299904123313 2944745371584224928092485)
                  ·
                    refine ⟨552139757172042174017341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944745371584224928092485 552139757172042174017341)
                    ·
                      rfl

theorem cell23_3225865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_3225865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225865 prefixEnd_3225865 := by exact prefixLift 3225865
  have htrace : WordTrace (prefixWord ++ tailWord_3225865) baseStart_3225865 baseEnd_3225865 := by
    simpa [prefixWord, tailWord_3225865, baseEnd_3225865] using wordTrace_append hprefix tailTrace_3225865
  have hstable : (prefixWord ++ tailWord_3225865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225865).length < 2 ^ (prefixWord ++ tailWord_3225865).sum := by decide
  have hdescent : baseEnd_3225865 < baseStart_3225865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225891 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 7]
def baseStart_3225891 : Nat := 118140960795 + 3225891 * 2 ^ 59
def prefixEnd_3225891 : Nat := 4983230072969 + 3 ^ 40 * 3225891 * 2
def baseEnd_3225891 : Nat := 552144207337714473442301

theorem tailTrace_3225891 : CollatzResearch.WordTrace tailWord_3225891 prefixEnd_3225891 552144207337714473442301 := by
  unfold tailWord_3225891
  simp only [CollatzResearch.WordTrace]
  refine ⟨117657910756155320165469527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78438607170770213443646351 117657910756155320165469527)
  ·
    refine ⟨176486866134232980248204291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117657910756155320165469527 176486866134232980248204291)
    ·
      refine ⟨264730299201349470372306437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176486866134232980248204291 264730299201349470372306437)
      ·
        refine ⟨49636931100253025694807457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264730299201349470372306437 49636931100253025694807457)
        ·
          refine ⟨37227698325189769271105593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49636931100253025694807457 37227698325189769271105593)
          ·
            refine ⟨27920773743892326953329195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37227698325189769271105593 27920773743892326953329195)
            ·
              refine ⟨41881160615838490429993793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27920773743892326953329195 41881160615838490429993793)
              ·
                refine ⟨31410870461878867822495345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41881160615838490429993793 31410870461878867822495345)
                ·
                  refine ⟨23558152846409150866871509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31410870461878867822495345 23558152846409150866871509)
                  ·
                    refine ⟨552144207337714473442301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23558152846409150866871509 552144207337714473442301)
                    ·
                      rfl

theorem cell23_3225891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_3225891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225891 prefixEnd_3225891 := by exact prefixLift 3225891
  have htrace : WordTrace (prefixWord ++ tailWord_3225891) baseStart_3225891 baseEnd_3225891 := by
    simpa [prefixWord, tailWord_3225891, baseEnd_3225891] using wordTrace_append hprefix tailTrace_3225891
  have hstable : (prefixWord ++ tailWord_3225891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225891).length < 2 ^ (prefixWord ++ tailWord_3225891).sum := by decide
  have hdescent : baseEnd_3225891 < baseStart_3225891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225906 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_3225906 : Nat := 118140960795 + 3225906 * 2 ^ 59
def prefixEnd_3225906 : Nat := 4983230072969 + 3 ^ 40 * 3225906 * 2
def baseEnd_3225906 : Nat := 1656440324222960861639335

theorem tailTrace_3225906 : CollatzResearch.WordTrace tailWord_3225906 prefixEnd_3225906 1656440324222960861639335 := by
  unfold tailWord_3225906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29414614462775244431816393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78438971900733985151510381 29414614462775244431816393)
  ·
    refine ⟨22060960847081433323862295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29414614462775244431816393 22060960847081433323862295)
    ·
      refine ⟨33091441270622149985793443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22060960847081433323862295 33091441270622149985793443)
      ·
        refine ⟨49637161905933224978690165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33091441270622149985793443 49637161905933224978690165)
        ·
          refine ⟨4653483928681239841752203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49637161905933224978690165 4653483928681239841752203)
          ·
            refine ⟨6980225893021859762628305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653483928681239841752203 6980225893021859762628305)
            ·
              refine ⟨5235169419766394821971229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980225893021859762628305 5235169419766394821971229)
              ·
                refine ⟨1963188532412398058239211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235169419766394821971229 1963188532412398058239211)
                ·
                  refine ⟨2944782798618597087358817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963188532412398058239211 2944782798618597087358817)
                  ·
                    refine ⟨2208587098963947815519113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944782798618597087358817 2208587098963947815519113)
                    ·
                      refine ⟨1656440324222960861639335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208587098963947815519113 1656440324222960861639335)
                      ·
                        rfl

theorem cell23_3225906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_3225906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225906 prefixEnd_3225906 := by exact prefixLift 3225906
  have htrace : WordTrace (prefixWord ++ tailWord_3225906) baseStart_3225906 baseEnd_3225906 := by
    simpa [prefixWord, tailWord_3225906, baseEnd_3225906] using wordTrace_append hprefix tailTrace_3225906
  have hstable : (prefixWord ++ tailWord_3225906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225906).length < 2 ^ (prefixWord ++ tailWord_3225906).sum := by decide
  have hdescent : baseEnd_3225906 < baseStart_3225906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225931 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_3225931 : Nat := 118140960795 + 3225931 * 2 ^ 59
def prefixEnd_3225931 : Nat := 4983230072969 + 3 ^ 40 * 3225931 * 2
def baseEnd_3225931 : Nat := 1656453161239323263826719

theorem tailTrace_3225931 : CollatzResearch.WordTrace tailWord_3225931 prefixEnd_3225931 1656453161239323263826719 := by
  unfold tailWord_3225931
  simp only [CollatzResearch.WordTrace]
  refine ⟨117659369676010406996925647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78439579784006937997950431 117659369676010406996925647)
  ·
    refine ⟨176489054514015610495388471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117659369676010406996925647 176489054514015610495388471)
    ·
      refine ⟨264733581771023415743082707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176489054514015610495388471 264733581771023415743082707)
      ·
        refine ⟨397100372656535123614624061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264733581771023415743082707 397100372656535123614624061)
        ·
          refine ⟨148912639746200671355484023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397100372656535123614624061 148912639746200671355484023)
          ·
            refine ⟨223368959619301007033226035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148912639746200671355484023 223368959619301007033226035)
            ·
              refine ⟨335053439428951510549839053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223368959619301007033226035 335053439428951510549839053)
              ·
                refine ⟨125645039785856816456189645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335053439428951510549839053 125645039785856816456189645)
                ·
                  refine ⟨47116889919696306171071117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125645039785856816456189645 47116889919696306171071117)
                  ·
                    refine ⟨17668833719886114814151669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47116889919696306171071117 17668833719886114814151669)
                    ·
                      refine ⟨1656453161239323263826719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17668833719886114814151669 1656453161239323263826719)
                      ·
                        rfl

theorem cell23_3225931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_3225931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225931 prefixEnd_3225931 := by exact prefixLift 3225931
  have htrace : WordTrace (prefixWord ++ tailWord_3225931) baseStart_3225931 baseEnd_3225931 := by
    simpa [prefixWord, tailWord_3225931, baseEnd_3225931] using wordTrace_append hprefix tailTrace_3225931
  have hstable : (prefixWord ++ tailWord_3225931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225931).length < 2 ^ (prefixWord ++ tailWord_3225931).sum := by decide
  have hdescent : baseEnd_3225931 < baseStart_3225931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225938 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3225938 : Nat := 118140960795 + 3225938 * 2 ^ 59
def prefixEnd_3225938 : Nat := 4983230072969 + 3 ^ 40 * 3225938 * 2
def baseEnd_3225938 : Nat := 552152251867968245479729

theorem tailTrace_3225938 : CollatzResearch.WordTrace tailWord_3225938 prefixEnd_3225938 552152251867968245479729 := by
  unfold tailWord_3225938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29414906246746261798107617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78439749991323364794953645 29414906246746261798107617)
  ·
    refine ⟨22061179685059696348580713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29414906246746261798107617 22061179685059696348580713)
    ·
      refine ⟨16545884763794772261435535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22061179685059696348580713 16545884763794772261435535)
      ·
        refine ⟨24818827145692158392153303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16545884763794772261435535 24818827145692158392153303)
        ·
          refine ⟨37228240718538237588229955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24818827145692158392153303 37228240718538237588229955)
          ·
            refine ⟨55842361077807356382344933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37228240718538237588229955 55842361077807356382344933)
            ·
              refine ⟨10470442702088879321689675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55842361077807356382344933 10470442702088879321689675)
              ·
                refine ⟨15705664053133318982534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470442702088879321689675 15705664053133318982534513)
                ·
                  refine ⟨11779248039849989236900885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15705664053133318982534513 11779248039849989236900885)
                  ·
                    refine ⟨552152251867968245479729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11779248039849989236900885 552152251867968245479729)
                    ·
                      rfl

theorem cell23_3225938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3225938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225938 prefixEnd_3225938 := by exact prefixLift 3225938
  have htrace : WordTrace (prefixWord ++ tailWord_3225938) baseStart_3225938 baseEnd_3225938 := by
    simpa [prefixWord, tailWord_3225938, baseEnd_3225938] using wordTrace_append hprefix tailTrace_3225938
  have hstable : (prefixWord ++ tailWord_3225938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225938).length < 2 ^ (prefixWord ++ tailWord_3225938).sum := by decide
  have hdescent : baseEnd_3225938 < baseStart_3225938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225985 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 7]
def baseStart_3225985 : Nat := 118140960795 + 3225985 * 2 ^ 59
def prefixEnd_3225985 : Nat := 4983230072969 + 3 ^ 40 * 3225985 * 2
def baseEnd_3225985 : Nat := 184053432132740672505719

theorem tailTrace_3225985 : CollatzResearch.WordTrace tailWord_3225985 prefixEnd_3225985 184053432132740672505719 := by
  unfold tailWord_3225985
  simp only [CollatzResearch.WordTrace]
  refine ⟨117661339217814774219391409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78440892811876516146260939 117661339217814774219391409)
  ·
    refine ⟨88246004413361080664543557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117661339217814774219391409 88246004413361080664543557)
    ·
      refine ⟨16546125827505202624601917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88246004413361080664543557 16546125827505202624601917)
      ·
        refine ⟨6204797185314450984225719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16546125827505202624601917 6204797185314450984225719)
        ·
          refine ⟨9307195777971676476338579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204797185314450984225719 9307195777971676476338579)
          ·
            refine ⟨13960793666957514714507869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9307195777971676476338579 13960793666957514714507869)
            ·
              refine ⟨5235297625109068017940451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13960793666957514714507869 5235297625109068017940451)
              ·
                refine ⟨7852946437663602026910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235297625109068017940451 7852946437663602026910677)
                ·
                  refine ⟨184053432132740672505719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7852946437663602026910677 184053432132740672505719)
                  ·
                    rfl

theorem cell23_3225985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_3225985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225985 prefixEnd_3225985 := by exact prefixLift 3225985
  have htrace : WordTrace (prefixWord ++ tailWord_3225985) baseStart_3225985 baseEnd_3225985 := by
    simpa [prefixWord, tailWord_3225985, baseEnd_3225985] using wordTrace_append hprefix tailTrace_3225985
  have hstable : (prefixWord ++ tailWord_3225985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225985).length < 2 ^ (prefixWord ++ tailWord_3225985).sum := by decide
  have hdescent : baseEnd_3225985 < baseStart_3225985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3225996 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_3225996 : Nat := 118140960795 + 3225996 * 2 ^ 59
def prefixEnd_3225996 : Nat := 4983230072969 + 3 ^ 40 * 3225996 * 2
def baseEnd_3225996 : Nat := 1656486537481865509513921

theorem tailTrace_3225996 : CollatzResearch.WordTrace tailWord_3225996 prefixEnd_3225996 1656486537481865509513921 := by
  unfold tailWord_3225996
  simp only [CollatzResearch.WordTrace]
  refine ⟨58830870210387461549020921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78441160280516615398694561 58830870210387461549020921)
  ·
    refine ⟨44123152657790596161765691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58830870210387461549020921 44123152657790596161765691)
    ·
      refine ⟨66184728986685894242648537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44123152657790596161765691 66184728986685894242648537)
      ·
        refine ⟨49638546740014420681986403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66184728986685894242648537 49638546740014420681986403)
        ·
          refine ⟨74457820110021631022979605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49638546740014420681986403 74457820110021631022979605)
          ·
            refine ⟨3490210317657263954202169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74457820110021631022979605 3490210317657263954202169)
            ·
              refine ⟨2617657738242947965651627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3490210317657263954202169 2617657738242947965651627)
              ·
                refine ⟨3926486607364421948477441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617657738242947965651627 3926486607364421948477441)
                ·
                  refine ⟨2944864955523316461358081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926486607364421948477441 2944864955523316461358081)
                  ·
                    refine ⟨2208648716642487346018561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944864955523316461358081 2208648716642487346018561)
                    ·
                      refine ⟨1656486537481865509513921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208648716642487346018561 1656486537481865509513921)
                      ·
                        rfl

theorem cell23_3225996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_3225996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3225996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3225996 prefixEnd_3225996 := by exact prefixLift 3225996
  have htrace : WordTrace (prefixWord ++ tailWord_3225996) baseStart_3225996 baseEnd_3225996 := by
    simpa [prefixWord, tailWord_3225996, baseEnd_3225996] using wordTrace_append hprefix tailTrace_3225996
  have hstable : (prefixWord ++ tailWord_3225996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3225996).length < 2 ^ (prefixWord ++ tailWord_3225996).sum := by decide
  have hdescent : baseEnd_3225996 < baseStart_3225996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3225996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226015 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 2, 5]
def baseStart_3226015 : Nat := 118140960795 + 3226015 * 2 ^ 59
def prefixEnd_3226015 : Nat := 4983230072969 + 3 ^ 40 * 3226015 * 2
def baseEnd_3226015 : Nat := 552165431204766978392111

theorem tailTrace_3226015 : CollatzResearch.WordTrace tailWord_3226015 prefixEnd_3226015 552165431204766978392111 := by
  unfold tailWord_3226015
  simp only [CollatzResearch.WordTrace]
  refine ⟨117662433407706089342983499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78441622271804059561988999 117662433407706089342983499)
  ·
    refine ⟨176493650111559134014475249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117662433407706089342983499 176493650111559134014475249)
    ·
      refine ⟨132370237583669350510856437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176493650111559134014475249 132370237583669350510856437)
      ·
        refine ⟨12409709773469001610392791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132370237583669350510856437 12409709773469001610392791)
        ·
          refine ⟨18614564660203502415589187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409709773469001610392791 18614564660203502415589187)
          ·
            refine ⟨27921846990305253623383781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18614564660203502415589187 27921846990305253623383781)
            ·
              refine ⟨5235346310682235054384459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27921846990305253623383781 5235346310682235054384459)
              ·
                refine ⟨7853019466023352581576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235346310682235054384459 7853019466023352581576689)
                ·
                  refine ⟨5889764599517514436182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853019466023352581576689 5889764599517514436182517)
                  ·
                    refine ⟨552165431204766978392111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5889764599517514436182517 552165431204766978392111)
                    ·
                      rfl

theorem cell23_3226015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_3226015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226015 prefixEnd_3226015 := by exact prefixLift 3226015
  have htrace : WordTrace (prefixWord ++ tailWord_3226015) baseStart_3226015 baseEnd_3226015 := by
    simpa [prefixWord, tailWord_3226015, baseEnd_3226015] using wordTrace_append hprefix tailTrace_3226015
  have hstable : (prefixWord ++ tailWord_3226015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226015).length < 2 ^ (prefixWord ++ tailWord_3226015).sum := by decide
  have hdescent : baseEnd_3226015 < baseStart_3226015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226036 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3226036 : Nat := 118140960795 + 3226036 * 2 ^ 59
def prefixEnd_3226036 : Nat := 4983230072969 + 3 ^ 40 * 3226036 * 2
def baseEnd_3226036 : Nat := 184056341856449483668193

theorem tailTrace_3226036 : CollatzResearch.WordTrace tailWord_3226036 prefixEnd_3226036 184056341856449483668193 := by
  unfold tailWord_3226036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58831599670315004964748981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78442132893753339952998641 58831599670315004964748981)
  ·
    refine ⟨5515462469092031715445217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58831599670315004964748981 5515462469092031715445217)
    ·
      refine ⟨4136596851819023786583913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5515462469092031715445217 4136596851819023786583913)
      ·
        refine ⟨3102447638864267839937935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136596851819023786583913 3102447638864267839937935)
        ·
          refine ⟨4653671458296401759906903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102447638864267839937935 4653671458296401759906903)
          ·
            refine ⟨6980507187444602639860355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653671458296401759906903 6980507187444602639860355)
            ·
              refine ⟨10470760781166903959790533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980507187444602639860355 10470760781166903959790533)
              ·
                refine ⟨1963267646468794492460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10470760781166903959790533 1963267646468794492460725)
                ·
                  refine ⟨184056341856449483668193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1963267646468794492460725 184056341856449483668193)
                  ·
                    rfl

theorem cell23_3226036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3226036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226036 prefixEnd_3226036 := by exact prefixLift 3226036
  have htrace : WordTrace (prefixWord ++ tailWord_3226036) baseStart_3226036 baseEnd_3226036 := by
    simpa [prefixWord, tailWord_3226036, baseEnd_3226036] using wordTrace_append hprefix tailTrace_3226036
  have hstable : (prefixWord ++ tailWord_3226036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226036).length < 2 ^ (prefixWord ++ tailWord_3226036).sum := by decide
  have hdescent : baseEnd_3226036 < baseStart_3226036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226048 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_3226048 : Nat := 118140960795 + 3226048 * 2 ^ 59
def prefixEnd_3226048 : Nat := 4983230072969 + 3 ^ 40 * 3226048 * 2
def baseEnd_3226048 : Nat := 1656513238475899306063681

theorem tailTrace_3226048 : CollatzResearch.WordTrace tailWord_3226048 prefixEnd_3226048 1656513238475899306063681 := by
  unfold tailWord_3226048
  simp only [CollatzResearch.WordTrace]
  refine ⟨58831818508293267989467399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78442424677724357319289865 58831818508293267989467399)
  ·
    refine ⟨88247727762439901984201099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58831818508293267989467399 88247727762439901984201099)
    ·
      refine ⟨132371591643659852976301649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88247727762439901984201099 132371591643659852976301649)
      ·
        refine ⟨99278693732744889732226237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132371591643659852976301649 99278693732744889732226237)
        ·
          refine ⟨37229510149779333649584839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99278693732744889732226237 37229510149779333649584839)
          ·
            refine ⟨55844265224669000474377259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37229510149779333649584839 55844265224669000474377259)
            ·
              refine ⟨83766397837003500711565889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55844265224669000474377259 83766397837003500711565889)
              ·
                refine ⟨62824798377752625533674417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83766397837003500711565889 62824798377752625533674417)
                ·
                  refine ⟨47118598783314469150255813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62824798377752625533674417 47118598783314469150255813)
                  ·
                    refine ⟨8834737271871462965672965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47118598783314469150255813 8834737271871462965672965)
                    ·
                      refine ⟨1656513238475899306063681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8834737271871462965672965 1656513238475899306063681)
                      ·
                        rfl

theorem cell23_3226048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_3226048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226048 prefixEnd_3226048 := by exact prefixLift 3226048
  have htrace : WordTrace (prefixWord ++ tailWord_3226048) baseStart_3226048 baseEnd_3226048 := by
    simpa [prefixWord, tailWord_3226048, baseEnd_3226048] using wordTrace_append hprefix tailTrace_3226048
  have hstable : (prefixWord ++ tailWord_3226048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226048).length < 2 ^ (prefixWord ++ tailWord_3226048).sum := by decide
  have hdescent : baseEnd_3226048 < baseStart_3226048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226066 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3226066 : Nat := 118140960795 + 3226066 * 2 ^ 59
def prefixEnd_3226066 : Nat := 4983230072969 + 3 ^ 40 * 3226066 * 2
def baseEnd_3226066 : Nat := 552174160375893411879533

theorem tailTrace_3226066 : CollatzResearch.WordTrace tailWord_3226066 prefixEnd_3226066 552174160375893411879533 := by
  unfold tailWord_3226066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29416073382630331263272513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78442862353680883368726701 29416073382630331263272513)
  ·
    refine ⟨22062055036972748447454385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29416073382630331263272513 22062055036972748447454385)
    ·
      refine ⟨16546541277729561335590789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22062055036972748447454385 16546541277729561335590789)
      ·
        refine ⟨3102476489574292750423273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16546541277729561335590789 3102476489574292750423273)
        ·
          refine ⟨2326857367180719562817455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102476489574292750423273 2326857367180719562817455)
          ·
            refine ⟨3490286050771079344226183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326857367180719562817455 3490286050771079344226183)
            ·
              refine ⟨5235429076156619016339275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490286050771079344226183 5235429076156619016339275)
              ·
                refine ⟨7853143614234928524508913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235429076156619016339275 7853143614234928524508913)
                ·
                  refine ⟨5889857710676196393381685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853143614234928524508913 5889857710676196393381685)
                  ·
                    refine ⟨552174160375893411879533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5889857710676196393381685 552174160375893411879533)
                    ·
                      rfl

theorem cell23_3226066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3226066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226066 prefixEnd_3226066 := by exact prefixLift 3226066
  have htrace : WordTrace (prefixWord ++ tailWord_3226066) baseStart_3226066 baseEnd_3226066 := by
    simpa [prefixWord, tailWord_3226066, baseEnd_3226066] using wordTrace_append hprefix tailTrace_3226066
  have hstable : (prefixWord ++ tailWord_3226066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226066).length < 2 ^ (prefixWord ++ tailWord_3226066).sum := by decide
  have hdescent : baseEnd_3226066 < baseStart_3226066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226079 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 1, 4]
def baseStart_3226079 : Nat := 118140960795 + 3226079 * 2 ^ 59
def prefixEnd_3226079 : Nat := 4983230072969 + 3 ^ 40 * 3226079 * 2
def baseEnd_3226079 : Nat := 552176385458729561592013

theorem tailTrace_3226079 : CollatzResearch.WordTrace tailWord_3226079 prefixEnd_3226079 552176385458729561592013 := by
  unfold tailWord_3226079
  simp only [CollatzResearch.WordTrace]
  refine ⟨117664767679474228273313291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78443178452982818848875527 117664767679474228273313291)
  ·
    refine ⟨176497151519211342409969937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117664767679474228273313291 176497151519211342409969937)
    ·
      refine ⟨132372863639408506807477453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176497151519211342409969937 132372863639408506807477453)
      ·
        refine ⟨49639823864778190052804045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132372863639408506807477453 49639823864778190052804045)
        ·
          refine ⟨18614933949291821269801517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49639823864778190052804045 18614933949291821269801517)
          ·
            refine ⟨6980600230984432976175569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18614933949291821269801517 6980600230984432976175569)
            ·
              refine ⟨5235450173238324732131677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980600230984432976175569 5235450173238324732131677)
              ·
                refine ⟨1963293814964371774549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235450173238324732131677 1963293814964371774549379)
                ·
                  refine ⟨2944940722446557661824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963293814964371774549379 2944940722446557661824069)
                  ·
                    refine ⟨552176385458729561592013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944940722446557661824069 552176385458729561592013)
                    ·
                      rfl

theorem cell23_3226079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 4].length) (baseStart_3226079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226079 prefixEnd_3226079 := by exact prefixLift 3226079
  have htrace : WordTrace (prefixWord ++ tailWord_3226079) baseStart_3226079 baseEnd_3226079 := by
    simpa [prefixWord, tailWord_3226079, baseEnd_3226079] using wordTrace_append hprefix tailTrace_3226079
  have hstable : (prefixWord ++ tailWord_3226079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226079).length < 2 ^ (prefixWord ++ tailWord_3226079).sum := by decide
  have hdescent : baseEnd_3226079 < baseStart_3226079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226122 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3226122 : Nat := 118140960795 + 3226122 * 2 ^ 59
def prefixEnd_3226122 : Nat := 4983230072969 + 3 ^ 40 * 3226122 * 2
def baseEnd_3226122 : Nat := 552183745348110672179447

theorem tailTrace_3226122 : CollatzResearch.WordTrace tailWord_3226122 prefixEnd_3226122 552183745348110672179447 := by
  unfold tailWord_3226122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29416584004579611654282155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78444224012212297744752413 29416584004579611654282155)
  ·
    refine ⟨44124876006869417481423233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29416584004579611654282155 44124876006869417481423233)
    ·
      refine ⟨33093657005152063111067425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44124876006869417481423233 33093657005152063111067425)
      ·
        refine ⟨24820242753864047333300569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33093657005152063111067425 24820242753864047333300569)
        ·
          refine ⟨18615182065398035499975427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24820242753864047333300569 18615182065398035499975427)
          ·
            refine ⟨27922773098097053249963141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18615182065398035499975427 27922773098097053249963141)
            ·
              refine ⟨5235519955893197484368089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27922773098097053249963141 5235519955893197484368089)
              ·
                refine ⟨3926639966919898113276067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5235519955893197484368089 3926639966919898113276067)
                ·
                  refine ⟨5889959950379847169914101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926639966919898113276067 5889959950379847169914101)
                  ·
                    refine ⟨552183745348110672179447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5889959950379847169914101 552183745348110672179447)
                    ·
                      rfl

theorem cell23_3226122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3226122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226122 prefixEnd_3226122 := by exact prefixLift 3226122
  have htrace : WordTrace (prefixWord ++ tailWord_3226122) baseStart_3226122 baseEnd_3226122 := by
    simpa [prefixWord, tailWord_3226122, baseEnd_3226122] using wordTrace_append hprefix tailTrace_3226122
  have hstable : (prefixWord ++ tailWord_3226122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226122).length < 2 ^ (prefixWord ++ tailWord_3226122).sum := by decide
  have hdescent : baseEnd_3226122 < baseStart_3226122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226136 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3226136 : Nat := 118140960795 + 3226136 * 2 ^ 59
def prefixEnd_3226136 : Nat := 4983230072969 + 3 ^ 40 * 3226136 * 2
def baseEnd_3226136 : Nat := 1656558424773494961763277

theorem tailTrace_3226136 : CollatzResearch.WordTrace tailWord_3226136 prefixEnd_3226136 1656558424773494961763277 := by
  unfold tailWord_3226136
  simp only [CollatzResearch.WordTrace]
  refine ⟨58833423320133863504069131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78444564426845151338758841 58833423320133863504069131)
  ·
    refine ⟨88250134980200795256103697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58833423320133863504069131 88250134980200795256103697)
    ·
      refine ⟨66187601235150596442077773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88250134980200795256103697 66187601235150596442077773)
      ·
        refine ⟨24820350463181473665779165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66187601235150596442077773 24820350463181473665779165)
        ·
          refine ⟨9307631423693052624667187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24820350463181473665779165 9307631423693052624667187)
          ·
            refine ⟨13961447135539578937000781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9307631423693052624667187 13961447135539578937000781)
            ·
              refine ⟨5235542675827342101375293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13961447135539578937000781 5235542675827342101375293)
              ·
                refine ⟨1963328503435253288015735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235542675827342101375293 1963328503435253288015735)
                ·
                  refine ⟨2944992755152879932023603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963328503435253288015735 2944992755152879932023603)
                  ·
                    refine ⟨4417489132729319898035405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2944992755152879932023603 4417489132729319898035405)
                    ·
                      refine ⟨1656558424773494961763277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417489132729319898035405 1656558424773494961763277)
                      ·
                        rfl

theorem cell23_3226136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3226136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226136 prefixEnd_3226136 := by exact prefixLift 3226136
  have htrace : WordTrace (prefixWord ++ tailWord_3226136) baseStart_3226136 baseEnd_3226136 := by
    simpa [prefixWord, tailWord_3226136, baseEnd_3226136] using wordTrace_append hprefix tailTrace_3226136
  have hstable : (prefixWord ++ tailWord_3226136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226136).length < 2 ^ (prefixWord ++ tailWord_3226136).sum := by decide
  have hdescent : baseEnd_3226136 < baseStart_3226136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226165 : List Nat := [1, 3, 3, 1, 1, 2, 4, 8]
def baseStart_3226165 : Nat := 118140960795 + 3226165 * 2 ^ 59
def prefixEnd_3226165 : Nat := 4983230072969 + 3 ^ 40 * 3226165 * 2
def baseEnd_3226165 : Nat := 61354567248610198085209

theorem tailTrace_3226165 : CollatzResearch.WordTrace tailWord_3226165 prefixEnd_3226165 61354567248610198085209 := by
  unfold tailWord_3226165
  simp only [CollatzResearch.WordTrace]
  refine ⟨117667904357162664960943949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78445269571441776640629299 117667904357162664960943949)
  ·
    refine ⟨44125464133935999360353981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117667904357162664960943949 44125464133935999360353981)
    ·
      refine ⟨16547049050225999760132743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44125464133935999360353981 16547049050225999760132743)
      ·
        refine ⟨24820573575338999640199115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547049050225999760132743 24820573575338999640199115)
        ·
          refine ⟨37230860363008499460298673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24820573575338999640199115 37230860363008499460298673)
          ·
            refine ⟨27923145272256374595224005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37230860363008499460298673 27923145272256374595224005)
            ·
              refine ⟨5235589738548070236604501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27923145272256374595224005 5235589738548070236604501)
              ·
                refine ⟨61354567248610198085209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5235589738548070236604501 61354567248610198085209)
                ·
                  rfl

theorem cell23_3226165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 8].length) (baseStart_3226165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226165 prefixEnd_3226165 := by exact prefixLift 3226165
  have htrace : WordTrace (prefixWord ++ tailWord_3226165) baseStart_3226165 baseEnd_3226165 := by
    simpa [prefixWord, tailWord_3226165, baseEnd_3226165] using wordTrace_append hprefix tailTrace_3226165
  have hstable : (prefixWord ++ tailWord_3226165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226165).length < 2 ^ (prefixWord ++ tailWord_3226165).sum := by decide
  have hdescent : baseEnd_3226165 < baseStart_3226165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226180 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3226180 : Nat := 118140960795 + 3226180 * 2 ^ 59
def prefixEnd_3226180 : Nat := 4983230072969 + 3 ^ 40 * 3226180 * 2
def baseEnd_3226180 : Nat := 1656581017922292789613075

theorem tailTrace_3226180 : CollatzResearch.WordTrace tailWord_3226180 prefixEnd_3226180 1656581017922292789613075 := by
  unfold tailWord_3226180
  simp only [CollatzResearch.WordTrace]
  refine ⟨58834225726054161261369997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78445634301405548348493329 58834225726054161261369997)
  ·
    refine ⟨22062834647270310473013749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58834225726054161261369997 22062834647270310473013749)
    ·
      refine ⟨2068390748181591606845039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22062834647270310473013749 2068390748181591606845039)
      ·
        refine ⟨3102586122272387410267559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068390748181591606845039 3102586122272387410267559)
        ·
          refine ⟨4653879183408581115401339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102586122272387410267559 4653879183408581115401339)
          ·
            refine ⟨6980818775112871673102009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653879183408581115401339 6980818775112871673102009)
            ·
              refine ⟨5235614081334653754826507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980818775112871673102009 5235614081334653754826507)
              ·
                refine ⟨7853421122001980632239761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235614081334653754826507 7853421122001980632239761)
                ·
                  refine ⟨5890065841501485474179821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853421122001980632239761 5890065841501485474179821)
                  ·
                    refine ⟨2208774690563057052817433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5890065841501485474179821 2208774690563057052817433)
                    ·
                      refine ⟨1656581017922292789613075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208774690563057052817433 1656581017922292789613075)
                      ·
                        rfl

theorem cell23_3226180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3226180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226180 prefixEnd_3226180 := by exact prefixLift 3226180
  have htrace : WordTrace (prefixWord ++ tailWord_3226180) baseStart_3226180 baseEnd_3226180 := by
    simpa [prefixWord, tailWord_3226180, baseEnd_3226180] using wordTrace_append hprefix tailTrace_3226180
  have hstable : (prefixWord ++ tailWord_3226180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226180).length < 2 ^ (prefixWord ++ tailWord_3226180).sum := by decide
  have hdescent : baseEnd_3226180 < baseStart_3226180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226189 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3226189 : Nat := 118140960795 + 3226189 * 2 ^ 59
def prefixEnd_3226189 : Nat := 4983230072969 + 3 ^ 40 * 3226189 * 2
def baseEnd_3226189 : Nat := 1656585639248183254400533

theorem tailTrace_3226189 : CollatzResearch.WordTrace tailWord_3226189 prefixEnd_3226189 1656585639248183254400533 := by
  unfold tailWord_3226189
  simp only [CollatzResearch.WordTrace]
  refine ⟨117668779709075717059817621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78445853139383811373211747 117668779709075717059817621)
  ·
    refine ⟨5515724048862924237178951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117668779709075717059817621 5515724048862924237178951)
    ·
      refine ⟨8273586073294386355768427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515724048862924237178951 8273586073294386355768427)
      ·
        refine ⟨12410379109941579533652641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8273586073294386355768427 12410379109941579533652641)
        ·
          refine ⟨9307784332456184650239481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12410379109941579533652641 9307784332456184650239481)
          ·
            refine ⟨6980838249342138487679611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307784332456184650239481 6980838249342138487679611)
            ·
              refine ⟨10471257374013207731519417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6980838249342138487679611 10471257374013207731519417)
              ·
                refine ⟨7853443030509905798639563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10471257374013207731519417 7853443030509905798639563)
                ·
                  refine ⟨11780164545764858697959345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853443030509905798639563 11780164545764858697959345)
                  ·
                    refine ⟨8835123409323644023469509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11780164545764858697959345 8835123409323644023469509)
                    ·
                      refine ⟨1656585639248183254400533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8835123409323644023469509 1656585639248183254400533)
                      ·
                        rfl

theorem cell23_3226189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3226189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226189 prefixEnd_3226189 := by exact prefixLift 3226189
  have htrace : WordTrace (prefixWord ++ tailWord_3226189) baseStart_3226189 baseEnd_3226189 := by
    simpa [prefixWord, tailWord_3226189, baseEnd_3226189] using wordTrace_append hprefix tailTrace_3226189
  have hstable : (prefixWord ++ tailWord_3226189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226189).length < 2 ^ (prefixWord ++ tailWord_3226189).sum := by decide
  have hdescent : baseEnd_3226189 < baseStart_3226189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226192 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3]
def baseStart_3226192 : Nat := 118140960795 + 3226192 * 2 ^ 59
def prefixEnd_3226192 : Nat := 4983230072969 + 3 ^ 40 * 3226192 * 2
def baseEnd_3226192 : Nat := 1656587179690146742663019

theorem tailTrace_3226192 : CollatzResearch.WordTrace tailWord_3226192 prefixEnd_3226192 1656587179690146742663019 := by
  unfold tailWord_3226192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58834444564032424286088415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78445926085376565714784553 58834444564032424286088415)
  ·
    refine ⟨88251666846048636429132623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58834444564032424286088415 88251666846048636429132623)
    ·
      refine ⟨132377500269072954643698935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88251666846048636429132623 132377500269072954643698935)
      ·
        refine ⟨198566250403609431965548403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132377500269072954643698935 198566250403609431965548403)
        ·
          refine ⟨297849375605414147948322605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198566250403609431965548403 297849375605414147948322605)
          ·
            refine ⟨111693515852030305480620977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297849375605414147948322605 111693515852030305480620977)
            ·
              refine ⟨83770136889022729110465733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111693515852030305480620977 83770136889022729110465733)
              ·
                refine ⟨15706900666691761708212325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83770136889022729110465733 15706900666691761708212325)
                ·
                  refine ⟨2945043875004705320289811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15706900666691761708212325 2945043875004705320289811)
                  ·
                    refine ⟨4417565812507057980434717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945043875004705320289811 4417565812507057980434717)
                    ·
                      refine ⟨1656587179690146742663019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417565812507057980434717 1656587179690146742663019)
                      ·
                        rfl

theorem cell23_3226192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_3226192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226192 prefixEnd_3226192 := by exact prefixLift 3226192
  have htrace : WordTrace (prefixWord ++ tailWord_3226192) baseStart_3226192 baseEnd_3226192 := by
    simpa [prefixWord, tailWord_3226192, baseEnd_3226192] using wordTrace_append hprefix tailTrace_3226192
  have hstable : (prefixWord ++ tailWord_3226192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226192).length < 2 ^ (prefixWord ++ tailWord_3226192).sum := by decide
  have hdescent : baseEnd_3226192 < baseStart_3226192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226196 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_3226196 : Nat := 118140960795 + 3226196 * 2 ^ 59
def prefixEnd_3226196 : Nat := 4983230072969 + 3 ^ 40 * 3226196 * 2
def baseEnd_3226196 : Nat := 1656589233612764727013001

theorem tailTrace_3226196 : CollatzResearch.WordTrace tailWord_3226196 prefixEnd_3226196 1656589233612764727013001 := by
  unfold tailWord_3226196
  simp only [CollatzResearch.WordTrace]
  refine ⟨58834517510025178627661221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78446023346700238170214961 58834517510025178627661221)
  ·
    refine ⟨11031472033129720992686479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58834517510025178627661221 11031472033129720992686479)
    ·
      refine ⟨16547208049694581489029719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031472033129720992686479 16547208049694581489029719)
      ·
        refine ⟨24820812074541872233544579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547208049694581489029719 24820812074541872233544579)
        ·
          refine ⟨37231218111812808350316869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24820812074541872233544579 37231218111812808350316869)
          ·
            refine ⟨6980853395964901565684413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37231218111812808350316869 6980853395964901565684413)
            ·
              refine ⟨2617820023486838087131655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6980853395964901565684413 2617820023486838087131655)
              ·
                refine ⟨3926730035230257130697483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617820023486838087131655 3926730035230257130697483)
                ·
                  refine ⟨5890095052845385696046225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926730035230257130697483 5890095052845385696046225)
                  ·
                    refine ⟨4417571289634039272034669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890095052845385696046225 4417571289634039272034669)
                    ·
                      refine ⟨1656589233612764727013001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417571289634039272034669 1656589233612764727013001)
                      ·
                        rfl

theorem cell23_3226196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_3226196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226196 prefixEnd_3226196 := by exact prefixLift 3226196
  have htrace : WordTrace (prefixWord ++ tailWord_3226196) baseStart_3226196 baseEnd_3226196 := by
    simpa [prefixWord, tailWord_3226196, baseEnd_3226196] using wordTrace_append hprefix tailTrace_3226196
  have hstable : (prefixWord ++ tailWord_3226196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226196).length < 2 ^ (prefixWord ++ tailWord_3226196).sum := by decide
  have hdescent : baseEnd_3226196 < baseStart_3226196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226209 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_3226209 : Nat := 118140960795 + 3226209 * 2 ^ 59
def prefixEnd_3226209 : Nat := 4983230072969 + 3 ^ 40 * 3226209 * 2
def baseEnd_3226209 : Nat := 1656595908861273176150441

theorem tailTrace_3226209 : CollatzResearch.WordTrace tailWord_3226209 prefixEnd_3226209 1656595908861273176150441 := by
  unfold tailWord_3226209
  simp only [CollatzResearch.WordTrace]
  refine ⟨117669509169003260475545681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78446339446002173650363787 117669509169003260475545681)
  ·
    refine ⟨88252131876752445356659261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117669509169003260475545681 88252131876752445356659261)
    ·
      refine ⟨33094549453782167008747223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88252131876752445356659261 33094549453782167008747223)
      ·
        refine ⟨49641824180673250513120835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33094549453782167008747223 49641824180673250513120835)
        ·
          refine ⟨74462736271009875769681253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49641824180673250513120835 74462736271009875769681253)
          ·
            refine ⟨13961763050814351706815235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74462736271009875769681253 13961763050814351706815235)
            ·
              refine ⟨20942644576221527560222853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13961763050814351706815235 20942644576221527560222853)
              ·
                refine ⟨3926745858041536417541785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20942644576221527560222853 3926745858041536417541785)
                ·
                  refine ⟨2945059393531152313156339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3926745858041536417541785 2945059393531152313156339)
                  ·
                    refine ⟨4417589090296728469734509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945059393531152313156339 4417589090296728469734509)
                    ·
                      refine ⟨1656595908861273176150441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417589090296728469734509 1656595908861273176150441)
                      ·
                        rfl

theorem cell23_3226209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_3226209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226209 prefixEnd_3226209 := by exact prefixLift 3226209
  have htrace : WordTrace (prefixWord ++ tailWord_3226209) baseStart_3226209 baseEnd_3226209 := by
    simpa [prefixWord, tailWord_3226209, baseEnd_3226209] using wordTrace_append hprefix tailTrace_3226209
  have hstable : (prefixWord ++ tailWord_3226209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226209).length < 2 ^ (prefixWord ++ tailWord_3226209).sum := by decide
  have hdescent : baseEnd_3226209 < baseStart_3226209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226232 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_3226232 : Nat := 118140960795 + 3226232 * 2 ^ 59
def prefixEnd_3226232 : Nat := 4983230072969 + 3 ^ 40 * 3226232 * 2
def baseEnd_3226232 : Nat := 1656607718916326586162835

theorem tailTrace_3226232 : CollatzResearch.WordTrace tailWord_3226232 prefixEnd_3226232 1656607718916326586162835 := by
  unfold tailWord_3226232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58835174023959967701816475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78446898698613290269088633 58835174023959967701816475)
  ·
    refine ⟨88252761035939951552724713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58835174023959967701816475 88252761035939951552724713)
    ·
      refine ⟨66189570776954963664543535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88252761035939951552724713 66189570776954963664543535)
      ·
        refine ⟨99284356165432445496815303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66189570776954963664543535 99284356165432445496815303)
        ·
          refine ⟨148926534248148668245222955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99284356165432445496815303 148926534248148668245222955)
          ·
            refine ⟨223389801372223002367834433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148926534248148668245222955 223389801372223002367834433)
            ·
              refine ⟨167542351029167251775875825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223389801372223002367834433 167542351029167251775875825)
              ·
                refine ⟨125656763271875438831906869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167542351029167251775875825 125656763271875438831906869)
                ·
                  refine ⟨11780321556738322390491269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125656763271875438831906869 11780321556738322390491269)
                  ·
                    refine ⟨2208810291888435448217113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11780321556738322390491269 2208810291888435448217113)
                    ·
                      refine ⟨1656607718916326586162835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208810291888435448217113 1656607718916326586162835)
                      ·
                        rfl

theorem cell23_3226232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_3226232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226232 prefixEnd_3226232 := by exact prefixLift 3226232
  have htrace : WordTrace (prefixWord ++ tailWord_3226232) baseStart_3226232 baseEnd_3226232 := by
    simpa [prefixWord, tailWord_3226232, baseEnd_3226232] using wordTrace_append hprefix tailTrace_3226232
  have hstable : (prefixWord ++ tailWord_3226232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226232).length < 2 ^ (prefixWord ++ tailWord_3226232).sum := by decide
  have hdescent : baseEnd_3226232 < baseStart_3226232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226235 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_3226235 : Nat := 118140960795 + 3226235 * 2 ^ 59
def prefixEnd_3226235 : Nat := 4983230072969 + 3 ^ 40 * 3226235 * 2
def baseEnd_3226235 : Nat := 1656609259358290074425321

theorem tailTrace_3226235 : CollatzResearch.WordTrace tailWord_3226235 prefixEnd_3226235 1656609259358290074425321 := by
  unfold tailWord_3226235
  simp only [CollatzResearch.WordTrace]
  refine ⟨117670457466909066915992159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78446971644606044610661439 117670457466909066915992159)
  ·
    refine ⟨176505686200363600373988239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117670457466909066915992159 176505686200363600373988239)
    ·
      refine ⟨264758529300545400560982359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176505686200363600373988239 264758529300545400560982359)
      ·
        refine ⟨397137793950818100841473539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264758529300545400560982359 397137793950818100841473539)
        ·
          refine ⟨595706690926227151262210309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397137793950818100841473539 595706690926227151262210309)
          ·
            refine ⟨111695004548667590861664433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 595706690926227151262210309 111695004548667590861664433)
            ·
              refine ⟨83771253411500693146248325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111695004548667590861664433 83771253411500693146248325)
              ·
                refine ⟨15707110014656379964921561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83771253411500693146248325 15707110014656379964921561)
                ·
                  refine ⟨11780332510992284973691171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15707110014656379964921561 11780332510992284973691171)
                  ·
                    refine ⟨17670498766488427460536757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11780332510992284973691171 17670498766488427460536757)
                    ·
                      refine ⟨1656609259358290074425321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17670498766488427460536757 1656609259358290074425321)
                      ·
                        rfl

theorem cell23_3226235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_3226235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226235 prefixEnd_3226235 := by exact prefixLift 3226235
  have htrace : WordTrace (prefixWord ++ tailWord_3226235) baseStart_3226235 baseEnd_3226235 := by
    simpa [prefixWord, tailWord_3226235, baseEnd_3226235] using wordTrace_append hprefix tailTrace_3226235
  have hstable : (prefixWord ++ tailWord_3226235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226235).length < 2 ^ (prefixWord ++ tailWord_3226235).sum := by decide
  have hdescent : baseEnd_3226235 < baseStart_3226235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226249 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 4, 2, 2]
def baseStart_3226249 : Nat := 118140960795 + 3226249 * 2 ^ 59
def prefixEnd_3226249 : Nat := 4983230072969 + 3 ^ 40 * 3226249 * 2
def baseEnd_3226249 : Nat := 1656616448087453019650257

theorem tailTrace_3226249 : CollatzResearch.WordTrace tailWord_3226249 prefixEnd_3226249 1656616448087453019650257 := by
  unfold tailWord_3226249
  simp only [CollatzResearch.WordTrace]
  refine ⟨117670968088858347307001801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78447312059238898204667867 117670968088858347307001801)
  ·
    refine ⟨88253226066643760480251351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117670968088858347307001801 88253226066643760480251351)
    ·
      refine ⟨132379839099965640720377027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88253226066643760480251351 132379839099965640720377027)
      ·
        refine ⟨198569758649948461080565541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132379839099965640720377027 198569758649948461080565541)
        ·
          refine ⟨37231829746865336452606039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198569758649948461080565541 37231829746865336452606039)
          ·
            refine ⟨55847744620298004678909059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37231829746865336452606039 55847744620298004678909059)
            ·
              refine ⟨83771616930447007018363589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55847744620298004678909059 83771616930447007018363589)
              ·
                refine ⟨15707178174458813815943173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83771616930447007018363589 15707178174458813815943173)
                ·
                  refine ⟨2945095907711027590489345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15707178174458813815943173 2945095907711027590489345)
                  ·
                    refine ⟨2208821930783270692867009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2945095907711027590489345 2208821930783270692867009)
                    ·
                      refine ⟨1656616448087453019650257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208821930783270692867009 1656616448087453019650257)
                      ·
                        rfl

theorem cell23_3226249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 2, 2].length) (baseStart_3226249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226249 prefixEnd_3226249 := by exact prefixLift 3226249
  have htrace : WordTrace (prefixWord ++ tailWord_3226249) baseStart_3226249 baseEnd_3226249 := by
    simpa [prefixWord, tailWord_3226249, baseEnd_3226249] using wordTrace_append hprefix tailTrace_3226249
  have hstable : (prefixWord ++ tailWord_3226249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226249).length < 2 ^ (prefixWord ++ tailWord_3226249).sum := by decide
  have hdescent : baseEnd_3226249 < baseStart_3226249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226302 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_3226302 : Nat := 118140960795 + 3226302 * 2 ^ 59
def prefixEnd_3226302 : Nat := 4983230072969 + 3 ^ 40 * 3226302 * 2
def baseEnd_3226302 : Nat := 552214554187380437429171

theorem tailTrace_3226302 : CollatzResearch.WordTrace tailWord_3226302 prefixEnd_3226302 552214554187380437429171 := by
  unfold tailWord_3226302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14709112644708292169835145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78448600771777558239120773 14709112644708292169835145)
  ·
    refine ⟨11031834483531219127376359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14709112644708292169835145 11031834483531219127376359)
    ·
      refine ⟨16547751725296828691064539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031834483531219127376359 16547751725296828691064539)
      ·
        refine ⟨24821627587945243036596809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547751725296828691064539 24821627587945243036596809)
        ·
          refine ⟨18616220690958932277447607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24821627587945243036596809 18616220690958932277447607)
          ·
            refine ⟨27924331036438398416171411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18616220690958932277447607 27924331036438398416171411)
            ·
              refine ⟨41886496554657597624257117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27924331036438398416171411 41886496554657597624257117)
              ·
                refine ⟨15707436207996599109096419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41886496554657597624257117 15707436207996599109096419)
                ·
                  refine ⟨23561154311994898663644629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15707436207996599109096419 23561154311994898663644629)
                  ·
                    refine ⟨552214554187380437429171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23561154311994898663644629 552214554187380437429171)
                    ·
                      rfl

theorem cell23_3226302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_3226302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226302 prefixEnd_3226302 := by exact prefixLift 3226302
  have htrace : WordTrace (prefixWord ++ tailWord_3226302) baseStart_3226302 baseEnd_3226302 := by
    simpa [prefixWord, tailWord_3226302, baseEnd_3226302] using wordTrace_append hprefix tailTrace_3226302
  have hstable : (prefixWord ++ tailWord_3226302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226302).length < 2 ^ (prefixWord ++ tailWord_3226302).sum := by decide
  have hdescent : baseEnd_3226302 < baseStart_3226302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226349 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3226349 : Nat := 118140960795 + 3226349 * 2 ^ 59
def prefixEnd_3226349 : Nat := 4983230072969 + 3 ^ 40 * 3226349 * 2
def baseEnd_3226349 : Nat := 552222598717634209466599

theorem tailTrace_3226349 : CollatzResearch.WordTrace tailWord_3226349 prefixEnd_3226349 552222598717634209466599 := by
  unfold tailWord_3226349
  simp only [CollatzResearch.WordTrace]
  refine ⟨117674615388496064385642101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78449743592330709590428067 117674615388496064385642101)
  ·
    refine ⟨11031995192671506036153947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117674615388496064385642101 11031995192671506036153947)
    ·
      refine ⟨16547992789007259054230921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031995192671506036153947 16547992789007259054230921)
      ·
        refine ⟨12410994591755444290673191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16547992789007259054230921 12410994591755444290673191)
        ·
          refine ⟨18616491887633166436009787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410994591755444290673191 18616491887633166436009787)
          ·
            refine ⟨27924737831449749654014681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18616491887633166436009787 27924737831449749654014681)
            ·
              refine ⟨20943553373587312240511011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27924737831449749654014681 20943553373587312240511011)
              ·
                refine ⟨31415330060380968360766517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20943553373587312240511011 31415330060380968360766517)
                ·
                  refine ⟨2945187193160715783821861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31415330060380968360766517 2945187193160715783821861)
                  ·
                    refine ⟨552222598717634209466599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2945187193160715783821861 552222598717634209466599)
                    ·
                      rfl

theorem cell23_3226349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3226349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226349 prefixEnd_3226349 := by exact prefixLift 3226349
  have htrace : WordTrace (prefixWord ++ tailWord_3226349) baseStart_3226349 baseEnd_3226349 := by
    simpa [prefixWord, tailWord_3226349, baseEnd_3226349] using wordTrace_append hprefix tailTrace_3226349
  have hstable : (prefixWord ++ tailWord_3226349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226349).length < 2 ^ (prefixWord ++ tailWord_3226349).sum := by decide
  have hdescent : baseEnd_3226349 < baseStart_3226349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226382 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3226382 : Nat := 118140960795 + 3226382 * 2 ^ 59
def prefixEnd_3226382 : Nat := 4983230072969 + 3 ^ 40 * 3226382 * 2
def baseEnd_3226382 : Nat := 1656684741014500999287145

theorem tailTrace_3226382 : CollatzResearch.WordTrace tailWord_3226382 prefixEnd_3226382 1656684741014500999287145 := by
  unfold tailWord_3226382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14709477374672063877699175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78450545998251007347728933 14709477374672063877699175)
  ·
    refine ⟨22064216062008095816548763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14709477374672063877699175 22064216062008095816548763)
    ·
      refine ⟨33096324093012143724823145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22064216062008095816548763 33096324093012143724823145)
      ·
        refine ⟨24822243069759107793617359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33096324093012143724823145 24822243069759107793617359)
        ·
          refine ⟨37233364604638661690426039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24822243069759107793617359 37233364604638661690426039)
          ·
            refine ⟨55850046906957992535639059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37233364604638661690426039 55850046906957992535639059)
            ·
              refine ⟨83775070360436988803458589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55850046906957992535639059 83775070360436988803458589)
              ·
                refine ⟨31415651385163870801296971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83775070360436988803458589 31415651385163870801296971)
                ·
                  refine ⟨47123477077745806201945457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31415651385163870801296971 47123477077745806201945457)
                  ·
                    refine ⟨35342607808309354651459093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47123477077745806201945457 35342607808309354651459093)
                    ·
                      refine ⟨1656684741014500999287145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35342607808309354651459093 1656684741014500999287145)
                      ·
                        rfl

theorem cell23_3226382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3226382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226382 prefixEnd_3226382 := by exact prefixLift 3226382
  have htrace : WordTrace (prefixWord ++ tailWord_3226382) baseStart_3226382 baseEnd_3226382 := by
    simpa [prefixWord, tailWord_3226382, baseEnd_3226382] using wordTrace_append hprefix tailTrace_3226382
  have hstable : (prefixWord ++ tailWord_3226382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226382).length < 2 ^ (prefixWord ++ tailWord_3226382).sum := by decide
  have hdescent : baseEnd_3226382 < baseStart_3226382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226410 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3226410 : Nat := 118140960795 + 3226410 * 2 ^ 59
def prefixEnd_3226410 : Nat := 4983230072969 + 3 ^ 40 * 3226410 * 2
def baseEnd_3226410 : Nat := 1656699118472826889737017

theorem tailTrace_3226410 : CollatzResearch.WordTrace tailWord_3226410 prefixEnd_3226410 1656699118472826889737017 := by
  unfold tailWord_3226410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29419210060318767950903171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78451226827516714535741789 29419210060318767950903171)
  ·
    refine ⟨44128815090478151926354757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29419210060318767950903171 44128815090478151926354757)
    ·
      refine ⟨8274152829464653486191517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44128815090478151926354757 8274152829464653486191517)
      ·
        refine ⟨3102807311049245057321819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8274152829464653486191517 3102807311049245057321819)
        ·
          refine ⟨4654210966573867585982729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102807311049245057321819 4654210966573867585982729)
          ·
            refine ⟨3490658224930400689487047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654210966573867585982729 3490658224930400689487047)
            ·
              refine ⟨5235987337395601034230571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490658224930400689487047 5235987337395601034230571)
              ·
                refine ⟨7853981006093401551345857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235987337395601034230571 7853981006093401551345857)
                ·
                  refine ⟨5890485754570051163509393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7853981006093401551345857 5890485754570051163509393)
                  ·
                    refine ⟨4417864315927538372632045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5890485754570051163509393 4417864315927538372632045)
                    ·
                      refine ⟨1656699118472826889737017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417864315927538372632045 1656699118472826889737017)
                      ·
                        rfl

theorem cell23_3226410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3226410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226410 prefixEnd_3226410 := by exact prefixLift 3226410
  have htrace : WordTrace (prefixWord ++ tailWord_3226410) baseStart_3226410 baseEnd_3226410 := by
    simpa [prefixWord, tailWord_3226410, baseEnd_3226410] using wordTrace_append hprefix tailTrace_3226410
  have hstable : (prefixWord ++ tailWord_3226410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226410).length < 2 ^ (prefixWord ++ tailWord_3226410).sum := by decide
  have hdescent : baseEnd_3226410 < baseStart_3226410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226423 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 1, 1, 3]
def baseStart_3226423 : Nat := 118140960795 + 3226423 * 2 ^ 59
def prefixEnd_3226423 : Nat := 4983230072969 + 3 ^ 40 * 3226423 * 2
def baseEnd_3226423 : Nat := 1656705793721335338874457

theorem tailTrace_3226423 : CollatzResearch.WordTrace tailWord_3226423 prefixEnd_3226423 1656705793721335338874457 := by
  unfold tailWord_3226423
  simp only [CollatzResearch.WordTrace]
  refine ⟨117677314390227975023835923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78451542926818650015890615 117677314390227975023835923)
  ·
    refine ⟨176515971585341962535753885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117677314390227975023835923 176515971585341962535753885)
    ·
      refine ⟨66193489344503235950907707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176515971585341962535753885 66193489344503235950907707)
      ·
        refine ⟨99290234016754853926361561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66193489344503235950907707 99290234016754853926361561)
        ·
          refine ⟨74467675512566140444771171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99290234016754853926361561 74467675512566140444771171)
          ·
            refine ⟨111701513268849210667156757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74467675512566140444771171 111701513268849210667156757)
            ·
              refine ⟨5236008434477306750022973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111701513268849210667156757 5236008434477306750022973)
              ·
                refine ⟨1963503162928990031258615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5236008434477306750022973 1963503162928990031258615)
                ·
                  refine ⟨2945254744393485046887923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963503162928990031258615 2945254744393485046887923)
                  ·
                    refine ⟨4417882116590227570331885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945254744393485046887923 4417882116590227570331885)
                    ·
                      refine ⟨1656705793721335338874457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417882116590227570331885 1656705793721335338874457)
                      ·
                        rfl

theorem cell23_3226423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_3226423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226423 prefixEnd_3226423 := by exact prefixLift 3226423
  have htrace : WordTrace (prefixWord ++ tailWord_3226423) baseStart_3226423 baseEnd_3226423 := by
    simpa [prefixWord, tailWord_3226423, baseEnd_3226423] using wordTrace_append hprefix tailTrace_3226423
  have hstable : (prefixWord ++ tailWord_3226423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226423).length < 2 ^ (prefixWord ++ tailWord_3226423).sum := by decide
  have hdescent : baseEnd_3226423 < baseStart_3226423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226426 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_3226426 : Nat := 118140960795 + 3226426 * 2 ^ 59
def prefixEnd_3226426 : Nat := 4983230072969 + 3 ^ 40 * 3226426 * 2
def baseEnd_3226426 : Nat := 552235778054432942378981

theorem tailTrace_3226426 : CollatzResearch.WordTrace tailWord_3226426 prefixEnd_3226426 552235778054432942378981 := by
  unfold tailWord_3226426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29419355952304276634048783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78451615872811404357463421 29419355952304276634048783)
  ·
    refine ⟨44129033928456414951073175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29419355952304276634048783 44129033928456414951073175)
    ·
      refine ⟨66193550892684622426609763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44129033928456414951073175 66193550892684622426609763)
      ·
        refine ⟨99290326339026933639914645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66193550892684622426609763 99290326339026933639914645)
        ·
          refine ⟨4654234047141887514370999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99290326339026933639914645 4654234047141887514370999)
          ·
            refine ⟨6981351070712831271556499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654234047141887514370999 6981351070712831271556499)
            ·
              refine ⟨10472026606069246907334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6981351070712831271556499 10472026606069246907334749)
              ·
                refine ⟨3927009977275967590250531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10472026606069246907334749 3927009977275967590250531)
                ·
                  refine ⟨5890514965913951385375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927009977275967590250531 5890514965913951385375797)
                  ·
                    refine ⟨552235778054432942378981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5890514965913951385375797 552235778054432942378981)
                    ·
                      rfl

theorem cell23_3226426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_3226426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226426 prefixEnd_3226426 := by exact prefixLift 3226426
  have htrace : WordTrace (prefixWord ++ tailWord_3226426) baseStart_3226426 baseEnd_3226426 := by
    simpa [prefixWord, tailWord_3226426, baseEnd_3226426] using wordTrace_append hprefix tailTrace_3226426
  have hstable : (prefixWord ++ tailWord_3226426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226426).length < 2 ^ (prefixWord ++ tailWord_3226426).sum := by decide
  have hdescent : baseEnd_3226426 < baseStart_3226426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226432 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_3226432 : Nat := 118140960795 + 3226432 * 2 ^ 59
def prefixEnd_3226432 : Nat := 4983230072969 + 3 ^ 40 * 3226432 * 2
def baseEnd_3226432 : Nat := 1656710415047225803661915

theorem tailTrace_3226432 : CollatzResearch.WordTrace tailWord_3226432 prefixEnd_3226432 1656710415047225803661915 := by
  unfold tailWord_3226432
  simp only [CollatzResearch.WordTrace]
  refine ⟨58838821323597684780456775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78451761764796913040609033 58838821323597684780456775)
  ·
    refine ⟨88258231985396527170685163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58838821323597684780456775 88258231985396527170685163)
    ·
      refine ⟨132387347978094790756027745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88258231985396527170685163 132387347978094790756027745)
      ·
        refine ⟨99290510983571093067020809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132387347978094790756027745 99290510983571093067020809)
        ·
          refine ⟨74467883237678319800265607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99290510983571093067020809 74467883237678319800265607)
          ·
            refine ⟨111701824856517479700398411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74467883237678319800265607 111701824856517479700398411)
            ·
              refine ⟨167552737284776219550597617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111701824856517479700398411 167552737284776219550597617)
              ·
                refine ⟨125664552963582164662948213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167552737284776219550597617 125664552963582164662948213)
                ·
                  refine ⟨11781051840335827937151395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125664552963582164662948213 11781051840335827937151395)
                  ·
                    refine ⟨17671577760503741905727093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11781051840335827937151395 17671577760503741905727093)
                    ·
                      refine ⟨1656710415047225803661915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17671577760503741905727093 1656710415047225803661915)
                      ·
                        rfl

theorem cell23_3226432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_3226432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226432 prefixEnd_3226432 := by exact prefixLift 3226432
  have htrace : WordTrace (prefixWord ++ tailWord_3226432) baseStart_3226432 baseEnd_3226432 := by
    simpa [prefixWord, tailWord_3226432, baseEnd_3226432] using wordTrace_append hprefix tailTrace_3226432
  have hstable : (prefixWord ++ tailWord_3226432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226432).length < 2 ^ (prefixWord ++ tailWord_3226432).sum := by decide
  have hdescent : baseEnd_3226432 < baseStart_3226432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226469 : List Nat := [1, 3, 1, 3, 1, 1, 6, 7]
def baseStart_3226469 : Nat := 118140960795 + 3226469 * 2 ^ 59
def prefixEnd_3226469 : Nat := 4983230072969 + 3 ^ 40 * 3226469 * 2
def baseEnd_3226469 : Nat := 61360348660423783662935

theorem tailTrace_3226469 : CollatzResearch.WordTrace tailWord_3226469 prefixEnd_3226469 61360348660423783662935 := by
  unfold tailWord_3226469
  simp only [CollatzResearch.WordTrace]
  refine ⟨117678992148061324880010461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78452661432040883253340307 117678992148061324880010461)
  ·
    refine ⟨44129622055522996830003923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117678992148061324880010461 44129622055522996830003923)
    ·
      refine ⟨66194433083284495245005885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44129622055522996830003923 66194433083284495245005885)
      ·
        refine ⟨24822912406231685716877207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66194433083284495245005885 24822912406231685716877207)
        ·
          refine ⟨37234368609347528575315811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24822912406231685716877207 37234368609347528575315811)
          ·
            refine ⟨55851552914021292862973717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37234368609347528575315811 55851552914021292862973717)
            ·
              refine ⟨2618041542844748102951893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55851552914021292862973717 2618041542844748102951893)
              ·
                refine ⟨61360348660423783662935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2618041542844748102951893 61360348660423783662935)
                ·
                  rfl

theorem cell23_3226469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 7].length) (baseStart_3226469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226469 prefixEnd_3226469 := by exact prefixLift 3226469
  have htrace : WordTrace (prefixWord ++ tailWord_3226469) baseStart_3226469 baseEnd_3226469 := by
    simpa [prefixWord, tailWord_3226469, baseEnd_3226469] using wordTrace_append hprefix tailTrace_3226469
  have hstable : (prefixWord ++ tailWord_3226469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226469).length < 2 ^ (prefixWord ++ tailWord_3226469).sum := by decide
  have hdescent : baseEnd_3226469 < baseStart_3226469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226479 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_3226479 : Nat := 118140960795 + 3226479 * 2 ^ 59
def prefixEnd_3226479 : Nat := 4983230072969 + 3 ^ 40 * 3226479 * 2
def baseEnd_3226479 : Nat := 1656734548637987119774199

theorem tailTrace_3226479 : CollatzResearch.WordTrace tailWord_3226479 prefixEnd_3226479 1656734548637987119774199 := by
  unfold tailWord_3226479
  simp only [CollatzResearch.WordTrace]
  refine ⟨117679356878025096587874491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78452904585350064391916327 117679356878025096587874491)
  ·
    refine ⟨176519035317037644881811737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117679356878025096587874491 176519035317037644881811737)
    ·
      refine ⟨132389276487778233661358803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176519035317037644881811737 132389276487778233661358803)
      ·
        refine ⟨198583914731667350492038205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132389276487778233661358803 198583914731667350492038205)
        ·
          refine ⟨74468968024375256434514327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198583914731667350492038205 74468968024375256434514327)
          ·
            refine ⟨111703452036562884651771491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74468968024375256434514327 111703452036562884651771491)
            ·
              refine ⟨167555178054844326977657237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111703452036562884651771491 167555178054844326977657237)
              ·
                refine ⟨7854148971320827827077683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167555178054844326977657237 7854148971320827827077683)
                ·
                  refine ⟨11781223456981241740616525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854148971320827827077683 11781223456981241740616525)
                  ·
                    refine ⟨4417958796367965652731197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11781223456981241740616525 4417958796367965652731197)
                    ·
                      refine ⟨1656734548637987119774199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4417958796367965652731197 1656734548637987119774199)
                      ·
                        rfl

theorem cell23_3226479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_3226479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226479 prefixEnd_3226479 := by exact prefixLift 3226479
  have htrace : WordTrace (prefixWord ++ tailWord_3226479) baseStart_3226479 baseEnd_3226479 := by
    simpa [prefixWord, tailWord_3226479, baseEnd_3226479] using wordTrace_append hprefix tailTrace_3226479
  have hstable : (prefixWord ++ tailWord_3226479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226479).length < 2 ^ (prefixWord ++ tailWord_3226479).sum := by decide
  have hdescent : baseEnd_3226479 < baseStart_3226479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226480 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 1, 2, 2]
def baseStart_3226480 : Nat := 118140960795 + 3226480 * 2 ^ 59
def prefixEnd_3226480 : Nat := 4983230072969 + 3 ^ 40 * 3226480 * 2
def baseEnd_3226480 : Nat := 1656735062118641615861695

theorem tailTrace_3226480 : CollatzResearch.WordTrace tailWord_3226480 prefixEnd_3226480 1656735062118641615861695 := by
  unfold tailWord_3226480
  simp only [CollatzResearch.WordTrace]
  refine ⟨58839696675510736879330447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78452928900680982505773929 58839696675510736879330447)
  ·
    refine ⟨88259545013266105318995671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58839696675510736879330447 88259545013266105318995671)
    ·
      refine ⟨132389317519899157978493507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88259545013266105318995671 132389317519899157978493507)
      ·
        refine ⟨198583976279848736967740261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132389317519899157978493507 198583976279848736967740261)
        ·
          refine ⟨37234495552471638181451299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198583976279848736967740261 37234495552471638181451299)
          ·
            refine ⟨55851743328707457272176949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37234495552471638181451299 55851743328707457272176949)
            ·
              refine ⟨5236100937066324119266589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55851743328707457272176949 5236100937066324119266589)
              ·
                refine ⟨1963537851399871544724971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5236100937066324119266589 1963537851399871544724971)
                ·
                  refine ⟨2945306777099807317087457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963537851399871544724971 2945306777099807317087457)
                  ·
                    refine ⟨2208980082824855487815593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2945306777099807317087457 2208980082824855487815593)
                    ·
                      refine ⟨1656735062118641615861695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2208980082824855487815593 1656735062118641615861695)
                      ·
                        rfl

theorem cell23_3226480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 2, 2].length) (baseStart_3226480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226480 prefixEnd_3226480 := by exact prefixLift 3226480
  have htrace : WordTrace (prefixWord ++ tailWord_3226480) baseStart_3226480 baseEnd_3226480 := by
    simpa [prefixWord, tailWord_3226480, baseEnd_3226480] using wordTrace_append hprefix tailTrace_3226480
  have hstable : (prefixWord ++ tailWord_3226480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226480).length < 2 ^ (prefixWord ++ tailWord_3226480).sum := by decide
  have hdescent : baseEnd_3226480 < baseStart_3226480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226486 : List Nat := [5, 1, 1, 3, 1, 3, 9]
def baseStart_3226486 : Nat := 118140960795 + 3226486 * 2 ^ 59
def prefixEnd_3226486 : Nat := 4983230072969 + 3 ^ 40 * 3226486 * 2
def baseEnd_3226486 : Nat := 20453557321019365338107

theorem tailTrace_3226486 : CollatzResearch.WordTrace tailWord_3226486 prefixEnd_3226486 20453557321019365338107 := by
  unfold tailWord_3226486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354975761812483548961207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78453074792666491188919541 7354975761812483548961207)
  ·
    refine ⟨11032463642718725323441811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7354975761812483548961207 11032463642718725323441811)
    ·
      refine ⟨16548695464078087985162717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11032463642718725323441811 16548695464078087985162717)
      ·
        refine ⟨6205760799029282994436019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16548695464078087985162717 6205760799029282994436019)
        ·
          refine ⟨9308641198543924491654029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205760799029282994436019 9308641198543924491654029)
          ·
            refine ⟨3490740449453971684370261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9308641198543924491654029 3490740449453971684370261)
            ·
              refine ⟨20453557321019365338107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3490740449453971684370261 20453557321019365338107)
              ·
                rfl

theorem cell23_3226486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 9].length) (baseStart_3226486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226486 prefixEnd_3226486 := by exact prefixLift 3226486
  have htrace : WordTrace (prefixWord ++ tailWord_3226486) baseStart_3226486 baseEnd_3226486 := by
    simpa [prefixWord, tailWord_3226486, baseEnd_3226486] using wordTrace_append hprefix tailTrace_3226486
  have hstable : (prefixWord ++ tailWord_3226486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226486).length < 2 ^ (prefixWord ++ tailWord_3226486).sum := by decide
  have hdescent : baseEnd_3226486 < baseStart_3226486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226596 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_3226596 : Nat := 118140960795 + 3226596 * 2 ^ 59
def prefixEnd_3226596 : Nat := 4983230072969 + 3 ^ 40 * 3226596 * 2
def baseEnd_3226596 : Nat := 1656794625874563162011161

theorem tailTrace_3226596 : CollatzResearch.WordTrace tailWord_3226596 prefixEnd_3226596 1656794625874563162011161 := by
  unfold tailWord_3226596
  simp only [CollatzResearch.WordTrace]
  refine ⟨58841812109300612784941821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78455749479067483713255761 58841812109300612784941821)
  ·
    refine ⟨22065679540987729794353183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58841812109300612784941821 22065679540987729794353183)
    ·
      refine ⟨33098519311481594691529775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22065679540987729794353183 33098519311481594691529775)
      ·
        refine ⟨49647778967222392037294663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33098519311481594691529775 49647778967222392037294663)
        ·
          refine ⟨74471668450833588055941995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49647778967222392037294663 74471668450833588055941995)
          ·
            refine ⟨111707502676250382083912993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74471668450833588055941995 111707502676250382083912993)
            ·
              refine ⟨83780627007187786562934745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111707502676250382083912993 83780627007187786562934745)
              ·
                refine ⟨62835470255390839922201059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83780627007187786562934745 62835470255390839922201059)
                ·
                  refine ⟨94253205383086259883301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62835470255390839922201059 94253205383086259883301589)
                  ·
                    refine ⟨2209059501166084216014881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94253205383086259883301589 2209059501166084216014881)
                    ·
                      refine ⟨1656794625874563162011161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2209059501166084216014881 1656794625874563162011161)
                      ·
                        rfl

theorem cell23_3226596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_3226596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226596 prefixEnd_3226596 := by exact prefixLift 3226596
  have htrace : WordTrace (prefixWord ++ tailWord_3226596) baseStart_3226596 baseEnd_3226596 := by
    simpa [prefixWord, tailWord_3226596, baseEnd_3226596] using wordTrace_append hprefix tailTrace_3226596
  have hstable : (prefixWord ++ tailWord_3226596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226596).length < 2 ^ (prefixWord ++ tailWord_3226596).sum := by decide
  have hdescent : baseEnd_3226596 < baseStart_3226596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226649 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 8]
def baseStart_3226649 : Nat := 118140960795 + 3226649 * 2 ^ 59
def prefixEnd_3226649 : Nat := 4983230072969 + 3 ^ 40 * 3226649 * 2
def baseEnd_3226649 : Nat := 184091315594361272738713

theorem tailTrace_3226649 : CollatzResearch.WordTrace tailWord_3226649 prefixEnd_3226649 184091315594361272738713 := by
  unfold tailWord_3226649
  simp only [CollatzResearch.WordTrace]
  refine ⟨117685557287409215621563001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78457038191606143747708667 117685557287409215621563001)
  ·
    refine ⟨88264167965556911716172251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117685557287409215621563001 88264167965556911716172251)
    ·
      refine ⟨132396251948335367574258377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88264167965556911716172251 132396251948335367574258377)
      ·
        refine ⟨99297188961251525680693783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132396251948335367574258377 99297188961251525680693783)
        ·
          refine ⟨148945783441877288521040675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99297188961251525680693783 148945783441877288521040675)
          ·
            refine ⟨223418675162815932781561013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148945783441877288521040675 223418675162815932781561013)
            ·
              refine ⟨20945500796513993698271345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223418675162815932781561013 20945500796513993698271345)
              ·
                refine ⟨15709125597385495273703509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20945500796513993698271345 15709125597385495273703509)
                ·
                  refine ⟨184091315594361272738713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15709125597385495273703509 184091315594361272738713)
                  ·
                    rfl

theorem cell23_3226649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_3226649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226649 prefixEnd_3226649 := by exact prefixLift 3226649
  have htrace : WordTrace (prefixWord ++ tailWord_3226649) baseStart_3226649 baseEnd_3226649 := by
    simpa [prefixWord, tailWord_3226649, baseEnd_3226649] using wordTrace_append hprefix tailTrace_3226649
  have hstable : (prefixWord ++ tailWord_3226649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226649).length < 2 ^ (prefixWord ++ tailWord_3226649).sum := by decide
  have hdescent : baseEnd_3226649 < baseStart_3226649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226679 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 9]
def baseStart_3226679 : Nat := 118140960795 + 3226679 * 2 ^ 59
def prefixEnd_3226679 : Nat := 4983230072969 + 3 ^ 40 * 3226679 * 2
def baseEnd_3226679 : Nat := 552279081589628779091093

theorem tailTrace_3226679 : CollatzResearch.WordTrace tailWord_3226679 prefixEnd_3226679 552279081589628779091093 := by
  unfold tailWord_3226679
  simp only [CollatzResearch.WordTrace]
  refine ⟨117686651477300530745155091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78457767651533687163436727 117686651477300530745155091)
  ·
    refine ⟨176529977215950796117732637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117686651477300530745155091 176529977215950796117732637)
    ·
      refine ⟨66198741455981548544149739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176529977215950796117732637 66198741455981548544149739)
      ·
        refine ⟨99298112183972322816224609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66198741455981548544149739 99298112183972322816224609)
        ·
          refine ⟨74473584137979242112168457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99298112183972322816224609 74473584137979242112168457)
          ·
            refine ⟨55855188103484431584126343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74473584137979242112168457 55855188103484431584126343)
            ·
              refine ⟨83782782155226647376189515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55855188103484431584126343 83782782155226647376189515)
              ·
                refine ⟨125674173232839971064284273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83782782155226647376189515 125674173232839971064284273)
                ·
                  refine ⟨94255629924629978298213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125674173232839971064284273 94255629924629978298213205)
                  ·
                    refine ⟨552279081589628779091093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94255629924629978298213205 552279081589628779091093)
                    ·
                      rfl

theorem cell23_3226679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_3226679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226679 prefixEnd_3226679 := by exact prefixLift 3226679
  have htrace : WordTrace (prefixWord ++ tailWord_3226679) baseStart_3226679 baseEnd_3226679 := by
    simpa [prefixWord, tailWord_3226679, baseEnd_3226679] using wordTrace_append hprefix tailTrace_3226679
  have hstable : (prefixWord ++ tailWord_3226679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226679).length < 2 ^ (prefixWord ++ tailWord_3226679).sum := by decide
  have hdescent : baseEnd_3226679 < baseStart_3226679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226693 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_3226693 : Nat := 118140960795 + 3226693 * 2 ^ 59
def prefixEnd_3226693 : Nat := 4983230072969 + 3 ^ 40 * 3226693 * 2
def baseEnd_3226693 : Nat := 1656844433498049282498215

theorem tailTrace_3226693 : CollatzResearch.WordTrace tailWord_3226693 prefixEnd_3226693 1656844433498049282498215 := by
  unfold tailWord_3226693
  simp only [CollatzResearch.WordTrace]
  refine ⟨117687162099249811136164733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78458108066166540757443155 117687162099249811136164733)
  ·
    refine ⟨44132685787218679176061775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117687162099249811136164733 44132685787218679176061775)
    ·
      refine ⟨66199028680828018764092663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44132685787218679176061775 66199028680828018764092663)
      ·
        refine ⟨99298543021242028146138995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66199028680828018764092663 99298543021242028146138995)
        ·
          refine ⟨148947814531863042219208493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99298543021242028146138995 148947814531863042219208493)
          ·
            refine ⟨55855430449448640832203185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148947814531863042219208493 55855430449448640832203185)
            ·
              refine ⟨41891572837086480624152389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55855430449448640832203185 41891572837086480624152389)
              ·
                refine ⟨7854669906953715117028573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41891572837086480624152389 7854669906953715117028573)
                ·
                  refine ⟨2945501215107643168885715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7854669906953715117028573 2945501215107643168885715)
                  ·
                    refine ⟨4418251822661464753328573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945501215107643168885715 4418251822661464753328573)
                    ·
                      refine ⟨1656844433498049282498215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4418251822661464753328573 1656844433498049282498215)
                      ·
                        rfl

theorem cell23_3226693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_3226693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226693 prefixEnd_3226693 := by exact prefixLift 3226693
  have htrace : WordTrace (prefixWord ++ tailWord_3226693) baseStart_3226693 baseEnd_3226693 := by
    simpa [prefixWord, tailWord_3226693, baseEnd_3226693] using wordTrace_append hprefix tailTrace_3226693
  have hstable : (prefixWord ++ tailWord_3226693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226693).length < 2 ^ (prefixWord ++ tailWord_3226693).sum := by decide
  have hdescent : baseEnd_3226693 < baseStart_3226693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226696 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3226696 : Nat := 118140960795 + 3226696 * 2 ^ 59
def prefixEnd_3226696 : Nat := 4983230072969 + 3 ^ 40 * 3226696 * 2
def baseEnd_3226696 : Nat := 552281991313337590253567

theorem tailTrace_3226696 : CollatzResearch.WordTrace tailWord_3226696 prefixEnd_3226696 552281991313337590253567 := by
  unfold tailWord_3226696
  simp only [CollatzResearch.WordTrace]
  refine ⟨58843635759119471324261971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78458181012159295099015961 58843635759119471324261971)
  ·
    refine ⟨88265453638679206986392957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58843635759119471324261971 88265453638679206986392957)
    ·
      refine ⟨33099545114504702619897359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88265453638679206986392957 33099545114504702619897359)
      ·
        refine ⟨49649317671757053929846039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33099545114504702619897359 49649317671757053929846039)
        ·
          refine ⟨74473976507635580894769059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49649317671757053929846039 74473976507635580894769059)
          ·
            refine ⟨111710964761453371342153589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74473976507635580894769059 111710964761453371342153589)
            ·
              refine ⟨10472902946386253563326899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111710964761453371342153589 10472902946386253563326899)
              ·
                refine ⟨15709354419579380344990349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10472902946386253563326899 15709354419579380344990349)
                ·
                  refine ⟨5891007907342267629371381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15709354419579380344990349 5891007907342267629371381)
                  ·
                    refine ⟨552281991313337590253567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5891007907342267629371381 552281991313337590253567)
                    ·
                      rfl

theorem cell23_3226696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3226696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226696 prefixEnd_3226696 := by exact prefixLift 3226696
  have htrace : WordTrace (prefixWord ++ tailWord_3226696) baseStart_3226696 baseEnd_3226696 := by
    simpa [prefixWord, tailWord_3226696, baseEnd_3226696] using wordTrace_append hprefix tailTrace_3226696
  have hstable : (prefixWord ++ tailWord_3226696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226696).length < 2 ^ (prefixWord ++ tailWord_3226696).sum := by decide
  have hdescent : baseEnd_3226696 < baseStart_3226696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226727 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_3226727 : Nat := 118140960795 + 3226727 * 2 ^ 59
def prefixEnd_3226727 : Nat := 4983230072969 + 3 ^ 40 * 3226727 * 2
def baseEnd_3226727 : Nat := 1656861891840302149473059

theorem tailTrace_3226727 : CollatzResearch.WordTrace tailWord_3226727 prefixEnd_3226727 1656861891840302149473059 := by
  unfold tailWord_3226727
  simp only [CollatzResearch.WordTrace]
  refine ⟨117688402181126634942902435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78458934787417756628601623 117688402181126634942902435)
  ·
    refine ⟨176532603271689952414353653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117688402181126634942902435 176532603271689952414353653)
    ·
      refine ⟨16549931556720933038845655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176532603271689952414353653 16549931556720933038845655)
      ·
        refine ⟨24824897335081399558268483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549931556720933038845655 24824897335081399558268483)
        ·
          refine ⟨37237346002622099337402725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24824897335081399558268483 37237346002622099337402725)
          ·
            refine ⟨6982002375491643625763011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37237346002622099337402725 6982002375491643625763011)
            ·
              refine ⟨10473003563237465438644517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982002375491643625763011 10473003563237465438644517)
              ·
                refine ⟨1963688168107024769745847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10473003563237465438644517 1963688168107024769745847)
                ·
                  refine ⟨2945532252160537154618771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963688168107024769745847 2945532252160537154618771)
                  ·
                    refine ⟨4418298378240805731928157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945532252160537154618771 4418298378240805731928157)
                    ·
                      refine ⟨1656861891840302149473059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4418298378240805731928157 1656861891840302149473059)
                      ·
                        rfl

theorem cell23_3226727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_3226727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226727 prefixEnd_3226727 := by exact prefixLift 3226727
  have htrace : WordTrace (prefixWord ++ tailWord_3226727) baseStart_3226727 baseEnd_3226727 := by
    simpa [prefixWord, tailWord_3226727, baseEnd_3226727] using wordTrace_append hprefix tailTrace_3226727
  have hstable : (prefixWord ++ tailWord_3226727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226727).length < 2 ^ (prefixWord ++ tailWord_3226727).sum := by decide
  have hdescent : baseEnd_3226727 < baseStart_3226727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226733 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3226733 : Nat := 118140960795 + 3226733 * 2 ^ 59
def prefixEnd_3226733 : Nat := 4983230072969 + 3 ^ 40 * 3226733 * 2
def baseEnd_3226733 : Nat := 1656864972724229125998031

theorem tailTrace_3226733 : CollatzResearch.WordTrace tailWord_3226733 prefixEnd_3226733 1656864972724229125998031 := by
  unfold tailWord_3226733
  simp only [CollatzResearch.WordTrace]
  refine ⟨117688621019104897967620853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78459080679403265311747235 117688621019104897967620853)
  ·
    refine ⟨11033308220541084184464455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117688621019104897967620853 11033308220541084184464455)
    ·
      refine ⟨16549962330811626276696683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033308220541084184464455 16549962330811626276696683)
      ·
        refine ⟨24824943496217439415045025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549962330811626276696683 24824943496217439415045025)
        ·
          refine ⟨18618707622163079561283769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24824943496217439415045025 18618707622163079561283769)
          ·
            refine ⟨13964030716622309670962827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18618707622163079561283769 13964030716622309670962827)
            ·
              refine ⟨20946046074933464506444241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964030716622309670962827 20946046074933464506444241)
              ·
                refine ⟨15709534556200098379833181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20946046074933464506444241 15709534556200098379833181)
                ·
                  refine ⟨5891075458575036892437443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15709534556200098379833181 5891075458575036892437443)
                  ·
                    refine ⟨8836613187862555338656165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891075458575036892437443 8836613187862555338656165)
                    ·
                      refine ⟨1656864972724229125998031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8836613187862555338656165 1656864972724229125998031)
                      ·
                        rfl

theorem cell23_3226733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3226733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226733 prefixEnd_3226733 := by exact prefixLift 3226733
  have htrace : WordTrace (prefixWord ++ tailWord_3226733) baseStart_3226733 baseEnd_3226733 := by
    simpa [prefixWord, tailWord_3226733, baseEnd_3226733] using wordTrace_append hprefix tailTrace_3226733
  have hstable : (prefixWord ++ tailWord_3226733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226733).length < 2 ^ (prefixWord ++ tailWord_3226733).sum := by decide
  have hdescent : baseEnd_3226733 < baseStart_3226733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226736 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_3226736 : Nat := 118140960795 + 3226736 * 2 ^ 59
def prefixEnd_3226736 : Nat := 4983230072969 + 3 ^ 40 * 3226736 * 2
def baseEnd_3226736 : Nat := 1656866513166192614260517

theorem tailTrace_3226736 : CollatzResearch.WordTrace tailWord_3226736 prefixEnd_3226736 1656866513166192614260517 := by
  unfold tailWord_3226736
  simp only [CollatzResearch.WordTrace]
  refine ⟨58844365219047014739990031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78459153625396019653320041 58844365219047014739990031)
  ·
    refine ⟨88266547828570522109985047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58844365219047014739990031 88266547828570522109985047)
    ·
      refine ⟨132399821742855783164977571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88266547828570522109985047 132399821742855783164977571)
      ·
        refine ⟨198599732614283674747466357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132399821742855783164977571 198599732614283674747466357)
        ·
          refine ⟨18618724932589094507574971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198599732614283674747466357 18618724932589094507574971)
          ·
            refine ⟨27928087398883641761362457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18618724932589094507574971 27928087398883641761362457)
            ·
              refine ⟨20946065549162731321021843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27928087398883641761362457 20946065549162731321021843)
              ·
                refine ⟨31419098323744096981532765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20946065549162731321021843 31419098323744096981532765)
                ·
                  refine ⟨11782161871404036368074787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31419098323744096981532765 11782161871404036368074787)
                  ·
                    refine ⟨17673242807106054552112181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11782161871404036368074787 17673242807106054552112181)
                    ·
                      refine ⟨1656866513166192614260517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17673242807106054552112181 1656866513166192614260517)
                      ·
                        rfl

theorem cell23_3226736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_3226736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226736 prefixEnd_3226736 := by exact prefixLift 3226736
  have htrace : WordTrace (prefixWord ++ tailWord_3226736) baseStart_3226736 baseEnd_3226736 := by
    simpa [prefixWord, tailWord_3226736, baseEnd_3226736] using wordTrace_append hprefix tailTrace_3226736
  have hstable : (prefixWord ++ tailWord_3226736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226736).length < 2 ^ (prefixWord ++ tailWord_3226736).sum := by decide
  have hdescent : baseEnd_3226736 < baseStart_3226736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226743 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 2, 4]
def baseStart_3226743 : Nat := 118140960795 + 3226743 * 2 ^ 59
def prefixEnd_3226743 : Nat := 4983230072969 + 3 ^ 40 * 3226743 * 2
def baseEnd_3226743 : Nat := 552290035843591362290995

theorem tailTrace_3226743 : CollatzResearch.WordTrace tailWord_3226743 prefixEnd_3226743 552290035843591362290995 := by
  unfold tailWord_3226743
  simp only [CollatzResearch.WordTrace]
  refine ⟨117688985749068669675484883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78459323832712446450323255 117688985749068669675484883)
  ·
    refine ⟨176533478623603004513227325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117688985749068669675484883 176533478623603004513227325)
    ·
      refine ⟨66200054483851126692460247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176533478623603004513227325 66200054483851126692460247)
      ·
        refine ⟨99300081725776690038690371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66200054483851126692460247 99300081725776690038690371)
        ·
          refine ⟨148950122588665035058035557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99300081725776690038690371 148950122588665035058035557)
          ·
            refine ⟨27928147985374694073381667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148950122588665035058035557 27928147985374694073381667)
            ·
              refine ⟨41892221978062041110072501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27928147985374694073381667 41892221978062041110072501)
              ·
                refine ⟨3927395810443316354069297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41892221978062041110072501 3927395810443316354069297)
                ·
                  refine ⟨2945546857832487265551973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927395810443316354069297 2945546857832487265551973)
                  ·
                    refine ⟨552290035843591362290995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2945546857832487265551973 552290035843591362290995)
                    ·
                      rfl

theorem cell23_3226743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_3226743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226743 prefixEnd_3226743 := by exact prefixLift 3226743
  have htrace : WordTrace (prefixWord ++ tailWord_3226743) baseStart_3226743 baseEnd_3226743 := by
    simpa [prefixWord, tailWord_3226743, baseEnd_3226743] using wordTrace_append hprefix tailTrace_3226743
  have hstable : (prefixWord ++ tailWord_3226743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226743).length < 2 ^ (prefixWord ++ tailWord_3226743).sum := by decide
  have hdescent : baseEnd_3226743 < baseStart_3226743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226794 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3226794 : Nat := 118140960795 + 3226794 * 2 ^ 59
def prefixEnd_3226794 : Nat := 4983230072969 + 3 ^ 40 * 3226794 * 2
def baseEnd_3226794 : Nat := 552298765014717795778417

theorem tailTrace_3226794 : CollatzResearch.WordTrace tailWord_3226794 prefixEnd_3226794 552298765014717795778417 := by
  unfold tailWord_3226794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29422711467970976346397859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78460563914589270257060957 29422711467970976346397859)
  ·
    refine ⟨44134067201956464519596789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29422711467970976346397859 44134067201956464519596789)
    ·
      refine ⟨4137568800183418548712199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44134067201956464519596789 4137568800183418548712199)
      ·
        refine ⟨6206353200275127823068299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137568800183418548712199 6206353200275127823068299)
        ·
          refine ⟨9309529800412691734602449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206353200275127823068299 9309529800412691734602449)
          ·
            refine ⟨6982147350309518800951837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309529800412691734602449 6982147350309518800951837)
            ·
              refine ⟨2618305256366069550356939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6982147350309518800951837 2618305256366069550356939)
              ·
                refine ⟨3927457884549104325535409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618305256366069550356939 3927457884549104325535409)
                ·
                  refine ⟨2945593413411828244151557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927457884549104325535409 2945593413411828244151557)
                  ·
                    refine ⟨552298765014717795778417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2945593413411828244151557 552298765014717795778417)
                    ·
                      rfl

theorem cell23_3226794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3226794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226794 prefixEnd_3226794 := by exact prefixLift 3226794
  have htrace : WordTrace (prefixWord ++ tailWord_3226794) baseStart_3226794 baseEnd_3226794 := by
    simpa [prefixWord, tailWord_3226794, baseEnd_3226794] using wordTrace_append hprefix tailTrace_3226794
  have hstable : (prefixWord ++ tailWord_3226794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226794).length < 2 ^ (prefixWord ++ tailWord_3226794).sum := by decide
  have hdescent : baseEnd_3226794 < baseStart_3226794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226797 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3226797 : Nat := 118140960795 + 3226797 * 2 ^ 59
def prefixEnd_3226797 : Nat := 4983230072969 + 3 ^ 40 * 3226797 * 2
def baseEnd_3226797 : Nat := 1656897835486116875597737

theorem tailTrace_3226797 : CollatzResearch.WordTrace tailWord_3226797 prefixEnd_3226797 1656897835486116875597737 := by
  unfold tailWord_3226797
  simp only [CollatzResearch.WordTrace]
  refine ⟨117690955290873036897950645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78460636860582024598633763 117690955290873036897950645)
  ·
    refine ⟨11033527058519347209182873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117690955290873036897950645 11033527058519347209182873)
    ·
      refine ⟨8275145293889510406887155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11033527058519347209182873 8275145293889510406887155)
      ·
        refine ⟨12412717940834265610330733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275145293889510406887155 12412717940834265610330733)
        ·
          refine ⟨4654769227812849603874025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12412717940834265610330733 4654769227812849603874025)
          ·
            refine ⟨3491076920859637202905519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654769227812849603874025 3491076920859637202905519)
            ·
              refine ⟨5236615381289455804358279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491076920859637202905519 5236615381289455804358279)
              ·
                refine ⟨7854923071934183706537419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236615381289455804358279 7854923071934183706537419)
                ·
                  refine ⟨11782384607901275559806129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854923071934183706537419 11782384607901275559806129)
                  ·
                    refine ⟨8836788455925956669854597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11782384607901275559806129 8836788455925956669854597)
                    ·
                      refine ⟨1656897835486116875597737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8836788455925956669854597 1656897835486116875597737)
                      ·
                        rfl

theorem cell23_3226797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3226797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226797 prefixEnd_3226797 := by exact prefixLift 3226797
  have htrace : WordTrace (prefixWord ++ tailWord_3226797) baseStart_3226797 baseEnd_3226797 := by
    simpa [prefixWord, tailWord_3226797, baseEnd_3226797] using wordTrace_append hprefix tailTrace_3226797
  have hstable : (prefixWord ++ tailWord_3226797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226797).length < 2 ^ (prefixWord ++ tailWord_3226797).sum := by decide
  have hdescent : baseEnd_3226797 < baseStart_3226797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226817 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3226817 : Nat := 118140960795 + 3226817 * 2 ^ 59
def prefixEnd_3226817 : Nat := 4983230072969 + 3 ^ 40 * 3226817 * 2
def baseEnd_3226817 : Nat := 1656908105099206797347645

theorem tailTrace_3226817 : CollatzResearch.WordTrace tailWord_3226817 prefixEnd_3226817 1656908105099206797347645 := by
  unfold tailWord_3226817
  simp only [CollatzResearch.WordTrace]
  refine ⟨117691684750800580313678705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78461123167200386875785803 117691684750800580313678705)
  ·
    refine ⟨88268763563100435235259029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117691684750800580313678705 88268763563100435235259029)
    ·
      refine ⟨4137598292020332901652767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88268763563100435235259029 4137598292020332901652767)
      ·
        refine ⟨6206397438030499352479151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137598292020332901652767 6206397438030499352479151)
        ·
          refine ⟨9309596157045749028718727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206397438030499352479151 9309596157045749028718727)
          ·
            refine ⟨13964394235568623543078091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309596157045749028718727 13964394235568623543078091)
            ·
              refine ⟨20946591353352935314617137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964394235568623543078091 20946591353352935314617137)
              ·
                refine ⟨15709943515014701485962853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20946591353352935314617137 15709943515014701485962853)
                ·
                  refine ⟨2945614409065256528618035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15709943515014701485962853 2945614409065256528618035)
                  ·
                    refine ⟨4418421613597884792927053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945614409065256528618035 4418421613597884792927053)
                    ·
                      refine ⟨1656908105099206797347645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4418421613597884792927053 1656908105099206797347645)
                      ·
                        rfl

theorem cell23_3226817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3226817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226817 prefixEnd_3226817 := by exact prefixLift 3226817
  have htrace : WordTrace (prefixWord ++ tailWord_3226817) baseStart_3226817 baseEnd_3226817 := by
    simpa [prefixWord, tailWord_3226817, baseEnd_3226817] using wordTrace_append hprefix tailTrace_3226817
  have hstable : (prefixWord ++ tailWord_3226817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226817).length < 2 ^ (prefixWord ++ tailWord_3226817).sum := by decide
  have hdescent : baseEnd_3226817 < baseStart_3226817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226903 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3226903 : Nat := 118140960795 + 3226903 * 2 ^ 59
def prefixEnd_3226903 : Nat := 4983230072969 + 3 ^ 40 * 3226903 * 2
def baseEnd_3226903 : Nat := 1656952264435493460872249

theorem tailTrace_3226903 : CollatzResearch.WordTrace tailWord_3226903 prefixEnd_3226903 1656952264435493460872249 := by
  unfold tailWord_3226903
  simp only [CollatzResearch.WordTrace]
  refine ⟨117694821428489017001309363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78463214285659344667539575 117694821428489017001309363)
  ·
    refine ⟨176542232142733525501964045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117694821428489017001309363 176542232142733525501964045)
    ·
      refine ⟨66203337053525072063236517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176542232142733525501964045 66203337053525072063236517)
      ·
        refine ⟨12413125697535951011856847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66203337053525072063236517 12413125697535951011856847)
        ·
          refine ⟨18619688546303926517785271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12413125697535951011856847 18619688546303926517785271)
          ·
            refine ⟨27929532819455889776677907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18619688546303926517785271 27929532819455889776677907)
            ·
              refine ⟨41894299229183834665016861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27929532819455889776677907 41894299229183834665016861)
              ·
                refine ⟨15710362210943937999381323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41894299229183834665016861 15710362210943937999381323)
                ·
                  refine ⟨23565543316415906999071985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15710362210943937999381323 23565543316415906999071985)
                  ·
                    refine ⟨17674157487311930249303989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23565543316415906999071985 17674157487311930249303989)
                    ·
                      refine ⟨1656952264435493460872249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17674157487311930249303989 1656952264435493460872249)
                      ·
                        rfl

theorem cell23_3226903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3226903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226903 prefixEnd_3226903 := by exact prefixLift 3226903
  have htrace : WordTrace (prefixWord ++ tailWord_3226903) baseStart_3226903 baseEnd_3226903 := by
    simpa [prefixWord, tailWord_3226903, baseEnd_3226903] using wordTrace_append hprefix tailTrace_3226903
  have hstable : (prefixWord ++ tailWord_3226903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226903).length < 2 ^ (prefixWord ++ tailWord_3226903).sum := by decide
  have hdescent : baseEnd_3226903 < baseStart_3226903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226913 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3226913 : Nat := 118140960795 + 3226913 * 2 ^ 59
def prefixEnd_3226913 : Nat := 4983230072969 + 3 ^ 40 * 3226913 * 2
def baseEnd_3226913 : Nat := 1656957399242038421747203

theorem tailTrace_3226913 : CollatzResearch.WordTrace tailWord_3226913 prefixEnd_3226913 1656957399242038421747203 := by
  unfold tailWord_3226913
  simp only [CollatzResearch.WordTrace]
  refine ⟨117695186158452788709173393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78463457438968525806115595 117695186158452788709173393)
  ·
    refine ⟨88271389618839591531880045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117695186158452788709173393 88271389618839591531880045)
    ·
      refine ⟨33101771107064846824455017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88271389618839591531880045 33101771107064846824455017)
      ·
        refine ⟨24826328330298635118341263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33101771107064846824455017 24826328330298635118341263)
        ·
          refine ⟨37239492495447952677511895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24826328330298635118341263 37239492495447952677511895)
          ·
            refine ⟨55859238743171929016267843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37239492495447952677511895 55859238743171929016267843)
            ·
              refine ⟨83788858114757893524401765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55859238743171929016267843 83788858114757893524401765)
              ·
                refine ⟨15710410896517105035825331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83788858114757893524401765 15710410896517105035825331)
                ·
                  refine ⟨23565616344775657553737997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15710410896517105035825331 23565616344775657553737997)
                  ·
                    refine ⟨8837106129290871582651749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23565616344775657553737997 8837106129290871582651749)
                    ·
                      refine ⟨1656957399242038421747203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8837106129290871582651749 1656957399242038421747203)
                      ·
                        rfl

theorem cell23_3226913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3226913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226913 prefixEnd_3226913 := by exact prefixLift 3226913
  have htrace : WordTrace (prefixWord ++ tailWord_3226913) baseStart_3226913 baseEnd_3226913 := by
    simpa [prefixWord, tailWord_3226913, baseEnd_3226913] using wordTrace_append hprefix tailTrace_3226913
  have hstable : (prefixWord ++ tailWord_3226913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226913).length < 2 ^ (prefixWord ++ tailWord_3226913).sum := by decide
  have hdescent : baseEnd_3226913 < baseStart_3226913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226930 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3226930 : Nat := 118140960795 + 3226930 * 2 ^ 59
def prefixEnd_3226930 : Nat := 4983230072969 + 3 ^ 40 * 3226930 * 2
def baseEnd_3226930 : Nat := 1656966128413164855234625

theorem tailTrace_3226930 : CollatzResearch.WordTrace tailWord_3226930 prefixEnd_3226930 1656966128413164855234625 := by
  unfold tailWord_3226930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423951549847800153135561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78463870799594133741694829 29423951549847800153135561)
  ·
    refine ⟨22067963662385850114851671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29423951549847800153135561 22067963662385850114851671)
    ·
      refine ⟨33101945493578775172277507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22067963662385850114851671 33101945493578775172277507)
      ·
        refine ⟨49652918240368162758416261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33101945493578775172277507 49652918240368162758416261)
        ·
          refine ⟨9309922170069030517203049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49652918240368162758416261 9309922170069030517203049)
          ·
            refine ⟨6982441627551772887902287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309922170069030517203049 6982441627551772887902287)
            ·
              refine ⟨10473662441327659331853431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982441627551772887902287 10473662441327659331853431)
              ·
                refine ⟨15710493661991488997780147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10473662441327659331853431 15710493661991488997780147)
                ·
                  refine ⟨23565740492987233496670221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15710493661991488997780147 23565740492987233496670221)
                  ·
                    refine ⟨8837152684870212561251333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23565740492987233496670221 8837152684870212561251333)
                    ·
                      refine ⟨1656966128413164855234625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8837152684870212561251333 1656966128413164855234625)
                      ·
                        rfl

theorem cell23_3226930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3226930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226930 prefixEnd_3226930 := by exact prefixLift 3226930
  have htrace : WordTrace (prefixWord ++ tailWord_3226930) baseStart_3226930 baseEnd_3226930 := by
    simpa [prefixWord, tailWord_3226930, baseEnd_3226930] using wordTrace_append hprefix tailTrace_3226930
  have hstable : (prefixWord ++ tailWord_3226930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226930).length < 2 ^ (prefixWord ++ tailWord_3226930).sum := by decide
  have hdescent : baseEnd_3226930 < baseStart_3226930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3226943 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_3226943 : Nat := 118140960795 + 3226943 * 2 ^ 59
def prefixEnd_3226943 : Nat := 4983230072969 + 3 ^ 40 * 3226943 * 2
def baseEnd_3226943 : Nat := 1656972803661673304372065

theorem tailTrace_3226943 : CollatzResearch.WordTrace tailWord_3226943 prefixEnd_3226943 1656972803661673304372065 := by
  unfold tailWord_3226943
  simp only [CollatzResearch.WordTrace]
  refine ⟨117696280348344103832765483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78464186898896069221843655 117696280348344103832765483)
  ·
    refine ⟨176544420522516155749148225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117696280348344103832765483 176544420522516155749148225)
    ·
      refine ⟨132408315391887116811861169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176544420522516155749148225 132408315391887116811861169)
      ·
        refine ⟨99306236543915337608895877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132408315391887116811861169 99306236543915337608895877)
        ·
          refine ⟨18619919351984125801667977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99306236543915337608895877 18619919351984125801667977)
          ·
            refine ⟨13964939513988094351250983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18619919351984125801667977 13964939513988094351250983)
            ·
              refine ⟨20947409270982141526876475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964939513988094351250983 20947409270982141526876475)
              ·
                refine ⟨31421113906473212290314713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20947409270982141526876475 31421113906473212290314713)
                ·
                  refine ⟨23565835429854909217736035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31421113906473212290314713 23565835429854909217736035)
                  ·
                    refine ⟨35348753144782363826604053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23565835429854909217736035 35348753144782363826604053)
                    ·
                      refine ⟨1656972803661673304372065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35348753144782363826604053 1656972803661673304372065)
                      ·
                        rfl

theorem cell23_3226943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_3226943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3226943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3226943 prefixEnd_3226943 := by exact prefixLift 3226943
  have htrace : WordTrace (prefixWord ++ tailWord_3226943) baseStart_3226943 baseEnd_3226943 := by
    simpa [prefixWord, tailWord_3226943, baseEnd_3226943] using wordTrace_append hprefix tailTrace_3226943
  have hstable : (prefixWord ++ tailWord_3226943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3226943).length < 2 ^ (prefixWord ++ tailWord_3226943).sum := by decide
  have hdescent : baseEnd_3226943 < baseStart_3226943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3226943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227020 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3227020 : Nat := 118140960795 + 3227020 * 2 ^ 59
def prefixEnd_3227020 : Nat := 4983230072969 + 3 ^ 40 * 3227020 * 2
def baseEnd_3227020 : Nat := 1657012341672069503109211

theorem tailTrace_3227020 : CollatzResearch.WordTrace tailWord_3227020 prefixEnd_3227020 1657012341672069503109211 := by
  unfold tailWord_3227020
  simp only [CollatzResearch.WordTrace]
  refine ⟨58849544384532572991659257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78466059179376763988879009 58849544384532572991659257)
  ·
    refine ⟨44137158288399429743744443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58849544384532572991659257 44137158288399429743744443)
    ·
      refine ⟨66205737432599144615616665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44137158288399429743744443 66205737432599144615616665)
      ·
        refine ⟨49654303074449358461712499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66205737432599144615616665 49654303074449358461712499)
        ·
          refine ⟨74481454611674037692568749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49654303074449358461712499 74481454611674037692568749)
          ·
            refine ⟨27930545479377764134713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74481454611674037692568749 27930545479377764134713281)
            ·
              refine ⟨20947909109533323101034961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27930545479377764134713281 20947909109533323101034961)
              ·
                refine ⟨15710931832149992325776221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20947909109533323101034961 15710931832149992325776221)
                ·
                  refine ⟨5891599437056247122166083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15710931832149992325776221 5891599437056247122166083)
                  ·
                    refine ⟨8837399155584370683249125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891599437056247122166083 8837399155584370683249125)
                    ·
                      refine ⟨1657012341672069503109211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8837399155584370683249125 1657012341672069503109211)
                      ·
                        rfl

theorem cell23_3227020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3227020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227020 prefixEnd_3227020 := by exact prefixLift 3227020
  have htrace : WordTrace (prefixWord ++ tailWord_3227020) baseStart_3227020 baseEnd_3227020 := by
    simpa [prefixWord, tailWord_3227020, baseEnd_3227020] using wordTrace_append hprefix tailTrace_3227020
  have hstable : (prefixWord ++ tailWord_3227020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227020).length < 2 ^ (prefixWord ++ tailWord_3227020).sum := by decide
  have hdescent : baseEnd_3227020 < baseStart_3227020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227037 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3227037 : Nat := 118140960795 + 3227037 * 2 ^ 59
def prefixEnd_3227037 : Nat := 4983230072969 + 3 ^ 40 * 3227037 * 2
def baseEnd_3227037 : Nat := 1657021070843195936596633

theorem tailTrace_3227037 : CollatzResearch.WordTrace tailWord_3227037 prefixEnd_3227037 1657021070843195936596633 := by
  unfold tailWord_3227037
  simp only [CollatzResearch.WordTrace]
  refine ⟨117699708810003557886687365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78466472540002371924458243 117699708810003557886687365)
  ·
    refine ⟨22068695401875667103753881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117699708810003557886687365 22068695401875667103753881)
    ·
      refine ⟨16551521551406750327815411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22068695401875667103753881 16551521551406750327815411)
      ·
        refine ⟨24827282327110125491723117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16551521551406750327815411 24827282327110125491723117)
        ·
          refine ⟨9310230872666297059396169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24827282327110125491723117 9310230872666297059396169)
          ·
            refine ⟨6982673154499722794547127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9310230872666297059396169 6982673154499722794547127)
            ·
              refine ⟨10474009731749584191820691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982673154499722794547127 10474009731749584191820691)
              ·
                refine ⟨15711014597624376287731037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10474009731749584191820691 15711014597624376287731037)
                ·
                  refine ⟨5891630474109141107899139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15711014597624376287731037 5891630474109141107899139)
                  ·
                    refine ⟨8837445711163711661848709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891630474109141107899139 8837445711163711661848709)
                    ·
                      refine ⟨1657021070843195936596633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8837445711163711661848709 1657021070843195936596633)
                      ·
                        rfl

theorem cell23_3227037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3227037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227037 prefixEnd_3227037 := by exact prefixLift 3227037
  have htrace : WordTrace (prefixWord ++ tailWord_3227037) baseStart_3227037 baseEnd_3227037 := by
    simpa [prefixWord, tailWord_3227037, baseEnd_3227037] using wordTrace_append hprefix tailTrace_3227037
  have hstable : (prefixWord ++ tailWord_3227037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227037).length < 2 ^ (prefixWord ++ tailWord_3227037).sum := by decide
  have hdescent : baseEnd_3227037 < baseStart_3227037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227043 : List Nat := [1, 1, 1, 4, 1, 3, 1, 11]
def baseStart_3227043 : Nat := 118140960795 + 3227043 * 2 ^ 59
def prefixEnd_3227043 : Nat := 4983230072969 + 3 ^ 40 * 3227043 * 2
def baseEnd_3227043 : Nat := 61371264878782330115615

theorem tailTrace_3227043 : CollatzResearch.WordTrace tailWord_3227043 prefixEnd_3227043 61371264878782330115615 := by
  unfold tailWord_3227043
  simp only [CollatzResearch.WordTrace]
  refine ⟨117699927647981820911405783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78466618431987880607603855 117699927647981820911405783)
  ·
    refine ⟨176549891471972731367108675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117699927647981820911405783 176549891471972731367108675)
    ·
      refine ⟨264824837207959097050663013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176549891471972731367108675 264824837207959097050663013)
      ·
        refine ⟨49654656976492330696999315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264824837207959097050663013 49654656976492330696999315)
        ·
          refine ⟨74481985464738496045498973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49654656976492330696999315 74481985464738496045498973)
          ·
            refine ⟨27930744549276936017062115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74481985464738496045498973 27930744549276936017062115)
            ·
              refine ⟨41896116823915404025593173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27930744549276936017062115 41896116823915404025593173)
              ·
                refine ⟨61371264878782330115615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41896116823915404025593173 61371264878782330115615)
                ·
                  rfl

theorem cell23_3227043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 11].length) (baseStart_3227043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227043 prefixEnd_3227043 := by exact prefixLift 3227043
  have htrace : WordTrace (prefixWord ++ tailWord_3227043) baseStart_3227043 baseEnd_3227043 := by
    simpa [prefixWord, tailWord_3227043, baseEnd_3227043] using wordTrace_append hprefix tailTrace_3227043
  have hstable : (prefixWord ++ tailWord_3227043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227043).length < 2 ^ (prefixWord ++ tailWord_3227043).sum := by decide
  have hdescent : baseEnd_3227043 < baseStart_3227043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227060 : List Nat := [2, 5, 2, 14]
def baseStart_3227060 : Nat := 118140960795 + 3227060 * 2 ^ 59
def prefixEnd_3227060 : Nat := 4983230072969 + 3 ^ 40 * 3227060 * 2
def baseEnd_3227060 : Nat := 757673928165637561321

theorem tailTrace_3227060 : CollatzResearch.WordTrace tailWord_3227060 prefixEnd_3227060 757673928165637561321 := by
  unfold tailWord_3227060
  simp only [CollatzResearch.WordTrace]
  refine ⟨58850273844460116407387317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78467031792613488543183089 58850273844460116407387317)
  ·
    refine ⟨5517213172918135913192561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58850273844460116407387317 5517213172918135913192561)
    ·
      refine ⟨4137909879688601934894421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5517213172918135913192561 4137909879688601934894421)
      ·
        refine ⟨757673928165637561321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 4137909879688601934894421 757673928165637561321)
        ·
          rfl

theorem cell23_3227060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 14].length) (baseStart_3227060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227060 prefixEnd_3227060 := by exact prefixLift 3227060
  have htrace : WordTrace (prefixWord ++ tailWord_3227060) baseStart_3227060 baseEnd_3227060 := by
    simpa [prefixWord, tailWord_3227060, baseEnd_3227060] using wordTrace_append hprefix tailTrace_3227060
  have hstable : (prefixWord ++ tailWord_3227060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227060).length < 2 ^ (prefixWord ++ tailWord_3227060).sum := by decide
  have hdescent : baseEnd_3227060 < baseStart_3227060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227065 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3227065 : Nat := 118140960795 + 3227065 * 2 ^ 59
def prefixEnd_3227065 : Nat := 4983230072969 + 3 ^ 40 * 3227065 * 2
def baseEnd_3227065 : Nat := 1657035448301521827046505

theorem tailTrace_3227065 : CollatzResearch.WordTrace tailWord_3227065 prefixEnd_3227065 1657035448301521827046505 := by
  unfold tailWord_3227065
  simp only [CollatzResearch.WordTrace]
  refine ⟨117700730053902118668706649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78467153369268079112471099 117700730053902118668706649)
  ·
    refine ⟨88275547540426589001529987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117700730053902118668706649 88275547540426589001529987)
    ·
      refine ⟨132413321310639883502294981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88275547540426589001529987 132413321310639883502294981)
      ·
        refine ⟨24827497745744978156680309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132413321310639883502294981 24827497745744978156680309)
        ·
          refine ⟨2327577913663591702188779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24827497745744978156680309 2327577913663591702188779)
          ·
            refine ⟨3491366870495387553283169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327577913663591702188779 3491366870495387553283169)
            ·
              refine ⟨2618525152871540664962377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491366870495387553283169 2618525152871540664962377)
              ·
                refine ⟨1963893864653655498721783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618525152871540664962377 1963893864653655498721783)
                ·
                  refine ⟨2945840796980483248082675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963893864653655498721783 2945840796980483248082675)
                  ·
                    refine ⟨4418761195470724872124013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945840796980483248082675 4418761195470724872124013)
                    ·
                      refine ⟨1657035448301521827046505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4418761195470724872124013 1657035448301521827046505)
                      ·
                        rfl

theorem cell23_3227065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3227065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227065 prefixEnd_3227065 := by exact prefixLift 3227065
  have htrace : WordTrace (prefixWord ++ tailWord_3227065) baseStart_3227065 baseEnd_3227065 := by
    simpa [prefixWord, tailWord_3227065, baseEnd_3227065] using wordTrace_append hprefix tailTrace_3227065
  have hstable : (prefixWord ++ tailWord_3227065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227065).length < 2 ^ (prefixWord ++ tailWord_3227065).sum := by decide
  have hdescent : baseEnd_3227065 < baseStart_3227065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227094 : List Nat := [5, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3227094 : Nat := 118140960795 + 3227094 * 2 ^ 59
def prefixEnd_3227094 : Nat := 4983230072969 + 3 ^ 40 * 3227094 * 2
def baseEnd_3227094 : Nat := 61372234786685267169773

theorem tailTrace_3227094 : CollatzResearch.WordTrace tailWord_3227094 prefixEnd_3227094 61372234786685267169773 := by
  unfold tailWord_3227094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356361735674816038844521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78467858513864704414341557 7356361735674816038844521)
  ·
    refine ⟨5517271301756112029133391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7356361735674816038844521 5517271301756112029133391)
    ·
      refine ⟨8275906952634168043700087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517271301756112029133391 8275906952634168043700087)
      ·
        refine ⟨12413860428951252065550131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275906952634168043700087 12413860428951252065550131)
        ·
          refine ⟨18620790643426878098325197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12413860428951252065550131 18620790643426878098325197)
          ·
            refine ⟨6982796491285079286871949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18620790643426878098325197 6982796491285079286871949)
            ·
              refine ⟨2618548684231904732576981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6982796491285079286871949 2618548684231904732576981)
              ·
                refine ⟨61372234786685267169773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2618548684231904732576981 61372234786685267169773)
                ·
                  rfl

theorem cell23_3227094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3227094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227094 prefixEnd_3227094 := by exact prefixLift 3227094
  have htrace : WordTrace (prefixWord ++ tailWord_3227094) baseStart_3227094 baseEnd_3227094 := by
    simpa [prefixWord, tailWord_3227094, baseEnd_3227094] using wordTrace_append hprefix tailTrace_3227094
  have hstable : (prefixWord ++ tailWord_3227094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227094).length < 2 ^ (prefixWord ++ tailWord_3227094).sum := by decide
  have hdescent : baseEnd_3227094 < baseStart_3227094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227120 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_3227120 : Nat := 118140960795 + 3227120 * 2 ^ 59
def prefixEnd_3227120 : Nat := 4983230072969 + 3 ^ 40 * 3227120 * 2
def baseEnd_3227120 : Nat := 552354563245839703952917

theorem tailTrace_3227120 : CollatzResearch.WordTrace tailWord_3227120 prefixEnd_3227120 552354563245839703952917 := by
  unfold tailWord_3227120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58851368034351431530979407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78468490712468575374639209 58851368034351431530979407)
  ·
    refine ⟨88277052051527147296469111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58851368034351431530979407 88277052051527147296469111)
    ·
      refine ⟨132415578077290720944703667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88277052051527147296469111 132415578077290720944703667)
      ·
        refine ⟨198623367115936081417055501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132415578077290720944703667 198623367115936081417055501)
        ·
          refine ⟨74483762668476030531395813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198623367115936081417055501 74483762668476030531395813)
          ·
            refine ⟨13965705500339255724636715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74483762668476030531395813 13965705500339255724636715)
            ·
              refine ⟨20948558250508883586955073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13965705500339255724636715 20948558250508883586955073)
              ·
                refine ⟨15711418687881662690216305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20948558250508883586955073 15711418687881662690216305)
                ·
                  refine ⟨11783564015911247017662229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15711418687881662690216305 11783564015911247017662229)
                  ·
                    refine ⟨552354563245839703952917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11783564015911247017662229 552354563245839703952917)
                    ·
                      rfl

theorem cell23_3227120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_3227120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227120 prefixEnd_3227120 := by exact prefixLift 3227120
  have htrace : WordTrace (prefixWord ++ tailWord_3227120) baseStart_3227120 baseEnd_3227120 := by
    simpa [prefixWord, tailWord_3227120, baseEnd_3227120] using wordTrace_append hprefix tailTrace_3227120
  have hstable : (prefixWord ++ tailWord_3227120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227120).length < 2 ^ (prefixWord ++ tailWord_3227120).sum := by decide
  have hdescent : baseEnd_3227120 < baseStart_3227120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227121 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_3227121 : Nat := 118140960795 + 3227121 * 2 ^ 59
def prefixEnd_3227121 : Nat := 4983230072969 + 3 ^ 40 * 3227121 * 2
def baseEnd_3227121 : Nat := 1657064203218173607946247

theorem tailTrace_3227121 : CollatzResearch.WordTrace tailWord_3227121 prefixEnd_3227121 1657064203218173607946247 := by
  unfold tailWord_3227121
  simp only [CollatzResearch.WordTrace]
  refine ⟨117702772541699240232745217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78468515027799493488496811 117702772541699240232745217)
  ·
    refine ⟨88277079406274430174558913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117702772541699240232745217 88277079406274430174558913)
    ·
      refine ⟨66207809554705822630919185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88277079406274430174558913 66207809554705822630919185)
      ·
        refine ⟨49655857166029366973189389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66207809554705822630919185 49655857166029366973189389)
        ·
          refine ⟨18620946437261012614946021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49655857166029366973189389 18620946437261012614946021)
          ·
            refine ⟨3491427456986439865302379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18620946437261012614946021 3491427456986439865302379)
            ·
              refine ⟨5237141185479659797953569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491427456986439865302379 5237141185479659797953569)
              ·
                refine ⟨3927855889109744848465177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5237141185479659797953569 3927855889109744848465177)
                ·
                  refine ⟨2945891916832308636348883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927855889109744848465177 2945891916832308636348883)
                  ·
                    refine ⟨4418837875248462954523325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945891916832308636348883 4418837875248462954523325)
                    ·
                      refine ⟨1657064203218173607946247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4418837875248462954523325 1657064203218173607946247)
                      ·
                        rfl

theorem cell23_3227121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_3227121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227121 prefixEnd_3227121 := by exact prefixLift 3227121
  have htrace : WordTrace (prefixWord ++ tailWord_3227121) baseStart_3227121 baseEnd_3227121 := by
    simpa [prefixWord, tailWord_3227121, baseEnd_3227121] using wordTrace_append hprefix tailTrace_3227121
  have hstable : (prefixWord ++ tailWord_3227121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227121).length < 2 ^ (prefixWord ++ tailWord_3227121).sum := by decide
  have hdescent : baseEnd_3227121 < baseStart_3227121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227144 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_3227144 : Nat := 118140960795 + 3227144 * 2 ^ 59
def prefixEnd_3227144 : Nat := 4983230072969 + 3 ^ 40 * 3227144 * 2
def baseEnd_3227144 : Nat := 1657076013273227017958641

theorem tailTrace_3227144 : CollatzResearch.WordTrace tailWord_3227144 prefixEnd_3227144 1657076013273227017958641 := by
  unfold tailWord_3227144
  simp only [CollatzResearch.WordTrace]
  refine ⟨58851805710307957580416243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78469074280410610107221657 58851805710307957580416243)
  ·
    refine ⟨88277708565461936370624365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58851805710307957580416243 88277708565461936370624365)
    ·
      refine ⟨33104140712048226138984137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88277708565461936370624365 33104140712048226138984137)
      ·
        refine ⟨24828105534036169604238103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33104140712048226138984137 24828105534036169604238103)
        ·
          refine ⟨37242158301054254406357155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24828105534036169604238103 37242158301054254406357155)
          ·
            refine ⟨55863237451581381609535733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37242158301054254406357155 55863237451581381609535733)
            ·
              refine ⟨5237178511085754525893975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55863237451581381609535733 5237178511085754525893975)
              ·
                refine ⟨7855767766628631788840963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237178511085754525893975 7855767766628631788840963)
                ·
                  refine ⟨11783651649942947683261445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855767766628631788840963 11783651649942947683261445)
                  ·
                    refine ⟨2209434684364302690611521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11783651649942947683261445 2209434684364302690611521)
                    ·
                      refine ⟨1657076013273227017958641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2209434684364302690611521 1657076013273227017958641)
                      ·
                        rfl

theorem cell23_3227144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_3227144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227144 prefixEnd_3227144 := by exact prefixLift 3227144
  have htrace : WordTrace (prefixWord ++ tailWord_3227144) baseStart_3227144 baseEnd_3227144 := by
    simpa [prefixWord, tailWord_3227144, baseEnd_3227144] using wordTrace_append hprefix tailTrace_3227144
  have hstable : (prefixWord ++ tailWord_3227144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227144).length < 2 ^ (prefixWord ++ tailWord_3227144).sum := by decide
  have hdescent : baseEnd_3227144 < baseStart_3227144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227257 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 6]
def baseStart_3227257 : Nat := 118140960795 + 3227257 * 2 ^ 59
def prefixEnd_3227257 : Nat := 4983230072969 + 3 ^ 40 * 3227257 * 2
def baseEnd_3227257 : Nat := 184126004065242786205069

theorem tailTrace_3227257 : CollatzResearch.WordTrace tailWord_3227257 prefixEnd_3227257 184126004065242786205069 := by
  unfold tailWord_3227257
  simp only [CollatzResearch.WordTrace]
  refine ⟨117707732869206535459696025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78471821912804356973130683 117707732869206535459696025)
  ·
    refine ⟨88280799651904901594772019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117707732869206535459696025 88280799651904901594772019)
    ·
      refine ⟨132421199477857352392158029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88280799651904901594772019 132421199477857352392158029)
      ·
        refine ⟨49657949804196507147059261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132421199477857352392158029 49657949804196507147059261)
        ·
          refine ⟨18621731176573690180147223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49657949804196507147059261 18621731176573690180147223)
          ·
            refine ⟨27932596764860535270220835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18621731176573690180147223 27932596764860535270220835)
            ·
              refine ⟨41898895147290802905331253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27932596764860535270220835 41898895147290802905331253)
              ·
                refine ⟨3928021420058512772374805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41898895147290802905331253 3928021420058512772374805)
                ·
                  refine ⟨184126004065242786205069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3928021420058512772374805 184126004065242786205069)
                  ·
                    rfl

theorem cell23_3227257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_3227257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227257 prefixEnd_3227257 := by exact prefixLift 3227257
  have htrace : WordTrace (prefixWord ++ tailWord_3227257) baseStart_3227257 baseEnd_3227257 := by
    simpa [prefixWord, tailWord_3227257, baseEnd_3227257] using wordTrace_append hprefix tailTrace_3227257
  have hstable : (prefixWord ++ tailWord_3227257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227257).length < 2 ^ (prefixWord ++ tailWord_3227257).sum := by decide
  have hdescent : baseEnd_3227257 < baseStart_3227257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227268 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_3227268 : Nat := 118140960795 + 3227268 * 2 ^ 59
def prefixEnd_3227268 : Nat := 4983230072969 + 3 ^ 40 * 3227268 * 2
def baseEnd_3227268 : Nat := 1657139684874384532808071

theorem tailTrace_3227268 : CollatzResearch.WordTrace tailWord_3227268 prefixEnd_3227268 1657139684874384532808071 := by
  unfold tailWord_3227268
  simp only [CollatzResearch.WordTrace]
  refine ⟨58854067036083342169173229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78472089381444456225564305 58854067036083342169173229)
  ·
    refine ⟨22070275138531253313439961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58854067036083342169173229 22070275138531253313439961)
    ·
      refine ⟨16552706353898439985079971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22070275138531253313439961 16552706353898439985079971)
      ·
        refine ⟨24829059530847659977619957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16552706353898439985079971 24829059530847659977619957)
        ·
          refine ⟨2327724331016968122901871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24829059530847659977619957 2327724331016968122901871)
          ·
            refine ⟨3491586496525452184352807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327724331016968122901871 3491586496525452184352807)
            ·
              refine ⟨5237379744788178276529211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491586496525452184352807 5237379744788178276529211)
              ·
                refine ⟨7856069617182267414793817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237379744788178276529211 7856069617182267414793817)
                ·
                  refine ⟨5892052212886700561095363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7856069617182267414793817 5892052212886700561095363)
                  ·
                    refine ⟨8838078319330050841643045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5892052212886700561095363 8838078319330050841643045)
                    ·
                      refine ⟨1657139684874384532808071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8838078319330050841643045 1657139684874384532808071)
                      ·
                        rfl

theorem cell23_3227268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_3227268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227268 prefixEnd_3227268 := by exact prefixLift 3227268
  have htrace : WordTrace (prefixWord ++ tailWord_3227268) baseStart_3227268 baseEnd_3227268 := by
    simpa [prefixWord, tailWord_3227268, baseEnd_3227268] using wordTrace_append hprefix tailTrace_3227268
  have hstable : (prefixWord ++ tailWord_3227268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227268).length < 2 ^ (prefixWord ++ tailWord_3227268).sum := by decide
  have hdescent : baseEnd_3227268 < baseStart_3227268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227271 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3227271 : Nat := 118140960795 + 3227271 * 2 ^ 59
def prefixEnd_3227271 : Nat := 4983230072969 + 3 ^ 40 * 3227271 * 2
def baseEnd_3227271 : Nat := 1657141225316348021070557

theorem tailTrace_3227271 : CollatzResearch.WordTrace tailWord_3227271 prefixEnd_3227271 1657141225316348021070557 := by
  unfold tailWord_3227271
  simp only [CollatzResearch.WordTrace]
  refine ⟨117708243491155815850705667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78472162327437210567137111 117708243491155815850705667)
  ·
    refine ⟨176562365236733723776058501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117708243491155815850705667 176562365236733723776058501)
    ·
      refine ⟨33105443481887573208010969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176562365236733723776058501 33105443481887573208010969)
      ·
        refine ⟨24829082611415679906008227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33105443481887573208010969 24829082611415679906008227)
        ·
          refine ⟨37243623917123519859012341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24829082611415679906008227 37243623917123519859012341)
          ·
            refine ⟨3491589742230329986782407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37243623917123519859012341 3491589742230329986782407)
            ·
              refine ⟨5237384613345494980173611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491589742230329986782407 5237384613345494980173611)
              ·
                refine ⟨7856076920018242470260417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237384613345494980173611 7856076920018242470260417)
                ·
                  refine ⟨5892057690013681852695313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7856076920018242470260417 5892057690013681852695313)
                  ·
                    refine ⟨4419043267510261389521485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5892057690013681852695313 4419043267510261389521485)
                    ·
                      refine ⟨1657141225316348021070557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4419043267510261389521485 1657141225316348021070557)
                      ·
                        rfl

theorem cell23_3227271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3227271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227271 prefixEnd_3227271 := by exact prefixLift 3227271
  have htrace : WordTrace (prefixWord ++ tailWord_3227271) baseStart_3227271 baseEnd_3227271 := by
    simpa [prefixWord, tailWord_3227271, baseEnd_3227271] using wordTrace_append hprefix tailTrace_3227271
  have hstable : (prefixWord ++ tailWord_3227271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227271).length < 2 ^ (prefixWord ++ tailWord_3227271).sum := by decide
  have hdescent : baseEnd_3227271 < baseStart_3227271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227278 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3227278 : Nat := 118140960795 + 3227278 * 2 ^ 59
def prefixEnd_3227278 : Nat := 4983230072969 + 3 ^ 40 * 3227278 * 2
def baseEnd_3227278 : Nat := 552381606560309831227675

theorem tailTrace_3227278 : CollatzResearch.WordTrace tailWord_3227278 prefixEnd_3227278 552381606560309831227675 := by
  unfold tailWord_3227278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14713562350266307005776311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78472332534753637364140325 14713562350266307005776311)
  ·
    refine ⟨22070343525399460508664467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14713562350266307005776311 22070343525399460508664467)
    ·
      refine ⟨33105515288099190762996701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22070343525399460508664467 33105515288099190762996701)
      ·
        refine ⟨12414568233037196536123763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33105515288099190762996701 12414568233037196536123763)
        ·
          refine ⟨18621852349555794804185645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12414568233037196536123763 18621852349555794804185645)
          ·
            refine ⟨6983194631083423051569617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18621852349555794804185645 6983194631083423051569617)
            ·
              refine ⟨5237395973312567288677213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6983194631083423051569617 5237395973312567288677213)
              ·
                refine ⟨1964023489992212733253955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5237395973312567288677213 1964023489992212733253955)
                ·
                  refine ⟨2946035234988319099880933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964023489992212733253955 2946035234988319099880933)
                  ·
                    refine ⟨552381606560309831227675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946035234988319099880933 552381606560309831227675)
                    ·
                      rfl

theorem cell23_3227278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3227278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227278 prefixEnd_3227278 := by exact prefixLift 3227278
  have htrace : WordTrace (prefixWord ++ tailWord_3227278) baseStart_3227278 baseEnd_3227278 := by
    simpa [prefixWord, tailWord_3227278, baseEnd_3227278] using wordTrace_append hprefix tailTrace_3227278
  have hstable : (prefixWord ++ tailWord_3227278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227278).length < 2 ^ (prefixWord ++ tailWord_3227278).sum := by decide
  have hdescent : baseEnd_3227278 < baseStart_3227278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227294 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3227294 : Nat := 118140960795 + 3227294 * 2 ^ 59
def prefixEnd_3227294 : Nat := 4983230072969 + 3 ^ 40 * 3227294 * 2
def baseEnd_3227294 : Nat := 1657153035371401431082951

theorem tailTrace_3227294 : CollatzResearch.WordTrace tailWord_3227294 prefixEnd_3227294 1657153035371401431082951 := by
  unfold tailWord_3227294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14713635296259061347349117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78472721580048327185861957 14713635296259061347349117)
  ·
    refine ⟨5517613236097148005255919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14713635296259061347349117 5517613236097148005255919)
    ·
      refine ⟨8276419854145722007883879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517613236097148005255919 8276419854145722007883879)
      ·
        refine ⟨12414629781218583011825819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8276419854145722007883879 12414629781218583011825819)
        ·
          refine ⟨18621944671827874517738729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12414629781218583011825819 18621944671827874517738729)
          ·
            refine ⟨13966458503870905888304047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18621944671827874517738729 13966458503870905888304047)
            ·
              refine ⟨20949687755806358832456071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13966458503870905888304047 20949687755806358832456071)
              ·
                refine ⟨31424531633709538248684107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20949687755806358832456071 31424531633709538248684107)
                ·
                  refine ⟨47136797450564307373026161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31424531633709538248684107 47136797450564307373026161)
                  ·
                    refine ⟨35352598087923230529769621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47136797450564307373026161 35352598087923230529769621)
                    ·
                      refine ⟨1657153035371401431082951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35352598087923230529769621 1657153035371401431082951)
                      ·
                        rfl

theorem cell23_3227294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3227294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227294 prefixEnd_3227294 := by exact prefixLift 3227294
  have htrace : WordTrace (prefixWord ++ tailWord_3227294) baseStart_3227294 baseEnd_3227294 := by
    simpa [prefixWord, tailWord_3227294, baseEnd_3227294] using wordTrace_append hprefix tailTrace_3227294
  have hstable : (prefixWord ++ tailWord_3227294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227294).length < 2 ^ (prefixWord ++ tailWord_3227294).sum := by decide
  have hdescent : baseEnd_3227294 < baseStart_3227294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227327 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_3227327 : Nat := 118140960795 + 3227327 * 2 ^ 59
def prefixEnd_3227327 : Nat := 4983230072969 + 3 ^ 40 * 3227327 * 2
def baseEnd_3227327 : Nat := 1657169980232999801970299

theorem tailTrace_3227327 : CollatzResearch.WordTrace tailWord_3227327 prefixEnd_3227327 1657169980232999801970299 := by
  unfold tailWord_3227327
  simp only [CollatzResearch.WordTrace]
  refine ⟨117710285978952937414744235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78473523985968624943162823 117710285978952937414744235)
  ·
    refine ⟨176565428968429406122116353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117710285978952937414744235 176565428968429406122116353)
    ·
      refine ⟨132424071726322054591587265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176565428968429406122116353 132424071726322054591587265)
      ·
        refine ⟨99318053794741540943690449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132424071726322054591587265 99318053794741540943690449)
        ·
          refine ⟨74488540346056155707767837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99318053794741540943690449 74488540346056155707767837)
          ·
            refine ⟨27933202629771058390412939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74488540346056155707767837 27933202629771058390412939)
            ·
              refine ⟨41899803944656587585619409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27933202629771058390412939 41899803944656587585619409)
              ·
                refine ⟨31424852958492440689214557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41899803944656587585619409 31424852958492440689214557)
                ·
                  refine ⟨11784319859434665258455459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31424852958492440689214557 11784319859434665258455459)
                  ·
                    refine ⟨17676479789151997887683189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11784319859434665258455459 17676479789151997887683189)
                    ·
                      refine ⟨1657169980232999801970299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17676479789151997887683189 1657169980232999801970299)
                      ·
                        rfl

theorem cell23_3227327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_3227327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227327 prefixEnd_3227327 := by exact prefixLift 3227327
  have htrace : WordTrace (prefixWord ++ tailWord_3227327) baseStart_3227327 baseEnd_3227327 := by
    simpa [prefixWord, tailWord_3227327, baseEnd_3227327] using wordTrace_append hprefix tailTrace_3227327
  have hstable : (prefixWord ++ tailWord_3227327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227327).length < 2 ^ (prefixWord ++ tailWord_3227327).sum := by decide
  have hdescent : baseEnd_3227327 < baseStart_3227327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227368 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 2, 4]
def baseStart_3227368 : Nat := 118140960795 + 3227368 * 2 ^ 59
def prefixEnd_3227368 : Nat := 4983230072969 + 3 ^ 40 * 3227368 * 2
def baseEnd_3227368 : Nat := 552397010979944713852537

theorem tailTrace_3227368 : CollatzResearch.WordTrace tailWord_3227368 prefixEnd_3227368 552397010979944713852537 := by
  unfold tailWord_3227368
  simp only [CollatzResearch.WordTrace]
  refine ⟨58855890685902200708493379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78474520914536267611324505 58855890685902200708493379)
  ·
    refine ⟨88283836028853301062740069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58855890685902200708493379 88283836028853301062740069)
    ·
      refine ⟨16553219255409993949263763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88283836028853301062740069 16553219255409993949263763)
      ·
        refine ⟨24829828883114990923895645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16553219255409993949263763 24829828883114990923895645)
        ·
          refine ⟨9311185831168121596460867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24829828883114990923895645 9311185831168121596460867)
          ·
            refine ⟨13966778746752182394691301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9311185831168121596460867 13966778746752182394691301)
            ·
              refine ⟨2618771015016034199004619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13966778746752182394691301 2618771015016034199004619)
              ·
                refine ⟨3928156522524051298506929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618771015016034199004619 3928156522524051298506929)
                ·
                  refine ⟨2946117391893038473880197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3928156522524051298506929 2946117391893038473880197)
                  ·
                    refine ⟨552397010979944713852537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946117391893038473880197 552397010979944713852537)
                    ·
                      rfl

theorem cell23_3227368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_3227368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227368 prefixEnd_3227368 := by exact prefixLift 3227368
  have htrace : WordTrace (prefixWord ++ tailWord_3227368) baseStart_3227368 baseEnd_3227368 := by
    simpa [prefixWord, tailWord_3227368, baseEnd_3227368] using wordTrace_append hprefix tailTrace_3227368
  have hstable : (prefixWord ++ tailWord_3227368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227368).length < 2 ^ (prefixWord ++ tailWord_3227368).sum := by decide
  have hdescent : baseEnd_3227368 < baseStart_3227368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227387 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_3227387 : Nat := 118140960795 + 3227387 * 2 ^ 59
def prefixEnd_3227387 : Nat := 4983230072969 + 3 ^ 40 * 3227387 * 2
def baseEnd_3227387 : Nat := 1657200789072269567220023

theorem tailTrace_3227387 : CollatzResearch.WordTrace tailWord_3227387 prefixEnd_3227387 1657200789072269567220023 := by
  unfold tailWord_3227387
  simp only [CollatzResearch.WordTrace]
  refine ⟨117712474358735567661928415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78474982905823711774618943 117712474358735567661928415)
  ·
    refine ⟨176568711538103351492892623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117712474358735567661928415 176568711538103351492892623)
    ·
      refine ⟨264853067307155027239338935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176568711538103351492892623 264853067307155027239338935)
      ·
        refine ⟨397279600960732540859008403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264853067307155027239338935 397279600960732540859008403)
        ·
          refine ⟨595919401441098811288512605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397279600960732540859008403 595919401441098811288512605)
          ·
            refine ⟨223469775540412054233192227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595919401441098811288512605 223469775540412054233192227)
            ·
              refine ⟨335204663310618081349788341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223469775540412054233192227 335204663310618081349788341)
              ·
                refine ⟨31425437185370445126542657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 335204663310618081349788341 31425437185370445126542657)
                ·
                  refine ⟨23569077889027833844906993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31425437185370445126542657 23569077889027833844906993)
                  ·
                    refine ⟨17676808416770875383680245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23569077889027833844906993 17676808416770875383680245)
                    ·
                      refine ⟨1657200789072269567220023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17676808416770875383680245 1657200789072269567220023)
                      ·
                        rfl

theorem cell23_3227387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_3227387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227387 prefixEnd_3227387 := by exact prefixLift 3227387
  have htrace : WordTrace (prefixWord ++ tailWord_3227387) baseStart_3227387 baseEnd_3227387 := by
    simpa [prefixWord, tailWord_3227387, baseEnd_3227387] using wordTrace_append hprefix tailTrace_3227387
  have hstable : (prefixWord ++ tailWord_3227387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227387).length < 2 ^ (prefixWord ++ tailWord_3227387).sum := by decide
  have hdescent : baseEnd_3227387 < baseStart_3227387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227424 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_3227424 : Nat := 118140960795 + 3227424 * 2 ^ 59
def prefixEnd_3227424 : Nat := 4983230072969 + 3 ^ 40 * 3227424 * 2
def baseEnd_3227424 : Nat := 552406595952161974152451

theorem tailTrace_3227424 : CollatzResearch.WordTrace tailWord_3227424 prefixEnd_3227424 552406595952161974152451 := by
  unfold tailWord_3227424
  simp only [CollatzResearch.WordTrace]
  refine ⟨58856911929800761490512663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78475882573067681987350217 58856911929800761490512663)
  ·
    refine ⟨88285367894701142235768995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58856911929800761490512663 88285367894701142235768995)
    ·
      refine ⟨132428051842051713353653493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88285367894701142235768995 132428051842051713353653493)
      ·
        refine ⟨12415129860192348126905015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132428051842051713353653493 12415129860192348126905015)
        ·
          refine ⟨18622694790288522190357523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12415129860192348126905015 18622694790288522190357523)
          ·
            refine ⟨27934042185432783285536285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18622694790288522190357523 27934042185432783285536285)
            ·
              refine ⟨10475265819537293732076107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27934042185432783285536285 10475265819537293732076107)
              ·
                refine ⟨15712898729305940598114161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10475265819537293732076107 15712898729305940598114161)
                ·
                  refine ⟨11784674046979455448585621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15712898729305940598114161 11784674046979455448585621)
                  ·
                    refine ⟨552406595952161974152451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11784674046979455448585621 552406595952161974152451)
                    ·
                      rfl

theorem cell23_3227424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_3227424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227424 prefixEnd_3227424 := by exact prefixLift 3227424
  have htrace : WordTrace (prefixWord ++ tailWord_3227424) baseStart_3227424 baseEnd_3227424 := by
    simpa [prefixWord, tailWord_3227424, baseEnd_3227424] using wordTrace_append hprefix tailTrace_3227424
  have hstable : (prefixWord ++ tailWord_3227424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227424).length < 2 ^ (prefixWord ++ tailWord_3227424).sum := by decide
  have hdescent : baseEnd_3227424 < baseStart_3227424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227518 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3227518 : Nat := 118140960795 + 3227518 * 2 ^ 59
def prefixEnd_3227518 : Nat := 4983230072969 + 3 ^ 40 * 3227518 * 2
def baseEnd_3227518 : Nat := 552422685012669518227307

theorem tailTrace_3227518 : CollatzResearch.WordTrace tailWord_3227518 prefixEnd_3227518 552422685012669518227307 := by
  unfold tailWord_3227518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14714656540157622129368401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78478168214173984689964805 14714656540157622129368401)
  ·
    refine ⟨11035992405118216597026301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14714656540157622129368401 11035992405118216597026301)
    ·
      refine ⟨4138497151919331223884863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11035992405118216597026301 4138497151919331223884863)
      ·
        refine ⟨6207745727878996835827295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4138497151919331223884863 6207745727878996835827295)
        ·
          refine ⟨9311618591818495253740943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6207745727878996835827295 9311618591818495253740943)
          ·
            refine ⟨13967427887727742880611415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9311618591818495253740943 13967427887727742880611415)
            ·
              refine ⟨20951141831591614320917123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967427887727742880611415 20951141831591614320917123)
              ·
                refine ⟨31426712747387421481375685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20951141831591614320917123 31426712747387421481375685)
                ·
                  refine ⟨5892508640135141527757941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31426712747387421481375685 5892508640135141527757941)
                  ·
                    refine ⟨552422685012669518227307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5892508640135141527757941 552422685012669518227307)
                    ·
                      rfl

theorem cell23_3227518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3227518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227518 prefixEnd_3227518 := by exact prefixLift 3227518
  have htrace : WordTrace (prefixWord ++ tailWord_3227518) baseStart_3227518 baseEnd_3227518 := by
    simpa [prefixWord, tailWord_3227518, baseEnd_3227518] using wordTrace_append hprefix tailTrace_3227518
  have hstable : (prefixWord ++ tailWord_3227518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227518).length < 2 ^ (prefixWord ++ tailWord_3227518).sum := by decide
  have hdescent : baseEnd_3227518 < baseStart_3227518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227541 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_3227541 : Nat := 118140960795 + 3227541 * 2 ^ 59
def prefixEnd_3227541 : Nat := 4983230072969 + 3 ^ 40 * 3227541 * 2
def baseEnd_3227541 : Nat := 1657279865093061964694315

theorem tailTrace_3227541 : CollatzResearch.WordTrace tailWord_3227541 prefixEnd_3227541 1657279865093061964694315 := by
  unfold tailWord_3227541
  simp only [CollatzResearch.WordTrace]
  refine ⟨117718091200177651963034477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78478727466785101308689651 117718091200177651963034477)
  ·
    refine ⟨44144284200066619486137929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117718091200177651963034477 44144284200066619486137929)
    ·
      refine ⟨33108213150049964614603447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44144284200066619486137929 33108213150049964614603447)
      ·
        refine ⟨49662319725074946921905171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33108213150049964614603447 49662319725074946921905171)
        ·
          refine ⟨74493479587612420382857757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49662319725074946921905171 74493479587612420382857757)
          ·
            refine ⟨27935054845354657643571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74493479587612420382857757 27935054845354657643571659)
            ·
              refine ⟨41902582268031986465357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27935054845354657643571659 41902582268031986465357489)
              ·
                refine ⟨31426936701023989849018117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41902582268031986465357489 31426936701023989849018117)
                ·
                  refine ⟨5892550631441998096690897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31426936701023989849018117 5892550631441998096690897)
                  ·
                    refine ⟨4419412973581498572518173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5892550631441998096690897 4419412973581498572518173)
                    ·
                      refine ⟨1657279865093061964694315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4419412973581498572518173 1657279865093061964694315)
                      ·
                        rfl

theorem cell23_3227541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_3227541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227541 prefixEnd_3227541 := by exact prefixLift 3227541
  have htrace : WordTrace (prefixWord ++ tailWord_3227541) baseStart_3227541 baseEnd_3227541 := by
    simpa [prefixWord, tailWord_3227541, baseEnd_3227541] using wordTrace_append hprefix tailTrace_3227541
  have hstable : (prefixWord ++ tailWord_3227541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227541).length < 2 ^ (prefixWord ++ tailWord_3227541).sum := by decide
  have hdescent : baseEnd_3227541 < baseStart_3227541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227582 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_3227582 : Nat := 118140960795 + 3227582 * 2 ^ 59
def prefixEnd_3227582 : Nat := 4983230072969 + 3 ^ 40 * 3227582 * 2
def baseEnd_3227582 : Nat := 552433639266632101427209

theorem tailTrace_3227582 : CollatzResearch.WordTrace tailWord_3227582 prefixEnd_3227582 552433639266632101427209 := by
  unfold tailWord_3227582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14714948324128639495659625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78479724395352743976851333 14714948324128639495659625)
  ·
    refine ⟨11036211243096479621744719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14714948324128639495659625 11036211243096479621744719)
    ·
      refine ⟨16554316864644719432617079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11036211243096479621744719 16554316864644719432617079)
      ·
        refine ⟨24831475296967079148925619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16554316864644719432617079 24831475296967079148925619)
        ·
          refine ⟨37247212945450618723388429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24831475296967079148925619 37247212945450618723388429)
          ·
            refine ⟨13967704854543982021270661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37247212945450618723388429 13967704854543982021270661)
            ·
              refine ⟨2618944660226996628988249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13967704854543982021270661 2618944660226996628988249)
              ·
                refine ⟨1964208495170247471741187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618944660226996628988249 1964208495170247471741187)
                ·
                  refine ⟨2946312742755371207611781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964208495170247471741187 2946312742755371207611781)
                  ·
                    refine ⟨552433639266632101427209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946312742755371207611781 552433639266632101427209)
                    ·
                      rfl

theorem cell23_3227582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_3227582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227582 prefixEnd_3227582 := by exact prefixLift 3227582
  have htrace : WordTrace (prefixWord ++ tailWord_3227582) baseStart_3227582 baseEnd_3227582 := by
    simpa [prefixWord, tailWord_3227582, baseEnd_3227582] using wordTrace_append hprefix tailTrace_3227582
  have hstable : (prefixWord ++ tailWord_3227582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227582).length < 2 ^ (prefixWord ++ tailWord_3227582).sum := by decide
  have hdescent : baseEnd_3227582 < baseStart_3227582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227598 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_3227598 : Nat := 118140960795 + 3227598 * 2 ^ 59
def prefixEnd_3227598 : Nat := 4983230072969 + 3 ^ 40 * 3227598 * 2
def baseEnd_3227598 : Nat := 1657309133490368241681553

theorem tailTrace_3227598 : CollatzResearch.WordTrace tailWord_3227598 prefixEnd_3227598 1657309133490368241681553 := by
  unfold tailWord_3227598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715021270121393837232431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78480113440647433798572965 14715021270121393837232431)
  ·
    refine ⟨22072531905182090755848647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14715021270121393837232431 22072531905182090755848647)
    ·
      refine ⟨33108797857773136133772971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22072531905182090755848647 33108797857773136133772971)
      ·
        refine ⟨49663196786659704200659457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33108797857773136133772971 49663196786659704200659457)
        ·
          refine ⟨37247397589994778150494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49663196786659704200659457 37247397589994778150494593)
          ·
            refine ⟨27935548192496083612870945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37247397589994778150494593 27935548192496083612870945)
            ·
              refine ⟨20951661144372062709653209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27935548192496083612870945 20951661144372062709653209)
              ·
                refine ⟨15713745858279047032239907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20951661144372062709653209 15713745858279047032239907)
                ·
                  refine ⟨23570618787418570548359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15713745858279047032239907 23570618787418570548359861)
                  ·
                    refine ⟨2209745511320490988908737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23570618787418570548359861 2209745511320490988908737)
                    ·
                      refine ⟨1657309133490368241681553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2209745511320490988908737 1657309133490368241681553)
                      ·
                        rfl

theorem cell23_3227598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_3227598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227598 prefixEnd_3227598 := by exact prefixLift 3227598
  have htrace : WordTrace (prefixWord ++ tailWord_3227598) baseStart_3227598 baseEnd_3227598 := by
    simpa [prefixWord, tailWord_3227598, baseEnd_3227598] using wordTrace_append hprefix tailTrace_3227598
  have hstable : (prefixWord ++ tailWord_3227598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227598).length < 2 ^ (prefixWord ++ tailWord_3227598).sum := by decide
  have hdescent : baseEnd_3227598 < baseStart_3227598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227605 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3227605 : Nat := 118140960795 + 3227605 * 2 ^ 59
def prefixEnd_3227605 : Nat := 4983230072969 + 3 ^ 40 * 3227605 * 2
def baseEnd_3227605 : Nat := 1657312727854949714294021

theorem tailTrace_3227605 : CollatzResearch.WordTrace tailWord_3227605 prefixEnd_3227605 1657312727854949714294021 := by
  unfold tailWord_3227605
  simp only [CollatzResearch.WordTrace]
  refine ⟨117720425471945790893364269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78480283647963860595576179 117720425471945790893364269)
  ·
    refine ⟨44145159551979671585011601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117720425471945790893364269 44145159551979671585011601)
    ·
      refine ⟨33108869663984753688758701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44145159551979671585011601 33108869663984753688758701)
      ·
        refine ⟨12415826123994282633284513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33108869663984753688758701 12415826123994282633284513)
        ·
          refine ⟨9311869592995711974963385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12415826123994282633284513 9311869592995711974963385)
          ·
            refine ⟨6983902194746783981222539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9311869592995711974963385 6983902194746783981222539)
            ·
              refine ⟨10475853292120175971833809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6983902194746783981222539 10475853292120175971833809)
              ·
                refine ⟨7856889969090131978875357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10475853292120175971833809 7856889969090131978875357)
                ·
                  refine ⟨2946333738408799492078259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7856889969090131978875357 2946333738408799492078259)
                  ·
                    refine ⟨4419500607613199238117389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946333738408799492078259 4419500607613199238117389)
                    ·
                      refine ⟨1657312727854949714294021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4419500607613199238117389 1657312727854949714294021)
                      ·
                        rfl

theorem cell23_3227605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3227605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227605 prefixEnd_3227605 := by exact prefixLift 3227605
  have htrace : WordTrace (prefixWord ++ tailWord_3227605) baseStart_3227605 baseEnd_3227605 := by
    simpa [prefixWord, tailWord_3227605, baseEnd_3227605] using wordTrace_append hprefix tailTrace_3227605
  have hstable : (prefixWord ++ tailWord_3227605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227605).length < 2 ^ (prefixWord ++ tailWord_3227605).sum := by decide
  have hdescent : baseEnd_3227605 < baseStart_3227605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227615 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 2, 3, 2]
def baseStart_3227615 : Nat := 118140960795 + 3227615 * 2 ^ 59
def prefixEnd_3227615 : Nat := 4983230072969 + 3 ^ 40 * 3227615 * 2
def baseEnd_3227615 : Nat := 1657317862661494675168975

theorem tailTrace_3227615 : CollatzResearch.WordTrace tailWord_3227615 prefixEnd_3227615 1657317862661494675168975 := by
  unfold tailWord_3227615
  simp only [CollatzResearch.WordTrace]
  refine ⟨117720790201909562601228299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78480526801273041734152199 117720790201909562601228299)
  ·
    refine ⟨176581185302864343901842449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117720790201909562601228299 176581185302864343901842449)
    ·
      refine ⟨132435888977148257926381837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176581185302864343901842449 132435888977148257926381837)
      ·
        refine ⟨49663458366430596722393189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132435888977148257926381837 49663458366430596722393189)
        ·
          refine ⟨9311898443705736885448723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49663458366430596722393189 9311898443705736885448723)
          ·
            refine ⟨13967847665558605328173085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9311898443705736885448723 13967847665558605328173085)
            ·
              refine ⟨5237942874584476998064907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13967847665558605328173085 5237942874584476998064907)
              ·
                refine ⟨7856914311876715497097361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237942874584476998064907 7856914311876715497097361)
                ·
                  refine ⟨5892685733907536622823021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7856914311876715497097361 5892685733907536622823021)
                  ·
                    refine ⟨2209757150215326233558633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5892685733907536622823021 2209757150215326233558633)
                    ·
                      refine ⟨1657317862661494675168975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2209757150215326233558633 1657317862661494675168975)
                      ·
                        rfl

theorem cell23_3227615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_3227615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227615 prefixEnd_3227615 := by exact prefixLift 3227615
  have htrace : WordTrace (prefixWord ++ tailWord_3227615) baseStart_3227615 baseEnd_3227615 := by
    simpa [prefixWord, tailWord_3227615, baseEnd_3227615] using wordTrace_append hprefix tailTrace_3227615
  have hstable : (prefixWord ++ tailWord_3227615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227615).length < 2 ^ (prefixWord ++ tailWord_3227615).sum := by decide
  have hdescent : baseEnd_3227615 < baseStart_3227615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227631 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_3227631 : Nat := 118140960795 + 3227631 * 2 ^ 59
def prefixEnd_3227631 : Nat := 4983230072969 + 3 ^ 40 * 3227631 * 2
def baseEnd_3227631 : Nat := 1657326078351966612568901

theorem tailTrace_3227631 : CollatzResearch.WordTrace tailWord_3227631 prefixEnd_3227631 1657326078351966612568901 := by
  unfold tailWord_3227631
  simp only [CollatzResearch.WordTrace]
  refine ⟨117721373769851597333810747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78480915846567731555873831 117721373769851597333810747)
  ·
    refine ⟨176582060654777396000716121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117721373769851597333810747 176582060654777396000716121)
    ·
      refine ⟨132436545491083047000537091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176582060654777396000716121 132436545491083047000537091)
      ·
        refine ⟨198654818236624570500805637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132436545491083047000537091 198654818236624570500805637)
        ·
          refine ⟨37247778419367106968901057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198654818236624570500805637 37247778419367106968901057)
          ·
            refine ⟨27935833814525330226675793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37247778419367106968901057 27935833814525330226675793)
            ·
              refine ⟨20951875360893997670006845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27935833814525330226675793 20951875360893997670006845)
              ·
                refine ⟨7856953260335249126252567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20951875360893997670006845 7856953260335249126252567)
                ·
                  refine ⟨11785429890502873689378851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856953260335249126252567 11785429890502873689378851)
                  ·
                    refine ⟨17678144835754310534068277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11785429890502873689378851 17678144835754310534068277)
                    ·
                      refine ⟨1657326078351966612568901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17678144835754310534068277 1657326078351966612568901)
                      ·
                        rfl

theorem cell23_3227631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_3227631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227631 prefixEnd_3227631 := by exact prefixLift 3227631
  have htrace : WordTrace (prefixWord ++ tailWord_3227631) baseStart_3227631 baseEnd_3227631 := by
    simpa [prefixWord, tailWord_3227631, baseEnd_3227631] using wordTrace_append hprefix tailTrace_3227631
  have hstable : (prefixWord ++ tailWord_3227631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227631).length < 2 ^ (prefixWord ++ tailWord_3227631).sum := by decide
  have hdescent : baseEnd_3227631 < baseStart_3227631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227645 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_3227645 : Nat := 118140960795 + 3227645 * 2 ^ 59
def prefixEnd_3227645 : Nat := 4983230072969 + 3 ^ 40 * 3227645 * 2
def baseEnd_3227645 : Nat := 1657333267081129557793837

theorem tailTrace_3227645 : CollatzResearch.WordTrace tailWord_3227645 prefixEnd_3227645 1657333267081129557793837 := by
  unfold tailWord_3227645
  simp only [CollatzResearch.WordTrace]
  refine ⟨117721884391800877724820389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78481256261200585149880259 117721884391800877724820389)
  ·
    refine ⟨22072853323462664573403823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117721884391800877724820389 22072853323462664573403823)
    ·
      refine ⟨33109279985193996860105735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22072853323462664573403823 33109279985193996860105735)
      ·
        refine ⟨49663919977790995290158603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33109279985193996860105735 49663919977790995290158603)
        ·
          refine ⟨74495879966686492935237905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49663919977790995290158603 74495879966686492935237905)
          ·
            refine ⟨55871909975014869701428429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74495879966686492935237905 55871909975014869701428429)
            ·
              refine ⟨20951966240630576138035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55871909975014869701428429 20951966240630576138035661)
              ·
                refine ⟨7856987340236466051763373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20951966240630576138035661 7856987340236466051763373)
                ·
                  refine ⟨2946370252588674769411265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7856987340236466051763373 2946370252588674769411265)
                  ·
                    refine ⟨2209777689441506077058449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2946370252588674769411265 2209777689441506077058449)
                    ·
                      refine ⟨1657333267081129557793837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2209777689441506077058449 1657333267081129557793837)
                      ·
                        rfl

theorem cell23_3227645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_3227645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227645 prefixEnd_3227645 := by exact prefixLift 3227645
  have htrace : WordTrace (prefixWord ++ tailWord_3227645) baseStart_3227645 baseEnd_3227645 := by
    simpa [prefixWord, tailWord_3227645, baseEnd_3227645] using wordTrace_append hprefix tailTrace_3227645
  have hstable : (prefixWord ++ tailWord_3227645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227645).length < 2 ^ (prefixWord ++ tailWord_3227645).sum := by decide
  have hdescent : baseEnd_3227645 < baseStart_3227645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227658 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3227658 : Nat := 118140960795 + 3227658 * 2 ^ 59
def prefixEnd_3227658 : Nat := 4983230072969 + 3 ^ 40 * 3227658 * 2
def baseEnd_3227658 : Nat := 1657339942329638006931277

theorem tailTrace_3227658 : CollatzResearch.WordTrace tailWord_3227658 prefixEnd_3227658 1657339942329638006931277 := by
  unfold tailWord_3227658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430589635188445236260907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78481572360502520630029085 29430589635188445236260907)
  ·
    refine ⟨44145884452782667854391361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29430589635188445236260907 44145884452782667854391361)
    ·
      refine ⟨33109413339587000890793521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44145884452782667854391361 33109413339587000890793521)
      ·
        refine ⟨24832060004690250668095141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33109413339587000890793521 24832060004690250668095141)
        ·
          refine ⟨4656011250879422000267839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24832060004690250668095141 4656011250879422000267839)
          ·
            refine ⟨6984016876319133000401759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656011250879422000267839 6984016876319133000401759)
            ·
              refine ⟨10476025314478699500602639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984016876319133000401759 10476025314478699500602639)
              ·
                refine ⟨15714037971718049250903959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10476025314478699500602639 15714037971718049250903959)
                ·
                  refine ⟨23571056957577073876355939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15714037971718049250903959 23571056957577073876355939)
                  ·
                    refine ⟨35356585436365610814533909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23571056957577073876355939 35356585436365610814533909)
                    ·
                      refine ⟨1657339942329638006931277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35356585436365610814533909 1657339942329638006931277)
                      ·
                        rfl

theorem cell23_3227658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3227658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227658 prefixEnd_3227658 := by exact prefixLift 3227658
  have htrace : WordTrace (prefixWord ++ tailWord_3227658) baseStart_3227658 baseEnd_3227658 := by
    simpa [prefixWord, tailWord_3227658, baseEnd_3227658] using wordTrace_append hprefix tailTrace_3227658
  have hstable : (prefixWord ++ tailWord_3227658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227658).length < 2 ^ (prefixWord ++ tailWord_3227658).sum := by decide
  have hdescent : baseEnd_3227658 < baseStart_3227658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227711 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 2, 6]
def baseStart_3227711 : Nat := 118140960795 + 3227711 * 2 ^ 59
def prefixEnd_3227711 : Nat := 4983230072969 + 3 ^ 40 * 3227711 * 2
def baseEnd_3227711 : Nat := 552455718934775433189511

theorem tailTrace_3227711 : CollatzResearch.WordTrace tailWord_3227711 prefixEnd_3227711 552455718934775433189511 := by
  unfold tailWord_3227711
  simp only [CollatzResearch.WordTrace]
  refine ⟨117724291609561770996722987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78482861073041180664481991 117724291609561770996722987)
  ·
    refine ⟨176586437414342656495084481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117724291609561770996722987 176586437414342656495084481)
    ·
      refine ⟨132439828060756992371313361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176586437414342656495084481 132439828060756992371313361)
      ·
        refine ⟨99329871045567744278485021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132439828060756992371313361 99329871045567744278485021)
        ·
          refine ⟨37248701642087904104431883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99329871045567744278485021 37248701642087904104431883)
          ·
            refine ⟨55873052463131856156647825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37248701642087904104431883 55873052463131856156647825)
            ·
              refine ⟨41904789347348892117485869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55873052463131856156647825 41904789347348892117485869)
              ·
                refine ⟨15714296005255834544057201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41904789347348892117485869 15714296005255834544057201)
                ·
                  refine ⟨11785722003941875908042901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15714296005255834544057201 11785722003941875908042901)
                  ·
                    refine ⟨552455718934775433189511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11785722003941875908042901 552455718934775433189511)
                    ·
                      rfl

theorem cell23_3227711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_3227711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227711 prefixEnd_3227711 := by exact prefixLift 3227711
  have htrace : WordTrace (prefixWord ++ tailWord_3227711) baseStart_3227711 baseEnd_3227711 := by
    simpa [prefixWord, tailWord_3227711, baseEnd_3227711] using wordTrace_append hprefix tailTrace_3227711
  have hstable : (prefixWord ++ tailWord_3227711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227711).length < 2 ^ (prefixWord ++ tailWord_3227711).sum := by decide
  have hdescent : baseEnd_3227711 < baseStart_3227711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227712 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3]
def baseStart_3227712 : Nat := 118140960795 + 3227712 * 2 ^ 59
def prefixEnd_3227712 : Nat := 4983230072969 + 3 ^ 40 * 3227712 * 2
def baseEnd_3227712 : Nat := 1657367670284980795656029

theorem tailTrace_3227712 : CollatzResearch.WordTrace tailWord_3227712 prefixEnd_3227712 1657367670284980795656029 := by
  unfold tailWord_3227712
  simp only [CollatzResearch.WordTrace]
  refine ⟨58862164041279074083754695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78482885388372098778339593 58862164041279074083754695)
  ·
    refine ⟨88293246061918611125632043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58862164041279074083754695 88293246061918611125632043)
    ·
      refine ⟨132439869092877916688448065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88293246061918611125632043 132439869092877916688448065)
      ·
        refine ⟨99329901819658437516336049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132439869092877916688448065 99329901819658437516336049)
        ·
          refine ⟨74497426364743828137252037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99329901819658437516336049 74497426364743828137252037)
          ·
            refine ⟨13968267443389467775734757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74497426364743828137252037 13968267443389467775734757)
            ·
              refine ⟨2619050145635525207950267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13968267443389467775734757 2619050145635525207950267)
              ·
                refine ⟨3928575218453287811925401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619050145635525207950267 3928575218453287811925401)
                ·
                  refine ⟨2946431413839965858944051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3928575218453287811925401 2946431413839965858944051)
                  ·
                    refine ⟨4419647120759948788416077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946431413839965858944051 4419647120759948788416077)
                    ·
                      refine ⟨1657367670284980795656029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4419647120759948788416077 1657367670284980795656029)
                      ·
                        rfl

theorem cell23_3227712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_3227712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227712 prefixEnd_3227712 := by exact prefixLift 3227712
  have htrace : WordTrace (prefixWord ++ tailWord_3227712) baseStart_3227712 baseEnd_3227712 := by
    simpa [prefixWord, tailWord_3227712, baseEnd_3227712] using wordTrace_append hprefix tailTrace_3227712
  have hstable : (prefixWord ++ tailWord_3227712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227712).length < 2 ^ (prefixWord ++ tailWord_3227712).sum := by decide
  have hdescent : baseEnd_3227712 < baseStart_3227712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227721 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_3227721 : Nat := 118140960795 + 3227721 * 2 ^ 59
def prefixEnd_3227721 : Nat := 4983230072969 + 3 ^ 40 * 3227721 * 2
def baseEnd_3227721 : Nat := 1657372291610871260443487

theorem tailTrace_3227721 : CollatzResearch.WordTrace tailWord_3227721 prefixEnd_3227721 1657372291610871260443487 := by
  unfold tailWord_3227721
  simp only [CollatzResearch.WordTrace]
  refine ⟨117724656339525542704587017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78483104226350361803058011 117724656339525542704587017)
  ·
    refine ⟨88293492254644157028440263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117724656339525542704587017 88293492254644157028440263)
    ·
      refine ⟨132440238381966235542660395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88293492254644157028440263 132440238381966235542660395)
      ·
        refine ⟨198660357572949353313990593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132440238381966235542660395 198660357572949353313990593)
        ·
          refine ⟨148995268179712014985492945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198660357572949353313990593 148995268179712014985492945)
          ·
            refine ⟨111746451134784011239119709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148995268179712014985492945 111746451134784011239119709)
            ·
              refine ⟨41904919175544004214669891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111746451134784011239119709 41904919175544004214669891)
              ·
                refine ⟨62857378763316006322004837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41904919175544004214669891 62857378763316006322004837)
                ·
                  refine ⟨11785758518121751185375907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62857378763316006322004837 11785758518121751185375907)
                  ·
                    refine ⟨17678637777182626778063861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11785758518121751185375907 17678637777182626778063861)
                    ·
                      refine ⟨1657372291610871260443487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17678637777182626778063861 1657372291610871260443487)
                      ·
                        rfl

theorem cell23_3227721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_3227721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227721 prefixEnd_3227721 := by exact prefixLift 3227721
  have htrace : WordTrace (prefixWord ++ tailWord_3227721) baseStart_3227721 baseEnd_3227721 := by
    simpa [prefixWord, tailWord_3227721, baseEnd_3227721] using wordTrace_append hprefix tailTrace_3227721
  have hstable : (prefixWord ++ tailWord_3227721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227721).length < 2 ^ (prefixWord ++ tailWord_3227721).sum := by decide
  have hdescent : baseEnd_3227721 < baseStart_3227721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227735 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_3227735 : Nat := 118140960795 + 3227735 * 2 ^ 59
def prefixEnd_3227735 : Nat := 4983230072969 + 3 ^ 40 * 3227735 * 2
def baseEnd_3227735 : Nat := 1657379480340034205668423

theorem tailTrace_3227735 : CollatzResearch.WordTrace tailWord_3227735 prefixEnd_3227735 1657379480340034205668423 := by
  unfold tailWord_3227735
  simp only [CollatzResearch.WordTrace]
  refine ⟨117725166961474823095596659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78483444640983215397064439 117725166961474823095596659)
  ·
    refine ⟨176587750442212234643394989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117725166961474823095596659 176587750442212234643394989)
    ·
      refine ⟨66220406415829587991273121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176587750442212234643394989 66220406415829587991273121)
      ·
        refine ⟨49665304811872190993454841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66220406415829587991273121 49665304811872190993454841)
        ·
          refine ⟨37248978608904143245091131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49665304811872190993454841 37248978608904143245091131)
          ·
            refine ⟨55873467913356214867636697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37248978608904143245091131 55873467913356214867636697)
            ·
              refine ⟨41905100935017161150727523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55873467913356214867636697 41905100935017161150727523)
              ·
                refine ⟨62857651402525741726091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41905100935017161150727523 62857651402525741726091285)
                ·
                  refine ⟨2946452409493394143410529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62857651402525741726091285 2946452409493394143410529)
                  ·
                    refine ⟨2209839307120045607557897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2946452409493394143410529 2209839307120045607557897)
                    ·
                      refine ⟨1657379480340034205668423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2209839307120045607557897 1657379480340034205668423)
                      ·
                        rfl

theorem cell23_3227735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_3227735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227735 prefixEnd_3227735 := by exact prefixLift 3227735
  have htrace : WordTrace (prefixWord ++ tailWord_3227735) baseStart_3227735 baseEnd_3227735 := by
    simpa [prefixWord, tailWord_3227735, baseEnd_3227735] using wordTrace_append hprefix tailTrace_3227735
  have hstable : (prefixWord ++ tailWord_3227735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227735).length < 2 ^ (prefixWord ++ tailWord_3227735).sum := by decide
  have hdescent : baseEnd_3227735 < baseStart_3227735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227758 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_3227758 : Nat := 118140960795 + 3227758 * 2 ^ 59
def prefixEnd_3227758 : Nat := 4983230072969 + 3 ^ 40 * 3227758 * 2
def baseEnd_3227758 : Nat := 184154587821676401742313

theorem tailTrace_3227758 : CollatzResearch.WordTrace tailWord_3227758 prefixEnd_3227758 184154587821676401742313 := by
  unfold tailWord_3227758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715750730048937252960491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78484003893594332015789285 14715750730048937252960491)
  ·
    refine ⟨22073626095073405879440737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14715750730048937252960491 22073626095073405879440737)
    ·
      refine ⟨16555219571305054409580553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22073626095073405879440737 16555219571305054409580553)
      ·
        refine ⟨12416414678478790807185415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16555219571305054409580553 12416414678478790807185415)
        ·
          refine ⟨18624622017718186210778123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12416414678478790807185415 18624622017718186210778123)
          ·
            refine ⟨27936933026577279316167185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18624622017718186210778123 27936933026577279316167185)
            ·
              refine ⟨20952699769932959487125389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27936933026577279316167185 20952699769932959487125389)
              ·
                refine ⟨7857262413724859807672021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20952699769932959487125389 7857262413724859807672021)
                ·
                  refine ⟨184154587821676401742313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7857262413724859807672021 184154587821676401742313)
                  ·
                    rfl

theorem cell23_3227758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_3227758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227758 prefixEnd_3227758 := by exact prefixLift 3227758
  have htrace : WordTrace (prefixWord ++ tailWord_3227758) baseStart_3227758 baseEnd_3227758 := by
    simpa [prefixWord, tailWord_3227758, baseEnd_3227758] using wordTrace_append hprefix tailTrace_3227758
  have hstable : (prefixWord ++ tailWord_3227758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227758).length < 2 ^ (prefixWord ++ tailWord_3227758).sum := by decide
  have hdescent : baseEnd_3227758 < baseStart_3227758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227801 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 10]
def baseStart_3227801 : Nat := 118140960795 + 3227801 * 2 ^ 59
def prefixEnd_3227801 : Nat := 4983230072969 + 3 ^ 40 * 3227801 * 2
def baseEnd_3227801 : Nat := 552471123354410315814373

theorem tailTrace_3227801 : CollatzResearch.WordTrace tailWord_3227801 prefixEnd_3227801 552471123354410315814373 := by
  unfold tailWord_3227801
  simp only [CollatzResearch.WordTrace]
  refine ⟨117727574179235716367499257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78485049452823810911666171 117727574179235716367499257)
  ·
    refine ⟨88295680634426787275624443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117727574179235716367499257 88295680634426787275624443)
    ·
      refine ⟨132443520951640180913436665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88295680634426787275624443 132443520951640180913436665)
      ·
        refine ⟨99332640713730135685077499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132443520951640180913436665 99332640713730135685077499)
        ·
          refine ⟨148998961070595203527616249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99332640713730135685077499 148998961070595203527616249)
          ·
            refine ⟨111749220802946402645712187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148998961070595203527616249 111749220802946402645712187)
            ·
              refine ⟨167623831204419603968568281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111749220802946402645712187 167623831204419603968568281)
              ·
                refine ⟨125717873403314702976426211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167623831204419603968568281 125717873403314702976426211)
                ·
                  refine ⟨188576810104972054464639317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125717873403314702976426211 188576810104972054464639317)
                  ·
                    refine ⟨552471123354410315814373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 188576810104972054464639317 552471123354410315814373)
                    ·
                      rfl

theorem cell23_3227801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_3227801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227801 prefixEnd_3227801 := by exact prefixLift 3227801
  have htrace : WordTrace (prefixWord ++ tailWord_3227801) baseStart_3227801 baseEnd_3227801 := by
    simpa [prefixWord, tailWord_3227801, baseEnd_3227801] using wordTrace_append hprefix tailTrace_3227801
  have hstable : (prefixWord ++ tailWord_3227801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227801).length < 2 ^ (prefixWord ++ tailWord_3227801).sum := by decide
  have hdescent : baseEnd_3227801 < baseStart_3227801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227869 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_3227869 : Nat := 118140960795 + 3227869 * 2 ^ 59
def prefixEnd_3227869 : Nat := 4983230072969 + 3 ^ 40 * 3227869 * 2
def baseEnd_3227869 : Nat := 552482762249245560464269

theorem tailTrace_3227869 : CollatzResearch.WordTrace tailWord_3227869 prefixEnd_3227869 552482762249245560464269 := by
  unfold tailWord_3227869
  simp only [CollatzResearch.WordTrace]
  refine ⟨117730054342989363980974661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78486702895326242653983107 117730054342989363980974661)
  ·
    refine ⟨22074385189310505746432749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117730054342989363980974661 22074385189310505746432749)
    ·
      refine ⟨8277894445991439654912281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22074385189310505746432749 8277894445991439654912281)
      ·
        refine ⟨6208420834493579741184211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8277894445991439654912281 6208420834493579741184211)
        ·
          refine ⟨9312631251740369611776317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6208420834493579741184211 9312631251740369611776317)
          ·
            refine ⟨3492236719402638604416119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9312631251740369611776317 3492236719402638604416119)
            ·
              refine ⟨5238355079103957906624179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492236719402638604416119 5238355079103957906624179)
              ·
                refine ⟨7857532618655936859936269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5238355079103957906624179 7857532618655936859936269)
                ·
                  refine ⟨2946574731995976322476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7857532618655936859936269 2946574731995976322476101)
                  ·
                    refine ⟨552482762249245560464269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946574731995976322476101 552482762249245560464269)
                    ·
                      rfl

theorem cell23_3227869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_3227869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227869 prefixEnd_3227869 := by exact prefixLift 3227869
  have htrace : WordTrace (prefixWord ++ tailWord_3227869) baseStart_3227869 baseEnd_3227869 := by
    simpa [prefixWord, tailWord_3227869, baseEnd_3227869] using wordTrace_append hprefix tailTrace_3227869
  have hstable : (prefixWord ++ tailWord_3227869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227869).length < 2 ^ (prefixWord ++ tailWord_3227869).sum := by decide
  have hdescent : baseEnd_3227869 < baseStart_3227869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227925 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_3227925 : Nat := 118140960795 + 3227925 * 2 ^ 59
def prefixEnd_3227925 : Nat := 4983230072969 + 3 ^ 40 * 3227925 * 2
def baseEnd_3227925 : Nat := 552492347221462820764183

theorem tailTrace_3227925 : CollatzResearch.WordTrace tailWord_3227925 prefixEnd_3227925 552492347221462820764183 := by
  unfold tailWord_3227925
  simp only [CollatzResearch.WordTrace]
  refine ⟨117732096830786485545013229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78488064553857657030008819 117732096830786485545013229)
  ·
    refine ⟨44149536311544932079379961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117732096830786485545013229 44149536311544932079379961)
    ·
      refine ⟨33112152233658699059534971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44149536311544932079379961 33112152233658699059534971)
      ·
        refine ⟨49668228350488048589302457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33112152233658699059534971 49668228350488048589302457)
        ·
          refine ⟨37251171262866036441976843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49668228350488048589302457 37251171262866036441976843)
          ·
            refine ⟨55876756894299054662965265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37251171262866036441976843 55876756894299054662965265)
            ·
              refine ⟨41907567670724290997223949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55876756894299054662965265 41907567670724290997223949)
              ·
                refine ⟨15715337876521609123958981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41907567670724290997223949 15715337876521609123958981)
                ·
                  refine ⟨2946625851847801710742309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15715337876521609123958981 2946625851847801710742309)
                  ·
                    refine ⟨552492347221462820764183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946625851847801710742309 552492347221462820764183)
                    ·
                      rfl

theorem cell23_3227925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_3227925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227925 prefixEnd_3227925 := by exact prefixLift 3227925
  have htrace : WordTrace (prefixWord ++ tailWord_3227925) baseStart_3227925 baseEnd_3227925 := by
    simpa [prefixWord, tailWord_3227925, baseEnd_3227925] using wordTrace_append hprefix tailTrace_3227925
  have hstable : (prefixWord ++ tailWord_3227925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227925).length < 2 ^ (prefixWord ++ tailWord_3227925).sum := by decide
  have hdescent : baseEnd_3227925 < baseStart_3227925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227943 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3227943 : Nat := 118140960795 + 3227943 * 2 ^ 59
def prefixEnd_3227943 : Nat := 4983230072969 + 3 ^ 40 * 3227943 * 2
def baseEnd_3227943 : Nat := 1657486284316169391867467

theorem tailTrace_3227943 : CollatzResearch.WordTrace tailWord_3227943 prefixEnd_3227943 1657486284316169391867467 := by
  unfold tailWord_3227943
  simp only [CollatzResearch.WordTrace]
  refine ⟨117732753344721274619168483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78488502229814183079445655 117732753344721274619168483)
  ·
    refine ⟨176599130017081911928752725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117732753344721274619168483 176599130017081911928752725)
    ·
      refine ⟨2069521054887678655415071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 176599130017081911928752725 2069521054887678655415071)
      ·
        refine ⟨3104281582331517983122607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069521054887678655415071 3104281582331517983122607)
        ·
          refine ⟨4656422373497276974683911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104281582331517983122607 4656422373497276974683911)
          ·
            refine ⟨6984633560245915462025867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656422373497276974683911 6984633560245915462025867)
            ·
              refine ⟨10476950340368873193038801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984633560245915462025867 10476950340368873193038801)
              ·
                refine ⟨7857712755276654894779101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10476950340368873193038801 7857712755276654894779101)
                ·
                  refine ⟨2946642283228745585542163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7857712755276654894779101 2946642283228745585542163)
                  ·
                    refine ⟨4419963424843118378313245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946642283228745585542163 4419963424843118378313245)
                    ·
                      refine ⟨1657486284316169391867467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4419963424843118378313245 1657486284316169391867467)
                      ·
                        rfl

theorem cell23_3227943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3227943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227943 prefixEnd_3227943 := by exact prefixLift 3227943
  have htrace : WordTrace (prefixWord ++ tailWord_3227943) baseStart_3227943 baseEnd_3227943 := by
    simpa [prefixWord, tailWord_3227943, baseEnd_3227943] using wordTrace_append hprefix tailTrace_3227943
  have hstable : (prefixWord ++ tailWord_3227943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227943).length < 2 ^ (prefixWord ++ tailWord_3227943).sum := by decide
  have hdescent : baseEnd_3227943 < baseStart_3227943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227955 : List Nat := [1, 1, 1, 2, 5, 1, 5, 7]
def baseStart_3227955 : Nat := 118140960795 + 3227955 * 2 ^ 59
def prefixEnd_3227955 : Nat := 4983230072969 + 3 ^ 40 * 3227955 * 2
def baseEnd_3227955 : Nat := 61388609114223086848793

theorem tailTrace_3227955 : CollatzResearch.WordTrace tailWord_3227955 prefixEnd_3227955 61388609114223086848793 := by
  unfold tailWord_3227955
  simp only [CollatzResearch.WordTrace]
  refine ⟨117733191020677800668605319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78488794013785200445736879 117733191020677800668605319)
  ·
    refine ⟨176599786531016701002907979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117733191020677800668605319 176599786531016701002907979)
    ·
      refine ⟨264899679796525051504361969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176599786531016701002907979 264899679796525051504361969)
      ·
        refine ⟨198674759847393788628271477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264899679796525051504361969 198674759847393788628271477)
        ·
          refine ⟨18625758735693167683900451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198674759847393788628271477 18625758735693167683900451)
          ·
            refine ⟨27938638103539751525850677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18625758735693167683900451 27938638103539751525850677)
            ·
              refine ⟨2619247322206851705548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27938638103539751525850677 2619247322206851705548501)
              ·
                refine ⟨61388609114223086848793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2619247322206851705548501 61388609114223086848793)
                ·
                  rfl

theorem cell23_3227955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 7].length) (baseStart_3227955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227955 prefixEnd_3227955 := by exact prefixLift 3227955
  have htrace : WordTrace (prefixWord ++ tailWord_3227955) baseStart_3227955 baseEnd_3227955 := by
    simpa [prefixWord, tailWord_3227955, baseEnd_3227955] using wordTrace_append hprefix tailTrace_3227955
  have hstable : (prefixWord ++ tailWord_3227955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227955).length < 2 ^ (prefixWord ++ tailWord_3227955).sum := by decide
  have hdescent : baseEnd_3227955 < baseStart_3227955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227966 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_3227966 : Nat := 118140960795 + 3227966 * 2 ^ 59
def prefixEnd_3227966 : Nat := 4983230072969 + 3 ^ 40 * 3227966 * 2
def baseEnd_3227966 : Nat := 1657498094371222801879861

theorem tailTrace_3227966 : CollatzResearch.WordTrace tailWord_3227966 prefixEnd_3227966 1657498094371222801879861 := by
  unfold tailWord_3227966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716699027954743693406969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78489061482425299698170501 14716699027954743693406969)
  ·
    refine ⟨11037524270966057770055227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14716699027954743693406969 11037524270966057770055227)
    ·
      refine ⟨16556286406449086655082841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11037524270966057770055227 16556286406449086655082841)
      ·
        refine ⟨12417214804836814991312131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16556286406449086655082841 12417214804836814991312131)
        ·
          refine ⟨18625822207255222486968197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12417214804836814991312131 18625822207255222486968197)
          ·
            refine ⟨3492341663860354216306537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18625822207255222486968197 3492341663860354216306537)
            ·
              refine ⟨2619256247895265662229903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492341663860354216306537 2619256247895265662229903)
              ·
                refine ⟨3928884371842898493344855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619256247895265662229903 3928884371842898493344855)
                ·
                  refine ⟨5893326557764347740017283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928884371842898493344855 5893326557764347740017283)
                  ·
                    refine ⟨8839989836646521610025925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5893326557764347740017283 8839989836646521610025925)
                    ·
                      refine ⟨1657498094371222801879861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8839989836646521610025925 1657498094371222801879861)
                      ·
                        rfl

theorem cell23_3227966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_3227966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227966 prefixEnd_3227966 := by exact prefixLift 3227966
  have htrace : WordTrace (prefixWord ++ tailWord_3227966) baseStart_3227966 baseEnd_3227966 := by
    simpa [prefixWord, tailWord_3227966, baseEnd_3227966] using wordTrace_append hprefix tailTrace_3227966
  have hstable : (prefixWord ++ tailWord_3227966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227966).length < 2 ^ (prefixWord ++ tailWord_3227966).sum := by decide
  have hdescent : baseEnd_3227966 < baseStart_3227966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227968 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_3227968 : Nat := 118140960795 + 3227968 * 2 ^ 59
def prefixEnd_3227968 : Nat := 4983230072969 + 3 ^ 40 * 3227968 * 2
def baseEnd_3227968 : Nat := 552499707110843931351617

theorem tailTrace_3227968 : CollatzResearch.WordTrace tailWord_3227968 prefixEnd_3227968 552499707110843931351617 := by
  unfold tailWord_3227968
  simp only [CollatzResearch.WordTrace]
  refine ⟨58866832584815351944414279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78489110113087135925885705 58866832584815351944414279)
  ·
    refine ⟨88300248877223027916621419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58866832584815351944414279 88300248877223027916621419)
    ·
      refine ⟨132450373315834541874932129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88300248877223027916621419 132450373315834541874932129)
      ·
        refine ⟨99337779986875906406199097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132450373315834541874932129 99337779986875906406199097)
        ·
          refine ⟨74503334990156929804649323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99337779986875906406199097 74503334990156929804649323)
          ·
            refine ⟨111755002485235394706973985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74503334990156929804649323 111755002485235394706973985)
            ·
              refine ⟨83816251863926546030230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111755002485235394706973985 83816251863926546030230489)
              ·
                refine ⟨62862188897944909522672867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83816251863926546030230489 62862188897944909522672867)
                ·
                  refine ⟨94293283346917364284009301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62862188897944909522672867 94293283346917364284009301)
                  ·
                    refine ⟨552499707110843931351617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94293283346917364284009301 552499707110843931351617)
                    ·
                      rfl

theorem cell23_3227968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_3227968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227968 prefixEnd_3227968 := by exact prefixLift 3227968
  have htrace : WordTrace (prefixWord ++ tailWord_3227968) baseStart_3227968 baseEnd_3227968 := by
    simpa [prefixWord, tailWord_3227968, baseEnd_3227968] using wordTrace_append hprefix tailTrace_3227968
  have hstable : (prefixWord ++ tailWord_3227968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227968).length < 2 ^ (prefixWord ++ tailWord_3227968).sum := by decide
  have hdescent : baseEnd_3227968 < baseStart_3227968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227972 : List Nat := [2, 3, 4, 1, 2, 1, 10]
def baseStart_3227972 : Nat := 118140960795 + 3227972 * 2 ^ 59
def prefixEnd_3227972 : Nat := 4983230072969 + 3 ^ 40 * 3227972 * 2
def baseEnd_3227972 : Nat := 20462977472285799733393

theorem tailTrace_3227972 : CollatzResearch.WordTrace tailWord_3227972 prefixEnd_3227972 20462977472285799733393 := by
  unfold tailWord_3227972
  simp only [CollatzResearch.WordTrace]
  refine ⟨58866905530808106285987085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78489207374410808381316113 58866905530808106285987085)
  ·
    refine ⟨22075089574053039857245157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58866905530808106285987085 22075089574053039857245157)
    ·
      refine ⟨4139079295134944973233467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22075089574053039857245157 4139079295134944973233467)
      ·
        refine ⟨6208618942702417459850201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139079295134944973233467 6208618942702417459850201)
        ·
          refine ⟨4656464207026813094887651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6208618942702417459850201 4656464207026813094887651)
          ·
            refine ⟨6984696310540219642331477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656464207026813094887651 6984696310540219642331477)
            ·
              refine ⟨20462977472285799733393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6984696310540219642331477 20462977472285799733393)
              ·
                rfl

theorem cell23_3227972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 10].length) (baseStart_3227972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227972 prefixEnd_3227972 := by exact prefixLift 3227972
  have htrace : WordTrace (prefixWord ++ tailWord_3227972) baseStart_3227972 baseEnd_3227972 := by
    simpa [prefixWord, tailWord_3227972, baseEnd_3227972] using wordTrace_append hprefix tailTrace_3227972
  have hstable : (prefixWord ++ tailWord_3227972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227972).length < 2 ^ (prefixWord ++ tailWord_3227972).sum := by decide
  have hdescent : baseEnd_3227972 < baseStart_3227972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227992 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_3227992 : Nat := 118140960795 + 3227992 * 2 ^ 59
def prefixEnd_3227992 : Nat := 4983230072969 + 3 ^ 40 * 3227992 * 2
def baseEnd_3227992 : Nat := 1657511444868239700154741

theorem tailTrace_3227992 : CollatzResearch.WordTrace tailWord_3227992 prefixEnd_3227992 1657511444868239700154741 := by
  unfold tailWord_3227992
  simp only [CollatzResearch.WordTrace]
  refine ⟨58867270260771877993851115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78489693681029170658468153 58867270260771877993851115)
  ·
    refine ⟨88300905391157816990776673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58867270260771877993851115 88300905391157816990776673)
    ·
      refine ⟨66225679043368362743082505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88300905391157816990776673 66225679043368362743082505)
      ·
        refine ⟨49669259282526272057311879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66225679043368362743082505 49669259282526272057311879)
        ·
          refine ⟨74503888923789408085967819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49669259282526272057311879 74503888923789408085967819)
          ·
            refine ⟨111755833385684112128951729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74503888923789408085967819 111755833385684112128951729)
            ·
              refine ⟨83816875039263084096713797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111755833385684112128951729 83816875039263084096713797)
              ·
                refine ⟨15715664069861828268133837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83816875039263084096713797 15715664069861828268133837)
                ·
                  refine ⟨5893374026198185600550189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15715664069861828268133837 5893374026198185600550189)
                  ·
                    refine ⟨2210015259824319600206321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5893374026198185600550189 2210015259824319600206321)
                    ·
                      refine ⟨1657511444868239700154741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210015259824319600206321 1657511444868239700154741)
                      ·
                        rfl

theorem cell23_3227992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_3227992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227992 prefixEnd_3227992 := by exact prefixLift 3227992
  have htrace : WordTrace (prefixWord ++ tailWord_3227992) baseStart_3227992 baseEnd_3227992 := by
    simpa [prefixWord, tailWord_3227992, baseEnd_3227992] using wordTrace_append hprefix tailTrace_3227992
  have hstable : (prefixWord ++ tailWord_3227992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227992).length < 2 ^ (prefixWord ++ tailWord_3227992).sum := by decide
  have hdescent : baseEnd_3227992 < baseStart_3227992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3227996 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3227996 : Nat := 118140960795 + 3227996 * 2 ^ 59
def prefixEnd_3227996 : Nat := 4983230072969 + 3 ^ 40 * 3227996 * 2
def baseEnd_3227996 : Nat := 1657513498790857684504723

theorem tailTrace_3227996 : CollatzResearch.WordTrace tailWord_3227996 prefixEnd_3227996 1657513498790857684504723 := by
  unfold tailWord_3227996
  simp only [CollatzResearch.WordTrace]
  refine ⟨58867343206764632335423921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78489790942352843113898561 58867343206764632335423921)
  ·
    refine ⟨44150507405073474251567941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58867343206764632335423921 44150507405073474251567941)
    ·
      refine ⟨8278220138451276422168989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44150507405073474251567941 8278220138451276422168989)
      ·
        refine ⟨3104332551919228658313371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8278220138451276422168989 3104332551919228658313371)
        ·
          refine ⟨4656498827878842987470057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104332551919228658313371 4656498827878842987470057)
          ·
            refine ⟨3492374120909132240602543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656498827878842987470057 3492374120909132240602543)
            ·
              refine ⟨5238561181363698360903815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492374120909132240602543 5238561181363698360903815)
              ·
                refine ⟨7857841772045547541355723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5238561181363698360903815 7857841772045547541355723)
                ·
                  refine ⟨11786762658068321312033585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7857841772045547541355723 11786762658068321312033585)
                  ·
                    refine ⟨8840071993551240984025189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11786762658068321312033585 8840071993551240984025189)
                    ·
                      refine ⟨1657513498790857684504723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8840071993551240984025189 1657513498790857684504723)
                      ·
                        rfl

theorem cell23_3227996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3227996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3227996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3227996 prefixEnd_3227996 := by exact prefixLift 3227996
  have htrace : WordTrace (prefixWord ++ tailWord_3227996) baseStart_3227996 baseEnd_3227996 := by
    simpa [prefixWord, tailWord_3227996, baseEnd_3227996] using wordTrace_append hprefix tailTrace_3227996
  have hstable : (prefixWord ++ tailWord_3227996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3227996).length < 2 ^ (prefixWord ++ tailWord_3227996).sum := by decide
  have hdescent : baseEnd_3227996 < baseStart_3227996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3227996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228009 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 1, 3, 2]
def baseStart_3228009 : Nat := 118140960795 + 3228009 * 2 ^ 59
def prefixEnd_3228009 : Nat := 4983230072969 + 3 ^ 40 * 3228009 * 2
def baseEnd_3228009 : Nat := 1657520174039366133642163

theorem tailTrace_3228009 : CollatzResearch.WordTrace tailWord_3228009 prefixEnd_3228009 1657520174039366133642163 := by
  unfold tailWord_3228009
  simp only [CollatzResearch.WordTrace]
  refine ⟨117735160562482167891071081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78490107041654778594047387 117735160562482167891071081)
  ·
    refine ⟨88301370421861625918303311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117735160562482167891071081 88301370421861625918303311)
    ·
      refine ⟨132452055632792438877454967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88301370421861625918303311 132452055632792438877454967)
      ·
        refine ⟨198678083449188658316182451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132452055632792438877454967 198678083449188658316182451)
        ·
          refine ⟨298017125173782987474273677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198678083449188658316182451 298017125173782987474273677)
          ·
            refine ⟨111756421940168620302852629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298017125173782987474273677 111756421940168620302852629)
            ·
              refine ⟨5238582278445404076696217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111756421940168620302852629 5238582278445404076696217)
              ·
                refine ⟨3928936708834053057522163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238582278445404076696217 3928936708834053057522163)
                ·
                  refine ⟨5893405063251079586283245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928936708834053057522163 5893405063251079586283245)
                  ·
                    refine ⟨2210026898719154844856217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5893405063251079586283245 2210026898719154844856217)
                    ·
                      refine ⟨1657520174039366133642163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210026898719154844856217 1657520174039366133642163)
                      ·
                        rfl

theorem cell23_3228009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3, 2].length) (baseStart_3228009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228009 prefixEnd_3228009 := by exact prefixLift 3228009
  have htrace : WordTrace (prefixWord ++ tailWord_3228009) baseStart_3228009 baseEnd_3228009 := by
    simpa [prefixWord, tailWord_3228009, baseEnd_3228009] using wordTrace_append hprefix tailTrace_3228009
  have hstable : (prefixWord ++ tailWord_3228009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228009).length < 2 ^ (prefixWord ++ tailWord_3228009).sum := by decide
  have hdescent : baseEnd_3228009 < baseStart_3228009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228025 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3228025 : Nat := 118140960795 + 3228025 * 2 ^ 59
def prefixEnd_3228025 : Nat := 4983230072969 + 3 ^ 40 * 3228025 * 2
def baseEnd_3228025 : Nat := 1657528389729838071042089

theorem tailTrace_3228025 : CollatzResearch.WordTrace tailWord_3228025 prefixEnd_3228025 1657528389729838071042089 := by
  unfold tailWord_3228025
  simp only [CollatzResearch.WordTrace]
  refine ⟨117735744130424202623653529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78490496086949468415769019 117735744130424202623653529)
  ·
    refine ⟨88301808097818151967740147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117735744130424202623653529 88301808097818151967740147)
    ·
      refine ⟨132452712146727227951610221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88301808097818151967740147 132452712146727227951610221)
      ·
        refine ⟨49669767055022710481853833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132452712146727227951610221 49669767055022710481853833)
        ·
          refine ⟨37252325291267032861390375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49669767055022710481853833 37252325291267032861390375)
          ·
            refine ⟨55878487936900549292085563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37252325291267032861390375 55878487936900549292085563)
            ·
              refine ⟨83817731905350823938128345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55878487936900549292085563 83817731905350823938128345)
              ·
                refine ⟨62863298929013117953596259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83817731905350823938128345 62863298929013117953596259)
                ·
                  refine ⟨94294948393519676930394389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62863298929013117953596259 94294948393519676930394389)
                  ·
                    refine ⟨4420075705946234856112237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94294948393519676930394389 4420075705946234856112237)
                    ·
                      refine ⟨1657528389729838071042089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420075705946234856112237 1657528389729838071042089)
                      ·
                        rfl

theorem cell23_3228025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3228025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228025 prefixEnd_3228025 := by exact prefixLift 3228025
  have htrace : WordTrace (prefixWord ++ tailWord_3228025) baseStart_3228025 baseEnd_3228025 := by
    simpa [prefixWord, tailWord_3228025, baseEnd_3228025] using wordTrace_append hprefix tailTrace_3228025
  have hstable : (prefixWord ++ tailWord_3228025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228025).length < 2 ^ (prefixWord ++ tailWord_3228025).sum := by decide
  have hdescent : baseEnd_3228025 < baseStart_3228025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228039 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_3228039 : Nat := 118140960795 + 3228039 * 2 ^ 59
def prefixEnd_3228039 : Nat := 4983230072969 + 3 ^ 40 * 3228039 * 2
def baseEnd_3228039 : Nat := 1657535578459001016267025

theorem tailTrace_3228039 : CollatzResearch.WordTrace tailWord_3228039 prefixEnd_3228039 1657535578459001016267025 := by
  unfold tailWord_3228039
  simp only [CollatzResearch.WordTrace]
  refine ⟨117736254752373483014663171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78490836501582322009775447 117736254752373483014663171)
  ·
    refine ⟨176604382128560224521994757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117736254752373483014663171 176604382128560224521994757)
    ·
      refine ⟨33113321649105042097874017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176604382128560224521994757 33113321649105042097874017)
      ·
        refine ⟨24834991236828781573405513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33113321649105042097874017 24834991236828781573405513)
        ·
          refine ⟨18626243427621586180054135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24834991236828781573405513 18626243427621586180054135)
          ·
            refine ⟨27939365141432379270081203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626243427621586180054135 27939365141432379270081203)
            ·
              refine ⟨41909047712148568905121805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27939365141432379270081203 41909047712148568905121805)
              ·
                refine ⟨15715892892055713339420677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41909047712148568905121805 15715892892055713339420677)
                ·
                  refine ⟨2946729917260446251141377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15715892892055713339420677 2946729917260446251141377)
                  ·
                    refine ⟨2210047437945334688356033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2946729917260446251141377 2210047437945334688356033)
                    ·
                      refine ⟨1657535578459001016267025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210047437945334688356033 1657535578459001016267025)
                      ·
                        rfl

theorem cell23_3228039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_3228039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228039 prefixEnd_3228039 := by exact prefixLift 3228039
  have htrace : WordTrace (prefixWord ++ tailWord_3228039) baseStart_3228039 baseEnd_3228039 := by
    simpa [prefixWord, tailWord_3228039, baseEnd_3228039] using wordTrace_append hprefix tailTrace_3228039
  have hstable : (prefixWord ++ tailWord_3228039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228039).length < 2 ^ (prefixWord ++ tailWord_3228039).sum := by decide
  have hdescent : baseEnd_3228039 < baseStart_3228039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228095 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_3228095 : Nat := 118140960795 + 3228095 * 2 ^ 59
def prefixEnd_3228095 : Nat := 4983230072969 + 3 ^ 40 * 3228095 * 2
def baseEnd_3228095 : Nat := 1657564333375652797166767

theorem tailTrace_3228095 : CollatzResearch.WordTrace tailWord_3228095 prefixEnd_3228095 1657564333375652797166767 := by
  unfold tailWord_3228095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117738297240170604578701739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78492198160113736385801159 117738297240170604578701739)
  ·
    refine ⟨176607445860255906868052609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117738297240170604578701739 176607445860255906868052609)
    ·
      refine ⟨132455584395191930151039457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176607445860255906868052609 132455584395191930151039457)
      ·
        refine ⟨99341688296393947613279593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132455584395191930151039457 99341688296393947613279593)
        ·
          refine ⟨74506266222295460709959695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99341688296393947613279593 74506266222295460709959695)
          ·
            refine ⟨111759399333443191064939543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74506266222295460709959695 111759399333443191064939543)
            ·
              refine ⟨167639099000164786597409315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111759399333443191064939543 167639099000164786597409315)
              ·
                refine ⟨251458648500247179896113973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167639099000164786597409315 251458648500247179896113973)
                ·
                  refine ⟨23574248296898173115260685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251458648500247179896113973 23574248296898173115260685)
                  ·
                    refine ⟨8840343111336814918222757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23574248296898173115260685 8840343111336814918222757)
                    ·
                      refine ⟨1657564333375652797166767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8840343111336814918222757 1657564333375652797166767)
                      ·
                        rfl

theorem cell23_3228095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_3228095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228095 prefixEnd_3228095 := by exact prefixLift 3228095
  have htrace : WordTrace (prefixWord ++ tailWord_3228095) baseStart_3228095 baseEnd_3228095 := by
    simpa [prefixWord, tailWord_3228095, baseEnd_3228095] using wordTrace_append hprefix tailTrace_3228095
  have hstable : (prefixWord ++ tailWord_3228095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228095).length < 2 ^ (prefixWord ++ tailWord_3228095).sum := by decide
  have hdescent : baseEnd_3228095 < baseStart_3228095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228142 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3228142 : Nat := 118140960795 + 3228142 * 2 ^ 59
def prefixEnd_3228142 : Nat := 4983230072969 + 3 ^ 40 * 3228142 * 2
def baseEnd_3228142 : Nat := 1657588466966414113279051

theorem tailTrace_3228142 : CollatzResearch.WordTrace tailWord_3228142 prefixEnd_3228142 1657588466966414113279051 := by
  unfold tailWord_3228142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14717501433875041450707835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78493340980666887737108453 14717501433875041450707835)
  ·
    refine ⟨22076252150812562176061753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14717501433875041450707835 22076252150812562176061753)
    ·
      refine ⟨16557189113109421632046315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22076252150812562176061753 16557189113109421632046315)
      ·
        refine ⟨24835783669664132448069473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16557189113109421632046315 24835783669664132448069473)
        ·
          refine ⟨18626837752248099336052105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24835783669664132448069473 18626837752248099336052105)
          ·
            refine ⟨13970128314186074502039079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18626837752248099336052105 13970128314186074502039079)
            ·
              refine ⟨20955192471279111753058619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13970128314186074502039079 20955192471279111753058619)
              ·
                refine ⟨31432788706918667629587929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20955192471279111753058619 31432788706918667629587929)
                ·
                  refine ⟨23574591530189000722190947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31432788706918667629587929 23574591530189000722190947)
                  ·
                    refine ⟨35361887295283501083286421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23574591530189000722190947 35361887295283501083286421)
                    ·
                      refine ⟨1657588466966414113279051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35361887295283501083286421 1657588466966414113279051)
                      ·
                        rfl

theorem cell23_3228142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3228142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228142 prefixEnd_3228142 := by exact prefixLift 3228142
  have htrace : WordTrace (prefixWord ++ tailWord_3228142) baseStart_3228142 baseEnd_3228142 := by
    simpa [prefixWord, tailWord_3228142, baseEnd_3228142] using wordTrace_append hprefix tailTrace_3228142
  have hstable : (prefixWord ++ tailWord_3228142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228142).length < 2 ^ (prefixWord ++ tailWord_3228142).sum := by decide
  have hdescent : baseEnd_3228142 < baseStart_3228142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228173 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3228173 : Nat := 118140960795 + 3228173 * 2 ^ 59
def prefixEnd_3228173 : Nat := 4983230072969 + 3 ^ 40 * 3228173 * 2
def baseEnd_3228173 : Nat := 552534794955567830663803

theorem tailTrace_3228173 : CollatzResearch.WordTrace tailWord_3228173 prefixEnd_3228173 552534794955567830663803 := by
  unfold tailWord_3228173
  simp only [CollatzResearch.WordTrace]
  refine ⟨117741142133888023900041173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78494094755925349266694115 117741142133888023900041173)
  ·
    refine ⟨2759558018763000560157215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 117741142133888023900041173 2759558018763000560157215)
    ·
      refine ⟨4139337028144500840235823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759558018763000560157215 4139337028144500840235823)
      ·
        refine ⟨6209005542216751260353735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139337028144500840235823 6209005542216751260353735)
        ·
          refine ⟨9313508313325126890530603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209005542216751260353735 9313508313325126890530603)
          ·
            refine ⟨13970262469987690335795905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9313508313325126890530603 13970262469987690335795905)
            ·
              refine ⟨10477696852490767751846929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13970262469987690335795905 10477696852490767751846929)
              ·
                refine ⟨7858272639368075813885197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10477696852490767751846929 7858272639368075813885197)
                ·
                  refine ⟨2946852239763028430206949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7858272639368075813885197 2946852239763028430206949)
                  ·
                    refine ⟨552534794955567830663803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2946852239763028430206949 552534794955567830663803)
                    ·
                      rfl

theorem cell23_3228173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3228173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228173 prefixEnd_3228173 := by exact prefixLift 3228173
  have htrace : WordTrace (prefixWord ++ tailWord_3228173) baseStart_3228173 baseEnd_3228173 := by
    simpa [prefixWord, tailWord_3228173, baseEnd_3228173] using wordTrace_append hprefix tailTrace_3228173
  have hstable : (prefixWord ++ tailWord_3228173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228173).length < 2 ^ (prefixWord ++ tailWord_3228173).sum := by decide
  have hdescent : baseEnd_3228173 < baseStart_3228173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228175 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_3228175 : Nat := 118140960795 + 3228175 * 2 ^ 59
def prefixEnd_3228175 : Nat := 4983230072969 + 3 ^ 40 * 3228175 * 2
def baseEnd_3228175 : Nat := 1657605411828012484166399

theorem tailTrace_3228175 : CollatzResearch.WordTrace tailWord_3228175 prefixEnd_3228175 1657605411828012484166399 := by
  unfold tailWord_3228175
  simp only [CollatzResearch.WordTrace]
  refine ⟨117741215079880778241613979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78494143386587185494409319 117741215079880778241613979)
  ·
    refine ⟨176611822619821167362420969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117741215079880778241613979 176611822619821167362420969)
    ·
      refine ⟨132458866964865875521815727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176611822619821167362420969 132458866964865875521815727)
      ·
        refine ⟨198688300447298813282723591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132458866964865875521815727 198688300447298813282723591)
        ·
          refine ⟨298032450670948219924085387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198688300447298813282723591 298032450670948219924085387)
          ·
            refine ⟨447048676006422329886128081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298032450670948219924085387 447048676006422329886128081)
            ·
              refine ⟨335286507004816747414596061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447048676006422329886128081 335286507004816747414596061)
              ·
                refine ⟨125732440126806280280473523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335286507004816747414596061 125732440126806280280473523)
                ·
                  refine ⟨188598660190209420420710285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125732440126806280280473523 188598660190209420420710285)
                  ·
                    refine ⟨70724497571328532657766357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188598660190209420420710285 70724497571328532657766357)
                    ·
                      refine ⟨1657605411828012484166399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70724497571328532657766357 1657605411828012484166399)
                      ·
                        rfl

theorem cell23_3228175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_3228175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228175 prefixEnd_3228175 := by exact prefixLift 3228175
  have htrace : WordTrace (prefixWord ++ tailWord_3228175) baseStart_3228175 baseEnd_3228175 := by
    simpa [prefixWord, tailWord_3228175, baseEnd_3228175] using wordTrace_append hprefix tailTrace_3228175
  have hstable : (prefixWord ++ tailWord_3228175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228175).length < 2 ^ (prefixWord ++ tailWord_3228175).sum := by decide
  have hdescent : baseEnd_3228175 < baseStart_3228175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228179 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 3]
def baseStart_3228179 : Nat := 118140960795 + 3228179 * 2 ^ 59
def prefixEnd_3228179 : Nat := 4983230072969 + 3 ^ 40 * 3228179 * 2
def baseEnd_3228179 : Nat := 1657607465750630468516381

theorem tailTrace_3228179 : CollatzResearch.WordTrace tailWord_3228179 prefixEnd_3228179 1657607465750630468516381 := by
  unfold tailWord_3228179
  simp only [CollatzResearch.WordTrace]
  refine ⟨117741360971866286924759591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78494240647910857949839727 117741360971866286924759591)
  ·
    refine ⟨176612041457799430387139387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117741360971866286924759591 176612041457799430387139387)
    ·
      refine ⟨264918062186699145580709081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176612041457799430387139387 264918062186699145580709081)
      ·
        refine ⟨198688546640024359185531811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264918062186699145580709081 198688546640024359185531811)
        ·
          refine ⟨298032819960036538778297717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198688546640024359185531811 298032819960036538778297717)
          ·
            refine ⟨27940576871253425510465411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298032819960036538778297717 27940576871253425510465411)
            ·
              refine ⟨41910865306880138265698117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27940576871253425510465411 41910865306880138265698117)
              ·
                refine ⟨7858287245040025924818397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41910865306880138265698117 7858287245040025924818397)
                ·
                  refine ⟨2946857716890009721806899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7858287245040025924818397 2946857716890009721806899)
                  ·
                    refine ⟨4420286575335014582710349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946857716890009721806899 4420286575335014582710349)
                    ·
                      refine ⟨1657607465750630468516381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420286575335014582710349 1657607465750630468516381)
                      ·
                        rfl

theorem cell23_3228179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 3].length) (baseStart_3228179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228179 prefixEnd_3228179 := by exact prefixLift 3228179
  have htrace : WordTrace (prefixWord ++ tailWord_3228179) baseStart_3228179 baseEnd_3228179 := by
    simpa [prefixWord, tailWord_3228179, baseEnd_3228179] using wordTrace_append hprefix tailTrace_3228179
  have hstable : (prefixWord ++ tailWord_3228179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228179).length < 2 ^ (prefixWord ++ tailWord_3228179).sum := by decide
  have hdescent : baseEnd_3228179 < baseStart_3228179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228232 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3228232 : Nat := 118140960795 + 3228232 * 2 ^ 59
def prefixEnd_3228232 : Nat := 4983230072969 + 3 ^ 40 * 3228232 * 2
def baseEnd_3228232 : Nat := 1657634680225318761153637

theorem tailTrace_3228232 : CollatzResearch.WordTrace tailWord_3228232 prefixEnd_3228232 1657634680225318761153637 := by
  unfold tailWord_3228232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58871647020337138488219475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78495529360449517984292633 58871647020337138488219475)
  ·
    refine ⟨88307470530505707732329213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58871647020337138488219475 88307470530505707732329213)
    ·
      refine ⟨33115301448939640399623455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88307470530505707732329213 33115301448939640399623455)
      ·
        refine ⟨49672952173409460599435183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33115301448939640399623455 49672952173409460599435183)
        ·
          refine ⟨74509428260114190899152775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49672952173409460599435183 74509428260114190899152775)
          ·
            refine ⟨111764142390171286348729163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74509428260114190899152775 111764142390171286348729163)
            ·
              refine ⟨167646213585256929523093745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111764142390171286348729163 167646213585256929523093745)
              ·
                refine ⟨125734660188942697142320309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167646213585256929523093745 125734660188942697142320309)
                ·
                  refine ⟨11787624392713377857092529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125734660188942697142320309 11787624392713377857092529)
                  ·
                    refine ⟨8840718294535033392819397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11787624392713377857092529 8840718294535033392819397)
                    ·
                      refine ⟨1657634680225318761153637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8840718294535033392819397 1657634680225318761153637)
                      ·
                        rfl

theorem cell23_3228232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3228232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228232 prefixEnd_3228232 := by exact prefixLift 3228232
  have htrace : WordTrace (prefixWord ++ tailWord_3228232) baseStart_3228232 baseEnd_3228232 := by
    simpa [prefixWord, tailWord_3228232, baseEnd_3228232] using wordTrace_append hprefix tailTrace_3228232
  have hstable : (prefixWord ++ tailWord_3228232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228232).length < 2 ^ (prefixWord ++ tailWord_3228232).sum := by decide
  have hdescent : baseEnd_3228232 < baseStart_3228232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228236 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3228236 : Nat := 118140960795 + 3228236 * 2 ^ 59
def prefixEnd_3228236 : Nat := 4983230072969 + 3 ^ 40 * 3228236 * 2
def baseEnd_3228236 : Nat := 1657636734147936745503619

theorem tailTrace_3228236 : CollatzResearch.WordTrace tailWord_3228236 prefixEnd_3228236 1657636734147936745503619 := by
  unfold tailWord_3228236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58871719966329892829792281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78495626621773190439723041 58871719966329892829792281)
  ·
    refine ⟨44153789974747419622344211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58871719966329892829792281 44153789974747419622344211)
    ·
      refine ⟨66230684962121129433516317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44153789974747419622344211 66230684962121129433516317)
      ·
        refine ⟨24836506860795423537568619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66230684962121129433516317 24836506860795423537568619)
        ·
          refine ⟨37254760291193135306352929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24836506860795423537568619 37254760291193135306352929)
          ·
            refine ⟨27941070218394851479764697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37254760291193135306352929 27941070218394851479764697)
            ·
              refine ⟨20955802663796138609823523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27941070218394851479764697 20955802663796138609823523)
              ·
                refine ⟨31433703995694207914735285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20955802663796138609823523 31433703995694207914735285)
                ·
                  refine ⟨2946909749596331992006433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31433703995694207914735285 2946909749596331992006433)
                  ·
                    refine ⟨2210182312197248994004825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2946909749596331992006433 2210182312197248994004825)
                    ·
                      refine ⟨1657636734147936745503619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210182312197248994004825 1657636734147936745503619)
                      ·
                        rfl

theorem cell23_3228236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3228236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228236 prefixEnd_3228236 := by exact prefixLift 3228236
  have htrace : WordTrace (prefixWord ++ tailWord_3228236) baseStart_3228236 baseEnd_3228236 := by
    simpa [prefixWord, tailWord_3228236, baseEnd_3228236] using wordTrace_append hprefix tailTrace_3228236
  have hstable : (prefixWord ++ tailWord_3228236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228236).length < 2 ^ (prefixWord ++ tailWord_3228236).sum := by decide
  have hdescent : baseEnd_3228236 < baseStart_3228236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228242 : List Nat := [3, 2, 2, 1, 2, 1, 1, 11]
def baseStart_3228242 : Nat := 118140960795 + 3228242 * 2 ^ 59
def prefixEnd_3228242 : Nat := 4983230072969 + 3 ^ 40 * 3228242 * 2
def baseEnd_3228242 : Nat := 61394067223402360075133

theorem tailTrace_3228242 : CollatzResearch.WordTrace tailWord_3228242 prefixEnd_3228242 61394067223402360075133 := by
  unfold tailWord_3228242
  simp only [CollatzResearch.WordTrace]
  refine ⟨29435914692659512171075745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78495772513758699122868653 29435914692659512171075745)
  ·
    refine ⟨22076936019494634128306809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29435914692659512171075745 22076936019494634128306809)
    ·
      refine ⟨16557702014620975596230107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22076936019494634128306809 16557702014620975596230107)
      ·
        refine ⟨24836553021931463394345161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16557702014620975596230107 24836553021931463394345161)
        ·
          refine ⟨18627414766448597545758871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24836553021931463394345161 18627414766448597545758871)
          ·
            refine ⟨27941122149672896318638307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18627414766448597545758871 27941122149672896318638307)
            ·
              refine ⟨41911683224509344477957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27941122149672896318638307 41911683224509344477957461)
              ·
                refine ⟨61394067223402360075133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41911683224509344477957461 61394067223402360075133)
                ·
                  rfl

theorem cell23_3228242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_3228242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228242 prefixEnd_3228242 := by exact prefixLift 3228242
  have htrace : WordTrace (prefixWord ++ tailWord_3228242) baseStart_3228242 baseEnd_3228242 := by
    simpa [prefixWord, tailWord_3228242, baseEnd_3228242] using wordTrace_append hprefix tailTrace_3228242
  have hstable : (prefixWord ++ tailWord_3228242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228242).length < 2 ^ (prefixWord ++ tailWord_3228242).sum := by decide
  have hdescent : baseEnd_3228242 < baseStart_3228242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228264 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3228264 : Nat := 118140960795 + 3228264 * 2 ^ 59
def prefixEnd_3228264 : Nat := 4983230072969 + 3 ^ 40 * 3228264 * 2
def baseEnd_3228264 : Nat := 1657651111606262635953491

theorem tailTrace_3228264 : CollatzResearch.WordTrace tailWord_3228264 prefixEnd_3228264 1657651111606262635953491 := by
  unfold tailWord_3228264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58872230588279173220801923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78496307451038897627735897 58872230588279173220801923)
  ·
    refine ⟨88308345882418759831202885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58872230588279173220801923 88308345882418759831202885)
    ·
      refine ⟨16557814852953517468350541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88308345882418759831202885 16557814852953517468350541)
      ·
        refine ⟨6209180569857569050631453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16557814852953517468350541 6209180569857569050631453)
        ·
          refine ⟨2328442713696588393986795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6209180569857569050631453 2328442713696588393986795)
          ·
            refine ⟨3492664070544882590980193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328442713696588393986795 3492664070544882590980193)
            ·
              refine ⟨2619498052908661943235145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492664070544882590980193 2619498052908661943235145)
              ·
                refine ⟨1964623539681496457426359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619498052908661943235145 1964623539681496457426359)
                ·
                  refine ⟨2946935309522244686139539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964623539681496457426359 2946935309522244686139539)
                  ·
                    refine ⟨4420402964283367029209309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946935309522244686139539 4420402964283367029209309)
                    ·
                      refine ⟨1657651111606262635953491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420402964283367029209309 1657651111606262635953491)
                      ·
                        rfl

theorem cell23_3228264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3228264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228264 prefixEnd_3228264 := by exact prefixLift 3228264
  have htrace : WordTrace (prefixWord ++ tailWord_3228264) baseStart_3228264 baseEnd_3228264 := by
    simpa [prefixWord, tailWord_3228264, baseEnd_3228264] using wordTrace_append hprefix tailTrace_3228264
  have hstable : (prefixWord ++ tailWord_3228264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228264).length < 2 ^ (prefixWord ++ tailWord_3228264).sum := by decide
  have hdescent : baseEnd_3228264 < baseStart_3228264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
