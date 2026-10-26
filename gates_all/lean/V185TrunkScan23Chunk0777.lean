import V185TrunkScan23Chunk0776

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4595693 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_4595693 : Nat := 118140960795 + 4595693 * 2 ^ 59
def prefixEnd_4595693 : Nat := 4983230072969 + 3 ^ 40 * 4595693 * 2
def baseEnd_4595693 : Nat := 786599816501064354567433

theorem tailTrace_4595693 : CollatzResearch.WordTrace tailWord_4595693 prefixEnd_4595693 786599816501064354567433 := by
  unfold tailWord_4595693
  simp only [CollatzResearch.WordTrace]
  refine ⟨167618694139596617721871733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111745796093064411814581155 167618694139596617721871733)
  ·
    refine ⟨15714252575587182911425475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167618694139596617721871733 15714252575587182911425475)
    ·
      refine ⟨23571378863380774367138213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15714252575587182911425475 23571378863380774367138213)
      ·
        refine ⟨4419633536883895193838415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23571378863380774367138213 4419633536883895193838415)
        ·
          refine ⟨6629450305325842790757623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419633536883895193838415 6629450305325842790757623)
          ·
            refine ⟨9944175457988764186136435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629450305325842790757623 9944175457988764186136435)
            ·
              refine ⟨14916263186983146279204653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9944175457988764186136435 14916263186983146279204653)
              ·
                refine ⟨5593598695118679854701745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14916263186983146279204653 5593598695118679854701745)
                ·
                  refine ⟨4195199021339009891026309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593598695118679854701745 4195199021339009891026309)
                  ·
                    refine ⟨786599816501064354567433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195199021339009891026309 786599816501064354567433)
                    ·
                      rfl

theorem cell23_4595693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_4595693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595693 prefixEnd_4595693 := by exact prefixLift 4595693
  have htrace : WordTrace (prefixWord ++ tailWord_4595693) baseStart_4595693 baseEnd_4595693 := by
    simpa [prefixWord, tailWord_4595693, baseEnd_4595693] using wordTrace_append hprefix tailTrace_4595693
  have hstable : (prefixWord ++ tailWord_4595693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595693).length < 2 ^ (prefixWord ++ tailWord_4595693).sum := by decide
  have hdescent : baseEnd_4595693 < baseStart_4595693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595733 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_4595733 : Nat := 118140960795 + 4595733 * 2 ^ 59
def prefixEnd_4595733 : Nat := 4983230072969 + 3 ^ 40 * 4595733 * 2
def baseEnd_4595733 : Nat := 2359819988729372907202115

theorem tailTrace_4595733 : CollatzResearch.WordTrace tailWord_4595733 prefixEnd_4595733 2359819988729372907202115 := by
  unfold tailWord_4595733
  simp only [CollatzResearch.WordTrace]
  refine ⟨167620153059451704553327853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111746768706301136368885235 167620153059451704553327853)
  ·
    refine ⟨62857557397294389207497945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167620153059451704553327853 62857557397294389207497945)
    ·
      refine ⟨47143168047970791905623459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62857557397294389207497945 47143168047970791905623459)
      ·
        refine ⟨70714752071956187858435189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47143168047970791905623459 70714752071956187858435189)
        ·
          refine ⟨6629508006745892611728299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70714752071956187858435189 6629508006745892611728299)
          ·
            refine ⟨9944262010118838917592449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629508006745892611728299 9944262010118838917592449)
            ·
              refine ⟨7458196507589129188194337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9944262010118838917592449 7458196507589129188194337)
              ·
                refine ⟨5593647380691846891145753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7458196507589129188194337 5593647380691846891145753)
                ·
                  refine ⟨4195235535518885168359315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593647380691846891145753 4195235535518885168359315)
                  ·
                    refine ⟨6292853303278327752538973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4195235535518885168359315 6292853303278327752538973)
                    ·
                      refine ⟨2359819988729372907202115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6292853303278327752538973 2359819988729372907202115)
                      ·
                        rfl

theorem cell23_4595733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_4595733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595733 prefixEnd_4595733 := by exact prefixLift 4595733
  have htrace : WordTrace (prefixWord ++ tailWord_4595733) baseStart_4595733 baseEnd_4595733 := by
    simpa [prefixWord, tailWord_4595733, baseEnd_4595733] using wordTrace_append hprefix tailTrace_4595733
  have hstable : (prefixWord ++ tailWord_4595733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595733).length < 2 ^ (prefixWord ++ tailWord_4595733).sum := by decide
  have hdescent : baseEnd_4595733 < baseStart_4595733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595762 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_4595762 : Nat := 118140960795 + 4595762 * 2 ^ 59
def prefixEnd_4595762 : Nat := 4983230072969 + 3 ^ 40 * 4595762 * 2
def baseEnd_4595762 : Nat := 262203875518705921526609

theorem tailTrace_4595762 : CollatzResearch.WordTrace tailWord_4595762 prefixEnd_4595762 262203875518705921526609 := by
  unfold tailWord_4595762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41905302694086660626533385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111747473850897761670755693 41905302694086660626533385)
  ·
    refine ⟨31428977020564995469900039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41905302694086660626533385 31428977020564995469900039)
    ·
      refine ⟨47143465530847493204850059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31428977020564995469900039 47143465530847493204850059)
      ·
        refine ⟨70715198296271239807275089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47143465530847493204850059 70715198296271239807275089)
        ·
          refine ⟨53036398722203429855456317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70715198296271239807275089 53036398722203429855456317)
          ·
            refine ⟨19888649520826286195796119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53036398722203429855456317 19888649520826286195796119)
            ·
              refine ⟨29832974281239429293694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19888649520826286195796119 29832974281239429293694179)
              ·
                refine ⟨44749461421859143940541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29832974281239429293694179 44749461421859143940541269)
                ·
                  refine ⟨262203875518705921526609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44749461421859143940541269 262203875518705921526609)
                  ·
                    rfl

theorem cell23_4595762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_4595762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595762 prefixEnd_4595762 := by exact prefixLift 4595762
  have htrace : WordTrace (prefixWord ++ tailWord_4595762) baseStart_4595762 baseEnd_4595762 := by
    simpa [prefixWord, tailWord_4595762, baseEnd_4595762] using wordTrace_append hprefix tailTrace_4595762
  have hstable : (prefixWord ++ tailWord_4595762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595762).length < 2 ^ (prefixWord ++ tailWord_4595762).sum := by decide
  have hdescent : baseEnd_4595762 < baseStart_4595762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595790 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_4595790 : Nat := 118140960795 + 4595790 * 2 ^ 59
def prefixEnd_4595790 : Nat := 4983230072969 + 3 ^ 40 * 4595790 * 2
def baseEnd_4595790 : Nat := 2359849257126679184189353

theorem tailTrace_4595790 : CollatzResearch.WordTrace tailWord_4595790 prefixEnd_4595790 2359849257126679184189353 := by
  unfold tailWord_4595790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952779002530650411019103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111748154680163468858768549 20952779002530650411019103)
  ·
    refine ⟨31429168503795975616528655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20952779002530650411019103 31429168503795975616528655)
    ·
      refine ⟨47143752755693963424792983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31429168503795975616528655 47143752755693963424792983)
      ·
        refine ⟨70715629133540945137189475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47143752755693963424792983 70715629133540945137189475)
        ·
          refine ⟨106073443700311417705784213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70715629133540945137189475 106073443700311417705784213)
          ·
            refine ⟨4972192673452097704958635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106073443700311417705784213 4972192673452097704958635)
            ·
              refine ⟨7458289010178146557437953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972192673452097704958635 7458289010178146557437953)
              ·
                refine ⟨5593716757633609918078465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7458289010178146557437953 5593716757633609918078465)
                ·
                  refine ⟨4195287568225207438558849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593716757633609918078465 4195287568225207438558849)
                  ·
                    refine ⟨3146465676168905578919137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195287568225207438558849 3146465676168905578919137)
                    ·
                      refine ⟨2359849257126679184189353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146465676168905578919137 2359849257126679184189353)
                      ·
                        rfl

theorem cell23_4595790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_4595790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595790 prefixEnd_4595790 := by exact prefixLift 4595790
  have htrace : WordTrace (prefixWord ++ tailWord_4595790) baseStart_4595790 baseEnd_4595790 := by
    simpa [prefixWord, tailWord_4595790, baseEnd_4595790] using wordTrace_append hprefix tailTrace_4595790
  have hstable : (prefixWord ++ tailWord_4595790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595790).length < 2 ^ (prefixWord ++ tailWord_4595790).sum := by decide
  have hdescent : baseEnd_4595790 < baseStart_4595790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595799 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_4595799 : Nat := 118140960795 + 4595799 * 2 ^ 59
def prefixEnd_4595799 : Nat := 4983230072969 + 3 ^ 40 * 4595799 * 2
def baseEnd_4595799 : Nat := 2359853878452569648976811

theorem tailTrace_4595799 : CollatzResearch.WordTrace tailWord_4595799 prefixEnd_4595799 2359853878452569648976811 := by
  unfold tailWord_4595799
  simp only [CollatzResearch.WordTrace]
  refine ⟨167622560277212597825230451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111748373518141731883486967 167622560277212597825230451)
  ·
    refine ⟨251433840415818896737845677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167622560277212597825230451 251433840415818896737845677)
    ·
      refine ⟨94287690155932086276692129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251433840415818896737845677 94287690155932086276692129)
      ·
        refine ⟨70715767616949064707519097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94287690155932086276692129 70715767616949064707519097)
        ·
          refine ⟨53036825712711798530639323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70715767616949064707519097 53036825712711798530639323)
          ·
            refine ⟨79555238569067697795958985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53036825712711798530639323 79555238569067697795958985)
            ·
              refine ⟨59666428926800773346969239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79555238569067697795958985 59666428926800773346969239)
              ·
                refine ⟨89499643390201160020453859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59666428926800773346969239 89499643390201160020453859)
                ·
                  refine ⟨134249465085301740030680789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89499643390201160020453859 134249465085301740030680789)
                  ·
                    refine ⟨3146471837936759531969081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134249465085301740030680789 3146471837936759531969081)
                    ·
                      refine ⟨2359853878452569648976811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146471837936759531969081 2359853878452569648976811)
                      ·
                        rfl

theorem cell23_4595799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_4595799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595799 prefixEnd_4595799 := by exact prefixLift 4595799
  have htrace : WordTrace (prefixWord ++ tailWord_4595799) baseStart_4595799 baseEnd_4595799 := by
    simpa [prefixWord, tailWord_4595799, baseEnd_4595799] using wordTrace_append hprefix tailTrace_4595799
  have hstable : (prefixWord ++ tailWord_4595799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595799).length < 2 ^ (prefixWord ++ tailWord_4595799).sum := by decide
  have hdescent : baseEnd_4595799 < baseStart_4595799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595802 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_4595802 : Nat := 118140960795 + 4595802 * 2 ^ 59
def prefixEnd_4595802 : Nat := 4983230072969 + 3 ^ 40 * 4595802 * 2
def baseEnd_4595802 : Nat := 2359855418894533137239297

theorem tailTrace_4595802 : CollatzResearch.WordTrace tailWord_4595802 prefixEnd_4595802 2359855418894533137239297 := by
  unfold tailWord_4595802
  simp only [CollatzResearch.WordTrace]
  refine ⟨41905667424050432334397415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111748446464134486225059773 41905667424050432334397415)
  ·
    refine ⟨62858501136075648501596123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41905667424050432334397415 62858501136075648501596123)
    ·
      refine ⟨94287751704113472752394185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62858501136075648501596123 94287751704113472752394185)
      ·
        refine ⟨70715813778085104564295639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94287751704113472752394185 70715813778085104564295639)
        ·
          refine ⟨106073720667127656846443459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70715813778085104564295639 106073720667127656846443459)
          ·
            refine ⟨159110581000691485269665189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106073720667127656846443459 159110581000691485269665189)
            ·
              refine ⟨29833233937629653488062223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159110581000691485269665189 29833233937629653488062223)
              ·
                refine ⟨44749850906444480232093335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29833233937629653488062223 44749850906444480232093335)
                ·
                  refine ⟨67124776359666720348140003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44749850906444480232093335 67124776359666720348140003)
                  ·
                    refine ⟨100687164539500080522210005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67124776359666720348140003 100687164539500080522210005)
                    ·
                      refine ⟨2359855418894533137239297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100687164539500080522210005 2359855418894533137239297)
                      ·
                        rfl

theorem cell23_4595802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_4595802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595802 prefixEnd_4595802 := by exact prefixLift 4595802
  have htrace : WordTrace (prefixWord ++ tailWord_4595802) baseStart_4595802 baseEnd_4595802 := by
    simpa [prefixWord, tailWord_4595802, baseEnd_4595802] using wordTrace_append hprefix tailTrace_4595802
  have hstable : (prefixWord ++ tailWord_4595802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595802).length < 2 ^ (prefixWord ++ tailWord_4595802).sum := by decide
  have hdescent : baseEnd_4595802 < baseStart_4595802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595832 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_4595832 : Nat := 118140960795 + 4595832 * 2 ^ 59
def prefixEnd_4595832 : Nat := 4983230072969 + 3 ^ 40 * 4595832 * 2
def baseEnd_4595832 : Nat := 2359870823314168019864159

theorem tailTrace_4595832 : CollatzResearch.WordTrace tailWord_4595832 prefixEnd_4595832 2359870823314168019864159 := by
  unfold tailWord_4595832
  simp only [CollatzResearch.WordTrace]
  refine ⟨83811881943046522230590875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111749175924062029640787833 83811881943046522230590875)
  ·
    refine ⟨125717822914569783345886313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83811881943046522230590875 125717822914569783345886313)
    ·
      refine ⟨94288367185927337509414735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125717822914569783345886313 94288367185927337509414735)
      ·
        refine ⟨141432550778891006264122103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94288367185927337509414735 141432550778891006264122103)
        ·
          refine ⟨212148826168336509396183155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141432550778891006264122103 212148826168336509396183155)
          ·
            refine ⟨318223239252504764094274733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212148826168336509396183155 318223239252504764094274733)
            ·
              refine ⟨119333714719689286535353025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318223239252504764094274733 119333714719689286535353025)
              ·
                refine ⟨89500286039766964901514769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119333714719689286535353025 89500286039766964901514769)
                ·
                  refine ⟨67125214529825223676136077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89500286039766964901514769 67125214529825223676136077)
                  ·
                    refine ⟨25171955448684458878551029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67125214529825223676136077 25171955448684458878551029)
                    ·
                      refine ⟨2359870823314168019864159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25171955448684458878551029 2359870823314168019864159)
                      ·
                        rfl

theorem cell23_4595832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_4595832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595832 prefixEnd_4595832 := by exact prefixLift 4595832
  have htrace : WordTrace (prefixWord ++ tailWord_4595832) baseStart_4595832 baseEnd_4595832 := by
    simpa [prefixWord, tailWord_4595832, baseEnd_4595832] using wordTrace_append hprefix tailTrace_4595832
  have hstable : (prefixWord ++ tailWord_4595832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595832).length < 2 ^ (prefixWord ++ tailWord_4595832).sum := by decide
  have hdescent : baseEnd_4595832 < baseStart_4595832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595919 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_4595919 : Nat := 118140960795 + 4595919 * 2 ^ 59
def prefixEnd_4595919 : Nat := 4983230072969 + 3 ^ 40 * 4595919 * 2
def baseEnd_4595919 : Nat := 2359915496131109179476259

theorem tailTrace_4595919 : CollatzResearch.WordTrace tailWord_4595919 prefixEnd_4595919 2359915496131109179476259 := by
  unfold tailWord_4595919
  simp only [CollatzResearch.WordTrace]
  refine ⟨167626937036777858319598811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111751291357851905546399207 167626937036777858319598811)
  ·
    refine ⟨251440405555166787479398217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167626937036777858319598811 251440405555166787479398217)
    ·
      refine ⟨188580304166375090609548663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251440405555166787479398217 188580304166375090609548663)
      ·
        refine ⟨282870456249562635914322995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188580304166375090609548663 282870456249562635914322995)
        ·
          refine ⟨424305684374343953871484493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282870456249562635914322995 424305684374343953871484493)
          ·
            refine ⟨159114631640378982701806685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424305684374343953871484493 159114631640378982701806685)
            ·
              refine ⟨59667986865142118513177507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159114631640378982701806685 59667986865142118513177507)
              ·
                refine ⟨89501980297713177769766261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59667986865142118513177507 89501980297713177769766261)
                ·
                  refine ⟨8390810652910610415915587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89501980297713177769766261 8390810652910610415915587)
                  ·
                    refine ⟨12586215979365915623873381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8390810652910610415915587 12586215979365915623873381)
                    ·
                      refine ⟨2359915496131109179476259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12586215979365915623873381 2359915496131109179476259)
                      ·
                        rfl

theorem cell23_4595919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_4595919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595919 prefixEnd_4595919 := by exact prefixLift 4595919
  have htrace : WordTrace (prefixWord ++ tailWord_4595919) baseStart_4595919 baseEnd_4595919 := by
    simpa [prefixWord, tailWord_4595919, baseEnd_4595919] using wordTrace_append hprefix tailTrace_4595919
  have hstable : (prefixWord ++ tailWord_4595919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595919).length < 2 ^ (prefixWord ++ tailWord_4595919).sum := by decide
  have hdescent : baseEnd_4595919 < baseStart_4595919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595929 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_4595929 : Nat := 118140960795 + 4595929 * 2 ^ 59
def prefixEnd_4595929 : Nat := 4983230072969 + 3 ^ 40 * 4595929 * 2
def baseEnd_4595929 : Nat := 786640210312551380117071

theorem tailTrace_4595929 : CollatzResearch.WordTrace tailWord_4595929 prefixEnd_4595929 786640210312551380117071 := by
  unfold tailWord_4595929
  simp only [CollatzResearch.WordTrace]
  refine ⟨167627301766741630027462841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111751534511161086684975227 167627301766741630027462841)
  ·
    refine ⟨125720476325056222520597131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167627301766741630027462841 125720476325056222520597131)
    ·
      refine ⟨188580714487584333780895697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125720476325056222520597131 188580714487584333780895697)
      ·
        refine ⟨141435535865688250335671773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188580714487584333780895697 141435535865688250335671773)
        ·
          refine ⟨53038325949633093875876915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141435535865688250335671773 53038325949633093875876915)
          ·
            refine ⟨79557488924449640813815373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53038325949633093875876915 79557488924449640813815373)
            ·
              refine ⟨29834058346668615305180765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79557488924449640813815373 29834058346668615305180765)
              ·
                refine ⟨11187771880000730739442787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29834058346668615305180765 11187771880000730739442787)
                ·
                  refine ⟨16781657820001096109164181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11187771880000730739442787 16781657820001096109164181)
                  ·
                    refine ⟨786640210312551380117071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16781657820001096109164181 786640210312551380117071)
                    ·
                      rfl

theorem cell23_4595929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_4595929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595929 prefixEnd_4595929 := by exact prefixLift 4595929
  have htrace : WordTrace (prefixWord ++ tailWord_4595929) baseStart_4595929 baseEnd_4595929 := by
    simpa [prefixWord, tailWord_4595929, baseEnd_4595929] using wordTrace_append hprefix tailTrace_4595929
  have hstable : (prefixWord ++ tailWord_4595929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595929).length < 2 ^ (prefixWord ++ tailWord_4595929).sum := by decide
  have hdescent : baseEnd_4595929 < baseStart_4595929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595936 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_4595936 : Nat := 118140960795 + 4595936 * 2 ^ 59
def prefixEnd_4595936 : Nat := 4983230072969 + 3 ^ 40 * 4595936 * 2
def baseEnd_4595936 : Nat := 2359924225302235612963681

theorem tailTrace_4595936 : CollatzResearch.WordTrace tailWord_4595936 prefixEnd_4595936 2359924225302235612963681 := by
  unfold tailWord_4595936
  simp only [CollatzResearch.WordTrace]
  refine ⟨83813778538858135111483831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111751704718477513481978441 83813778538858135111483831)
  ·
    refine ⟨125720667808287202667225747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83813778538858135111483831 125720667808287202667225747)
    ·
      refine ⟨188581001712430804000838621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125720667808287202667225747 188581001712430804000838621)
      ·
        refine ⟨70717875642161551500314483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188581001712430804000838621 70717875642161551500314483)
        ·
          refine ⟨106076813463242327250471725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70717875642161551500314483 106076813463242327250471725)
          ·
            refine ⟨39778805048715872718926897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106076813463242327250471725 39778805048715872718926897)
            ·
              refine ⟨29834103786536904539195173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39778805048715872718926897 29834103786536904539195173)
              ·
                refine ⟨5593894459975669601099095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29834103786536904539195173 5593894459975669601099095)
                ·
                  refine ⟨8390841689963504401648643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5593894459975669601099095 8390841689963504401648643)
                  ·
                    refine ⟨12586262534945256602472965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8390841689963504401648643 12586262534945256602472965)
                    ·
                      refine ⟨2359924225302235612963681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12586262534945256602472965 2359924225302235612963681)
                      ·
                        rfl

theorem cell23_4595936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_4595936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595936 prefixEnd_4595936 := by exact prefixLift 4595936
  have htrace : WordTrace (prefixWord ++ tailWord_4595936) baseStart_4595936 baseEnd_4595936 := by
    simpa [prefixWord, tailWord_4595936, baseEnd_4595936] using wordTrace_append hprefix tailTrace_4595936
  have hstable : (prefixWord ++ tailWord_4595936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595936).length < 2 ^ (prefixWord ++ tailWord_4595936).sum := by decide
  have hdescent : baseEnd_4595936 < baseStart_4595936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595946 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_4595946 : Nat := 118140960795 + 4595946 * 2 ^ 59
def prefixEnd_4595946 : Nat := 4983230072969 + 3 ^ 40 * 4595946 * 2
def baseEnd_4595946 : Nat := 786643120036260191279545

theorem tailTrace_4595946 : CollatzResearch.WordTrace tailWord_4595946 prefixEnd_4595946 786643120036260191279545 := by
  unfold tailWord_4595946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41906980451920010482707923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111751947871786694620554461 41906980451920010482707923)
  ·
    refine ⟨62860470677880015724061885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41906980451920010482707923 62860470677880015724061885)
    ·
      refine ⟨23572676504205005896523207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62860470677880015724061885 23572676504205005896523207)
      ·
        refine ⟨35359014756307508844784811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23572676504205005896523207 35359014756307508844784811)
        ·
          refine ⟨53038522134461263267177217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35359014756307508844784811 53038522134461263267177217)
          ·
            refine ⟨39778891600845947450382913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53038522134461263267177217 39778891600845947450382913)
            ·
              refine ⟨29834168700634460587787185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39778891600845947450382913 29834168700634460587787185)
              ·
                refine ⟨22375626525475845440840389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29834168700634460587787185 22375626525475845440840389)
                ·
                  refine ⟨4195429973526721020157573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22375626525475845440840389 4195429973526721020157573)
                  ·
                    refine ⟨786643120036260191279545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195429973526721020157573 786643120036260191279545)
                    ·
                      rfl

theorem cell23_4595946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_4595946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595946 prefixEnd_4595946 := by exact prefixLift 4595946
  have htrace : WordTrace (prefixWord ++ tailWord_4595946) baseStart_4595946 baseEnd_4595946 := by
    simpa [prefixWord, tailWord_4595946, baseEnd_4595946] using wordTrace_append hprefix tailTrace_4595946
  have hstable : (prefixWord ++ tailWord_4595946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595946).length < 2 ^ (prefixWord ++ tailWord_4595946).sum := by decide
  have hdescent : baseEnd_4595946 < baseStart_4595946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595953 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_4595953 : Nat := 118140960795 + 4595953 * 2 ^ 59
def prefixEnd_4595953 : Nat := 4983230072969 + 3 ^ 40 * 4595953 * 2
def baseEnd_4595953 : Nat := 2359932954473362046451103

theorem tailTrace_4595953 : CollatzResearch.WordTrace tailWord_4595953 prefixEnd_4595953 2359932954473362046451103 := by
  unfold tailWord_4595953
  simp only [CollatzResearch.WordTrace]
  refine ⟨167628177118654682126336513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111752118079103121417557675 167628177118654682126336513)
  ·
    refine ⟨125721132838991011594752385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167628177118654682126336513 125721132838991011594752385)
    ·
      refine ⟨94290849629243258696064289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125721132838991011594752385 94290849629243258696064289)
      ·
        refine ⟨70718137221932444022048217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94290849629243258696064289 70718137221932444022048217)
        ·
          refine ⟨53038602916449333016536163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70718137221932444022048217 53038602916449333016536163)
          ·
            refine ⟨79557904374673999524804245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53038602916449333016536163 79557904374673999524804245)
            ·
              refine ⟨3729276767562843727725199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79557904374673999524804245 3729276767562843727725199)
              ·
                refine ⟨5593915151344265591587799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729276767562843727725199 5593915151344265591587799)
                ·
                  refine ⟨8390872727016398387381699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5593915151344265591587799 8390872727016398387381699)
                  ·
                    refine ⟨12586309090524597581072549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8390872727016398387381699 12586309090524597581072549)
                    ·
                      refine ⟨2359932954473362046451103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12586309090524597581072549 2359932954473362046451103)
                      ·
                        rfl

theorem cell23_4595953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_4595953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595953 prefixEnd_4595953 := by exact prefixLift 4595953
  have htrace : WordTrace (prefixWord ++ tailWord_4595953) baseStart_4595953 baseEnd_4595953 := by
    simpa [prefixWord, tailWord_4595953, baseEnd_4595953] using wordTrace_append hprefix tailTrace_4595953
  have hstable : (prefixWord ++ tailWord_4595953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595953).length < 2 ^ (prefixWord ++ tailWord_4595953).sum := by decide
  have hdescent : baseEnd_4595953 < baseStart_4595953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595966 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4595966 : Nat := 118140960795 + 4595966 * 2 ^ 59
def prefixEnd_4595966 : Nat := 4983230072969 + 3 ^ 40 * 4595966 * 2
def baseEnd_4595966 : Nat := 2359939629721870495588543

theorem tailTrace_4595966 : CollatzResearch.WordTrace tailWord_4595966 prefixEnd_4595966 2359939629721870495588543 := by
  unfold tailWord_4595966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20953581408450948168319969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111752434178405056897706501 20953581408450948168319969)
  ·
    refine ⟨15715186056338211126239977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20953581408450948168319969 15715186056338211126239977)
    ·
      refine ⟨11786389542253658344679983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15715186056338211126239977 11786389542253658344679983)
      ·
        refine ⟨17679584313380487517019975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11786389542253658344679983 17679584313380487517019975)
        ·
          refine ⟨26519376470070731275529963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17679584313380487517019975 26519376470070731275529963)
          ·
            refine ⟨39779064705106096913294945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26519376470070731275529963 39779064705106096913294945)
            ·
              refine ⟨29834298528829572684971209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39779064705106096913294945 29834298528829572684971209)
              ·
                refine ⟨22375723896622179513728407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29834298528829572684971209 22375723896622179513728407)
                ·
                  refine ⟨33563585844933269270592611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22375723896622179513728407 33563585844933269270592611)
                  ·
                    refine ⟨50345378767399903905888917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33563585844933269270592611 50345378767399903905888917)
                    ·
                      refine ⟨2359939629721870495588543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50345378767399903905888917 2359939629721870495588543)
                      ·
                        rfl

theorem cell23_4595966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4595966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595966 prefixEnd_4595966 := by exact prefixLift 4595966
  have htrace : WordTrace (prefixWord ++ tailWord_4595966) baseStart_4595966 baseEnd_4595966 := by
    simpa [prefixWord, tailWord_4595966, baseEnd_4595966] using wordTrace_append hprefix tailTrace_4595966
  have hstable : (prefixWord ++ tailWord_4595966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595966).length < 2 ^ (prefixWord ++ tailWord_4595966).sum := by decide
  have hdescent : baseEnd_4595966 < baseStart_4595966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4595989 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_4595989 : Nat := 118140960795 + 4595989 * 2 ^ 59
def prefixEnd_4595989 : Nat := 4983230072969 + 3 ^ 40 * 4595989 * 2
def baseEnd_4595989 : Nat := 786650479925641301866979

theorem tailTrace_4595989 : CollatzResearch.WordTrace tailWord_4595989 prefixEnd_4595989 786650479925641301866979 := by
  unfold tailWord_4595989
  simp only [CollatzResearch.WordTrace]
  refine ⟨167629490146524260274647021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111752993431016173516431347 167629490146524260274647021)
  ·
    refine ⟨62861058804946597602992633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167629490146524260274647021 62861058804946597602992633)
    ·
      refine ⟨47145794103709948202244475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62861058804946597602992633 47145794103709948202244475)
      ·
        refine ⟨70718691155564922303366713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47145794103709948202244475 70718691155564922303366713)
        ·
          refine ⟨53039018366673691727525035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70718691155564922303366713 53039018366673691727525035)
          ·
            refine ⟨79558527550010537591287553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53039018366673691727525035 79558527550010537591287553)
            ·
              refine ⟨59668895662507903193465665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79558527550010537591287553 59668895662507903193465665)
              ·
                refine ⟨44751671746880927395099249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59668895662507903193465665 44751671746880927395099249)
                ·
                  refine ⟨33563753810160695546324437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44751671746880927395099249 33563753810160695546324437)
                  ·
                    refine ⟨786650479925641301866979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33563753810160695546324437 786650479925641301866979)
                    ·
                      rfl

theorem cell23_4595989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_4595989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4595989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4595989 prefixEnd_4595989 := by exact prefixLift 4595989
  have htrace : WordTrace (prefixWord ++ tailWord_4595989) baseStart_4595989 baseEnd_4595989 := by
    simpa [prefixWord, tailWord_4595989, baseEnd_4595989] using wordTrace_append hprefix tailTrace_4595989
  have hstable : (prefixWord ++ tailWord_4595989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4595989).length < 2 ^ (prefixWord ++ tailWord_4595989).sum := by decide
  have hdescent : baseEnd_4595989 < baseStart_4595989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4595989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596004 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 1, 2, 2]
def baseStart_4596004 : Nat := 118140960795 + 4596004 * 2 ^ 59
def prefixEnd_4596004 : Nat := 4983230072969 + 3 ^ 40 * 4596004 * 2
def baseEnd_4596004 : Nat := 2359959141986741346913369

theorem tailTrace_4596004 : CollatzResearch.WordTrace tailWord_4596004 prefixEnd_4596004 2359959141986741346913369 := by
  unfold tailWord_4596004
  simp only [CollatzResearch.WordTrace]
  refine ⟨83815018620734958918221533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111753358160979945224295377 83815018620734958918221533)
  ·
    refine ⟨31430631982775609594333075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83815018620734958918221533 31430631982775609594333075)
    ·
      refine ⟨47145947974163414391499613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31430631982775609594333075 47145947974163414391499613)
      ·
        refine ⟨17679730490311280396812355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47145947974163414391499613 17679730490311280396812355)
        ·
          refine ⟨26519595735466920595218533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17679730490311280396812355 26519595735466920595218533)
          ·
            refine ⟨4972424200400047611603475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26519595735466920595218533 4972424200400047611603475)
            ·
              refine ⟨7458636300600071417405213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972424200400047611603475 7458636300600071417405213)
              ·
                refine ⟨2796988612725026781526955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7458636300600071417405213 2796988612725026781526955)
                ·
                  refine ⟨4195482919087540172290433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796988612725026781526955 4195482919087540172290433)
                  ·
                    refine ⟨3146612189315655129217825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195482919087540172290433 3146612189315655129217825)
                    ·
                      refine ⟨2359959141986741346913369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146612189315655129217825 2359959141986741346913369)
                      ·
                        rfl

theorem cell23_4596004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_4596004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596004 prefixEnd_4596004 := by exact prefixLift 4596004
  have htrace : WordTrace (prefixWord ++ tailWord_4596004) baseStart_4596004 baseEnd_4596004 := by
    simpa [prefixWord, tailWord_4596004, baseEnd_4596004] using wordTrace_append hprefix tailTrace_4596004
  have hstable : (prefixWord ++ tailWord_4596004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596004).length < 2 ^ (prefixWord ++ tailWord_4596004).sum := by decide
  have hdescent : baseEnd_4596004 < baseStart_4596004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596007 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4596007 : Nat := 118140960795 + 4596007 * 2 ^ 59
def prefixEnd_4596007 : Nat := 4983230072969 + 3 ^ 40 * 4596007 * 2
def baseEnd_4596007 : Nat := 2359960682428704835175855

theorem tailTrace_4596007 : CollatzResearch.WordTrace tailWord_4596007 prefixEnd_4596007 2359960682428704835175855 := by
  unfold tailWord_4596007
  simp only [CollatzResearch.WordTrace]
  refine ⟨167630146660459049348802275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111753431106972699565868183 167630146660459049348802275)
  ·
    refine ⟨251445219990688574023203413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167630146660459049348802275 251445219990688574023203413)
    ·
      refine ⟨2946623671765881726834415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 251445219990688574023203413 2946623671765881726834415)
      ·
        refine ⟨4419935507648822590251623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2946623671765881726834415 4419935507648822590251623)
        ·
          refine ⟨6629903261473233885377435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419935507648822590251623 6629903261473233885377435)
          ·
            refine ⟨9944854892209850828066153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629903261473233885377435 9944854892209850828066153)
            ·
              refine ⟨7458641169157388121049615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9944854892209850828066153 7458641169157388121049615)
              ·
                refine ⟨11187961753736082181574423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7458641169157388121049615 11187961753736082181574423)
                ·
                  refine ⟨16781942630604123272361635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11187961753736082181574423 16781942630604123272361635)
                  ·
                    refine ⟨25172913945906184908542453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16781942630604123272361635 25172913945906184908542453)
                    ·
                      refine ⟨2359960682428704835175855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25172913945906184908542453 2359960682428704835175855)
                      ·
                        rfl

theorem cell23_4596007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4596007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596007 prefixEnd_4596007 := by exact prefixLift 4596007
  have htrace : WordTrace (prefixWord ++ tailWord_4596007) baseStart_4596007 baseEnd_4596007 := by
    simpa [prefixWord, tailWord_4596007, baseEnd_4596007] using wordTrace_append hprefix tailTrace_4596007
  have hstable : (prefixWord ++ tailWord_4596007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596007).length < 2 ^ (prefixWord ++ tailWord_4596007).sum := by decide
  have hdescent : baseEnd_4596007 < baseStart_4596007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596020 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_4596020 : Nat := 118140960795 + 4596020 * 2 ^ 59
def prefixEnd_4596020 : Nat := 4983230072969 + 3 ^ 40 * 4596020 * 2
def baseEnd_4596020 : Nat := 2359967357677213284313295

theorem tailTrace_4596020 : CollatzResearch.WordTrace tailWord_4596020 prefixEnd_4596020 2359967357677213284313295 := by
  unfold tailWord_4596020
  simp only [CollatzResearch.WordTrace]
  refine ⟨83815310404705976284512757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111753747206274635046017009 83815310404705976284512757)
  ·
    refine ⟨7857685350441185276673071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83815310404705976284512757 7857685350441185276673071)
    ·
      refine ⟨11786528025661777915009607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7857685350441185276673071 11786528025661777915009607)
      ·
        refine ⟨17679792038492666872514411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11786528025661777915009607 17679792038492666872514411)
        ·
          refine ⟨26519688057739000308771617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17679792038492666872514411 26519688057739000308771617)
          ·
            refine ⟨19889766043304250231578713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26519688057739000308771617 19889766043304250231578713)
            ·
              refine ⟨14917324532478187673684035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19889766043304250231578713 14917324532478187673684035)
              ·
                refine ⟨22375986798717281510526053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14917324532478187673684035 22375986798717281510526053)
                ·
                  refine ⟨4195497524759490283223635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22375986798717281510526053 4195497524759490283223635)
                  ·
                    refine ⟨6293246287139235424835453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4195497524759490283223635 6293246287139235424835453)
                    ·
                      refine ⟨2359967357677213284313295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293246287139235424835453 2359967357677213284313295)
                      ·
                        rfl

theorem cell23_4596020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_4596020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596020 prefixEnd_4596020 := by exact prefixLift 4596020
  have htrace : WordTrace (prefixWord ++ tailWord_4596020) baseStart_4596020 baseEnd_4596020 := by
    simpa [prefixWord, tailWord_4596020, baseEnd_4596020] using wordTrace_append hprefix tailTrace_4596020
  have hstable : (prefixWord ++ tailWord_4596020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596020).length < 2 ^ (prefixWord ++ tailWord_4596020).sum := by decide
  have hdescent : baseEnd_4596020 < baseStart_4596020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596043 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 6, 2, 2]
def baseStart_4596043 : Nat := 118140960795 + 4596043 * 2 ^ 59
def prefixEnd_4596043 : Nat := 4983230072969 + 3 ^ 40 * 4596043 * 2
def baseEnd_4596043 : Nat := 2359979167732266694325689

theorem tailTrace_4596043 : CollatzResearch.WordTrace tailWord_4596043 prefixEnd_4596043 2359979167732266694325689 := by
  unfold tailWord_4596043
  simp only [CollatzResearch.WordTrace]
  refine ⟨167631459688328627497112783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111754306458885751664741855 167631459688328627497112783)
  ·
    refine ⟨251447189532492941245669175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167631459688328627497112783 251447189532492941245669175)
    ·
      refine ⟨377170784298739411868503763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251447189532492941245669175 377170784298739411868503763)
      ·
        refine ⟨565756176448109117802755645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377170784298739411868503763 565756176448109117802755645)
        ·
          refine ⟨212158566168040919176033367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565756176448109117802755645 212158566168040919176033367)
          ·
            refine ⟨318237849252061378764050051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212158566168040919176033367 318237849252061378764050051)
            ·
              refine ⟨477356773878092068146075077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318237849252061378764050051 477356773878092068146075077)
              ·
                refine ⟨89504395102142262777389077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477356773878092068146075077 89504395102142262777389077)
                ·
                  refine ⟨4195518520412918567690113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89504395102142262777389077 4195518520412918567690113)
                  ·
                    refine ⟨3146638890309688925767585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195518520412918567690113 3146638890309688925767585)
                    ·
                      refine ⟨2359979167732266694325689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146638890309688925767585 2359979167732266694325689)
                      ·
                        rfl

theorem cell23_4596043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2, 2].length) (baseStart_4596043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596043 prefixEnd_4596043 := by exact prefixLift 4596043
  have htrace : WordTrace (prefixWord ++ tailWord_4596043) baseStart_4596043 baseEnd_4596043 := by
    simpa [prefixWord, tailWord_4596043, baseEnd_4596043] using wordTrace_append hprefix tailTrace_4596043
  have hstable : (prefixWord ++ tailWord_4596043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596043).length < 2 ^ (prefixWord ++ tailWord_4596043).sum := by decide
  have hdescent : baseEnd_4596043 < baseStart_4596043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596046 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_4596046 : Nat := 118140960795 + 4596046 * 2 ^ 59
def prefixEnd_4596046 : Nat := 4983230072969 + 3 ^ 40 * 4596046 * 2
def baseEnd_4596046 : Nat := 2359980708174230182588175

theorem tailTrace_4596046 : CollatzResearch.WordTrace tailWord_4596046 prefixEnd_4596046 2359980708174230182588175 := by
  unfold tailWord_4596046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20953946138414719876183999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111754379404878506006314661 20953946138414719876183999)
  ·
    refine ⟨31430919207622079814275999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20953946138414719876183999 31430919207622079814275999)
    ·
      refine ⟨47146378811433119721413999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31430919207622079814275999 47146378811433119721413999)
      ·
        refine ⟨70719568217149679582120999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47146378811433119721413999 70719568217149679582120999)
        ·
          refine ⟨106079352325724519373181499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70719568217149679582120999 106079352325724519373181499)
          ·
            refine ⟨159119028488586779059772249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106079352325724519373181499 159119028488586779059772249)
            ·
              refine ⟨119339271366440084294829187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159119028488586779059772249 119339271366440084294829187)
              ·
                refine ⟨179008907049660126442243781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119339271366440084294829187 179008907049660126442243781)
                ·
                  refine ⟨33564170071811273707920709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179008907049660126442243781 33564170071811273707920709)
                  ·
                    refine ⟨6293281888464613820235133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33564170071811273707920709 6293281888464613820235133)
                    ·
                      refine ⟨2359980708174230182588175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293281888464613820235133 2359980708174230182588175)
                      ·
                        rfl

theorem cell23_4596046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_4596046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596046 prefixEnd_4596046 := by exact prefixLift 4596046
  have htrace : WordTrace (prefixWord ++ tailWord_4596046) baseStart_4596046 baseEnd_4596046 := by
    simpa [prefixWord, tailWord_4596046, baseEnd_4596046] using wordTrace_append hprefix tailTrace_4596046
  have hstable : (prefixWord ++ tailWord_4596046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596046).length < 2 ^ (prefixWord ++ tailWord_4596046).sum := by decide
  have hdescent : baseEnd_4596046 < baseStart_4596046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596077 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4596077 : Nat := 118140960795 + 4596077 * 2 ^ 59
def prefixEnd_4596077 : Nat := 4983230072969 + 3 ^ 40 * 4596077 * 2
def baseEnd_4596077 : Nat := 2359996626074519561300533

theorem tailTrace_4596077 : CollatzResearch.WordTrace tailWord_4596077 prefixEnd_4596077 2359996626074519561300533 := by
  unfold tailWord_4596077
  simp only [CollatzResearch.WordTrace]
  refine ⟨167632699770205451303850485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111755133180136967535900323 167632699770205451303850485)
  ·
    refine ⟨15715565603456761059735983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167632699770205451303850485 15715565603456761059735983)
    ·
      refine ⟨23573348405185141589603975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15715565603456761059735983 23573348405185141589603975)
      ·
        refine ⟨35360022607777712384405963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23573348405185141589603975 35360022607777712384405963)
        ·
          refine ⟨53040033911666568576608945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35360022607777712384405963 53040033911666568576608945)
          ·
            refine ⟨39780025433749926432456709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53040033911666568576608945 39780025433749926432456709)
            ·
              refine ⟨7458754768828111206085633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39780025433749926432456709 7458754768828111206085633)
              ·
                refine ⟨5594066076621083404564225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7458754768828111206085633 5594066076621083404564225)
                ·
                  refine ⟨4195549557465812553423169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5594066076621083404564225 4195549557465812553423169)
                  ·
                    refine ⟨3146662168099359415067377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195549557465812553423169 3146662168099359415067377)
                    ·
                      refine ⟨2359996626074519561300533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146662168099359415067377 2359996626074519561300533)
                      ·
                        rfl

theorem cell23_4596077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4596077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596077 prefixEnd_4596077 := by exact prefixLift 4596077
  have htrace : WordTrace (prefixWord ++ tailWord_4596077) baseStart_4596077 baseEnd_4596077 := by
    simpa [prefixWord, tailWord_4596077, baseEnd_4596077] using wordTrace_append hprefix tailTrace_4596077
  have hstable : (prefixWord ++ tailWord_4596077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596077).length < 2 ^ (prefixWord ++ tailWord_4596077).sum := by decide
  have hdescent : baseEnd_4596077 < baseStart_4596077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596093 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_4596093 : Nat := 118140960795 + 4596093 * 2 ^ 59
def prefixEnd_4596093 : Nat := 4983230072969 + 3 ^ 40 * 4596093 * 2
def baseEnd_4596093 : Nat := 2360004841764991498700459

theorem tailTrace_4596093 : CollatzResearch.WordTrace tailWord_4596093 prefixEnd_4596093 2360004841764991498700459 := by
  unfold tailWord_4596093
  simp only [CollatzResearch.WordTrace]
  refine ⟨167633283338147486036432933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111755522225431657357621955 167633283338147486036432933)
  ·
    refine ⟨31431240625902653631831175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167633283338147486036432933 31431240625902653631831175)
    ·
      refine ⟨47146860938853980447746763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31431240625902653631831175 47146860938853980447746763)
      ·
        refine ⟨70720291408280970671620145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47146860938853980447746763 70720291408280970671620145)
        ·
          refine ⟨53040218556210728003715109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70720291408280970671620145 53040218556210728003715109)
          ·
            refine ⟨9945040979289511500696583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53040218556210728003715109 9945040979289511500696583)
            ·
              refine ⟨14917561468934267251044875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9945040979289511500696583 14917561468934267251044875)
              ·
                refine ⟨22376342203401400876567313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14917561468934267251044875 22376342203401400876567313)
                ·
                  refine ⟨16782256652551050657425485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22376342203401400876567313 16782256652551050657425485)
                  ·
                    refine ⟨6293346244706643996534557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16782256652551050657425485 6293346244706643996534557)
                    ·
                      refine ⟨2360004841764991498700459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293346244706643996534557 2360004841764991498700459)
                      ·
                        rfl

theorem cell23_4596093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_4596093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596093 prefixEnd_4596093 := by exact prefixLift 4596093
  have htrace : WordTrace (prefixWord ++ tailWord_4596093) baseStart_4596093 baseEnd_4596093 := by
    simpa [prefixWord, tailWord_4596093, baseEnd_4596093] using wordTrace_append hprefix tailTrace_4596093
  have hstable : (prefixWord ++ tailWord_4596093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596093).length < 2 ^ (prefixWord ++ tailWord_4596093).sum := by decide
  have hdescent : baseEnd_4596093 < baseStart_4596093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596103 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_4596103 : Nat := 118140960795 + 4596103 * 2 ^ 59
def prefixEnd_4596103 : Nat := 4983230072969 + 3 ^ 40 * 4596103 * 2
def baseEnd_4596103 : Nat := 2360009976571536459575413

theorem tailTrace_4596103 : CollatzResearch.WordTrace tailWord_4596103 prefixEnd_4596103 2360009976571536459575413 := by
  unfold tailWord_4596103
  simp only [CollatzResearch.WordTrace]
  refine ⟨167633648068111257744296963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111755765378740838496197975 167633648068111257744296963)
  ·
    refine ⟨251450472102166886616445445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167633648068111257744296963 251450472102166886616445445)
    ·
      refine ⟨47146963519156291240583521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251450472102166886616445445 47146963519156291240583521)
      ·
        refine ⟨35360222639367218430437641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47146963519156291240583521 35360222639367218430437641)
        ·
          refine ⟨26520166979525413822828231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35360222639367218430437641 26520166979525413822828231)
          ·
            refine ⟨39780250469288120734242347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26520166979525413822828231 39780250469288120734242347)
            ·
              refine ⟨59670375703932181101363521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39780250469288120734242347 59670375703932181101363521)
              ·
                refine ⟨44752781777949135826022641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59670375703932181101363521 44752781777949135826022641)
                ·
                  refine ⟨33564586333461851869516981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44752781777949135826022641 33564586333461851869516981)
                  ·
                    refine ⟨3146679968762048612767217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33564586333461851869516981 3146679968762048612767217)
                    ·
                      refine ⟨2360009976571536459575413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146679968762048612767217 2360009976571536459575413)
                      ·
                        rfl

theorem cell23_4596103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_4596103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596103 prefixEnd_4596103 := by exact prefixLift 4596103
  have htrace : WordTrace (prefixWord ++ tailWord_4596103) baseStart_4596103 baseEnd_4596103 := by
    simpa [prefixWord, tailWord_4596103, baseEnd_4596103] using wordTrace_append hprefix tailTrace_4596103
  have hstable : (prefixWord ++ tailWord_4596103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596103).length < 2 ^ (prefixWord ++ tailWord_4596103).sum := by decide
  have hdescent : baseEnd_4596103 < baseStart_4596103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596133 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_4596133 : Nat := 118140960795 + 4596133 * 2 ^ 59
def prefixEnd_4596133 : Nat := 4983230072969 + 3 ^ 40 * 4596133 * 2
def baseEnd_4596133 : Nat := 2360025380991171342200275

theorem tailTrace_4596133 : CollatzResearch.WordTrace tailWord_4596133 prefixEnd_4596133 2360025380991171342200275 := by
  unfold tailWord_4596133
  simp only [CollatzResearch.WordTrace]
  refine ⟨167634742258002572867889053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111756494838668381911926035 167634742258002572867889053)
  ·
    refine ⟨62863028346750964825458395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167634742258002572867889053 62863028346750964825458395)
    ·
      refine ⟨94294542520126447238187593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62863028346750964825458395 94294542520126447238187593)
      ·
        refine ⟨70720906890094835428640695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94294542520126447238187593 70720906890094835428640695)
        ·
          refine ⟨106081360335142253142961043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70720906890094835428640695 106081360335142253142961043)
          ·
            refine ⟨159122040502713379714441565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106081360335142253142961043 159122040502713379714441565)
            ·
              refine ⟨59670765188517517392915587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159122040502713379714441565 59670765188517517392915587)
              ·
                refine ⟨89506147782776276089373381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59670765188517517392915587 89506147782776276089373381)
                ·
                  refine ⟨16782402709270551766757509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89506147782776276089373381 16782402709270551766757509)
                  ·
                    refine ⟨3146700507988228456267033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16782402709270551766757509 3146700507988228456267033)
                    ·
                      refine ⟨2360025380991171342200275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146700507988228456267033 2360025380991171342200275)
                      ·
                        rfl

theorem cell23_4596133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_4596133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596133 prefixEnd_4596133 := by exact prefixLift 4596133
  have htrace : WordTrace (prefixWord ++ tailWord_4596133) baseStart_4596133 baseEnd_4596133 := by
    simpa [prefixWord, tailWord_4596133, baseEnd_4596133] using wordTrace_append hprefix tailTrace_4596133
  have hstable : (prefixWord ++ tailWord_4596133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596133).length < 2 ^ (prefixWord ++ tailWord_4596133).sum := by decide
  have hdescent : baseEnd_4596133 < baseStart_4596133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596146 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4596146 : Nat := 118140960795 + 4596146 * 2 ^ 59
def prefixEnd_4596146 : Nat := 4983230072969 + 3 ^ 40 * 4596146 * 2
def baseEnd_4596146 : Nat := 2360032056239679791337715

theorem tailTrace_4596146 : CollatzResearch.WordTrace tailWord_4596146 prefixEnd_4596146 2360032056239679791337715 := by
  unfold tailWord_4596146
  simp only [CollatzResearch.WordTrace]
  refine ⟨41908804101738869022028073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111756810937970317392074861 41908804101738869022028073)
  ·
    refine ⟨31431603076304151766521055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41908804101738869022028073 31431603076304151766521055)
    ·
      refine ⟨47147404614456227649781583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31431603076304151766521055 47147404614456227649781583)
      ·
        refine ⟨70721106921684341474672375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47147404614456227649781583 70721106921684341474672375)
        ·
          refine ⟨106081660382526512212008563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70721106921684341474672375 106081660382526512212008563)
          ·
            refine ⟨159122490573789768318012845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106081660382526512212008563 159122490573789768318012845)
            ·
              refine ⟨59670933965171163119254817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159122490573789768318012845 59670933965171163119254817)
              ·
                refine ⟨44753200473878372339441113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59670933965171163119254817 44753200473878372339441113)
                ·
                  refine ⟨33564900355408779254580835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44753200473878372339441113 33564900355408779254580835)
                  ·
                    refine ⟨50347350533113168881871253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33564900355408779254580835 50347350533113168881871253)
                    ·
                      refine ⟨2360032056239679791337715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50347350533113168881871253 2360032056239679791337715)
                      ·
                        rfl

theorem cell23_4596146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4596146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596146 prefixEnd_4596146 := by exact prefixLift 4596146
  have htrace : WordTrace (prefixWord ++ tailWord_4596146) baseStart_4596146 baseEnd_4596146 := by
    simpa [prefixWord, tailWord_4596146, baseEnd_4596146] using wordTrace_append hprefix tailTrace_4596146
  have hstable : (prefixWord ++ tailWord_4596146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596146).length < 2 ^ (prefixWord ++ tailWord_4596146).sum := by decide
  have hdescent : baseEnd_4596146 < baseStart_4596146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596153 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4596153 : Nat := 118140960795 + 4596153 * 2 ^ 59
def prefixEnd_4596153 : Nat := 4983230072969 + 3 ^ 40 * 4596153 * 2
def baseEnd_4596153 : Nat := 2360035650604261263950183

theorem tailTrace_4596153 : CollatzResearch.WordTrace tailWord_4596153 prefixEnd_4596153 2360035650604261263950183 := by
  unfold tailWord_4596153
  simp only [CollatzResearch.WordTrace]
  refine ⟨167635471717930116283617113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111756981145286744189078075 167635471717930116283617113)
  ·
    refine ⟨125726603788447587212712835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167635471717930116283617113 125726603788447587212712835)
    ·
      refine ⟨188589905682671380819069253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125726603788447587212712835 188589905682671380819069253)
      ·
        refine ⟨35360607315500883903575485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188589905682671380819069253 35360607315500883903575485)
        ·
          refine ⟨13260227743312831463840807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35360607315500883903575485 13260227743312831463840807)
          ·
            refine ⟨19890341614969247195761211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13260227743312831463840807 19890341614969247195761211)
            ·
              refine ⟨29835512422453870793641817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19890341614969247195761211 29835512422453870793641817)
              ·
                refine ⟨22376634316840403095231363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29835512422453870793641817 22376634316840403095231363)
                ·
                  refine ⟨33564951475260604642847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22376634316840403095231363 33564951475260604642847045)
                  ·
                    refine ⟨6293428401611363370533821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33564951475260604642847045 6293428401611363370533821)
                    ·
                      refine ⟨2360035650604261263950183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293428401611363370533821 2360035650604261263950183)
                      ·
                        rfl

theorem cell23_4596153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4596153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596153 prefixEnd_4596153 := by exact prefixLift 4596153
  have htrace : WordTrace (prefixWord ++ tailWord_4596153) baseStart_4596153 baseEnd_4596153 := by
    simpa [prefixWord, tailWord_4596153, baseEnd_4596153] using wordTrace_append hprefix tailTrace_4596153
  have hstable : (prefixWord ++ tailWord_4596153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596153).length < 2 ^ (prefixWord ++ tailWord_4596153).sum := by decide
  have hdescent : baseEnd_4596153 < baseStart_4596153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596196 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_4596196 : Nat := 118140960795 + 4596196 * 2 ^ 59
def prefixEnd_4596196 : Nat := 4983230072969 + 3 ^ 40 * 4596196 * 2
def baseEnd_4596196 : Nat := 2360057730272404595712485

theorem tailTrace_4596196 : CollatzResearch.WordTrace tailWord_4596196 prefixEnd_4596196 2360057730272404595712485 := by
  unfold tailWord_4596196
  simp only [CollatzResearch.WordTrace]
  refine ⟨83818520028387167313716221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111758026704516223084954961 83818520028387167313716221)
  ·
    refine ⟨31431945010645187742643583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83818520028387167313716221 31431945010645187742643583)
    ·
      refine ⟨47147917515967781613965375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31431945010645187742643583 47147917515967781613965375)
      ·
        refine ⟨70721876273951672420948063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47147917515967781613965375 70721876273951672420948063)
        ·
          refine ⟨106082814410927508631422095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70721876273951672420948063 106082814410927508631422095)
          ·
            refine ⟨159124221616391262947133143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106082814410927508631422095 159124221616391262947133143)
            ·
              refine ⟨238686332424586894420699715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159124221616391262947133143 238686332424586894420699715)
              ·
                refine ⟨358029498636880341631049573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238686332424586894420699715 358029498636880341631049573)
                ·
                  refine ⟨67130530994415064055821795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 358029498636880341631049573 67130530994415064055821795)
                  ·
                    refine ⟨100695796491622596083732693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67130530994415064055821795 100695796491622596083732693)
                    ·
                      refine ⟨2360057730272404595712485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100695796491622596083732693 2360057730272404595712485)
                      ·
                        rfl

theorem cell23_4596196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_4596196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596196 prefixEnd_4596196 := by exact prefixLift 4596196
  have htrace : WordTrace (prefixWord ++ tailWord_4596196) baseStart_4596196 baseEnd_4596196 := by
    simpa [prefixWord, tailWord_4596196, baseEnd_4596196] using wordTrace_append hprefix tailTrace_4596196
  have hstable : (prefixWord ++ tailWord_4596196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596196).length < 2 ^ (prefixWord ++ tailWord_4596196).sum := by decide
  have hdescent : baseEnd_4596196 < baseStart_4596196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596223 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_4596223 : Nat := 118140960795 + 4596223 * 2 ^ 59
def prefixEnd_4596223 : Nat := 4983230072969 + 3 ^ 40 * 4596223 * 2
def baseEnd_4596223 : Nat := 2360071594250075990074861

theorem tailTrace_4596223 : CollatzResearch.WordTrace tailWord_4596223 prefixEnd_4596223 2360071594250075990074861 := by
  unfold tailWord_4596223
  simp only [CollatzResearch.WordTrace]
  refine ⟨167638024827676518238665323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111758683218451012159110215 167638024827676518238665323)
  ·
    refine ⟨251457037241514777357997985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167638024827676518238665323 251457037241514777357997985)
    ·
      refine ⟨188592777931136083018498489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251457037241514777357997985 188592777931136083018498489)
      ·
        refine ⟨141444583448352062263873867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188592777931136083018498489 141444583448352062263873867)
        ·
          refine ⟨212166875172528093395810801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141444583448352062263873867 212166875172528093395810801)
          ·
            refine ⟨159125156379396070046858101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212166875172528093395810801 159125156379396070046858101)
            ·
              refine ⟨14917983410568381566892947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159125156379396070046858101 14917983410568381566892947)
              ·
                refine ⟨22376975115852572350339421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14917983410568381566892947 22376975115852572350339421)
                ·
                  refine ⟨8391365668444714631377283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22376975115852572350339421 8391365668444714631377283)
                  ·
                    refine ⟨12587048502667071947065925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8391365668444714631377283 12587048502667071947065925)
                    ·
                      refine ⟨2360071594250075990074861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12587048502667071947065925 2360071594250075990074861)
                      ·
                        rfl

theorem cell23_4596223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_4596223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596223 prefixEnd_4596223 := by exact prefixLift 4596223
  have htrace : WordTrace (prefixWord ++ tailWord_4596223) baseStart_4596223 baseEnd_4596223 := by
    simpa [prefixWord, tailWord_4596223, baseEnd_4596223] using wordTrace_append hprefix tailTrace_4596223
  have hstable : (prefixWord ++ tailWord_4596223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596223).length < 2 ^ (prefixWord ++ tailWord_4596223).sum := by decide
  have hdescent : baseEnd_4596223 < baseStart_4596223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596233 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_4596233 : Nat := 118140960795 + 4596233 * 2 ^ 59
def prefixEnd_4596233 : Nat := 4983230072969 + 3 ^ 40 * 4596233 * 2
def baseEnd_4596233 : Nat := 786692243018873650316605

theorem tailTrace_4596233 : CollatzResearch.WordTrace tailWord_4596233 prefixEnd_4596233 786692243018873650316605 := by
  unfold tailWord_4596233
  simp only [CollatzResearch.WordTrace]
  refine ⟨167638389557640289946529353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111758926371760193297686235 167638389557640289946529353)
  ·
    refine ⟨125728792168230217459897015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167638389557640289946529353 125728792168230217459897015)
    ·
      refine ⟨188593188252345326189845523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125728792168230217459897015 188593188252345326189845523)
      ·
        refine ⟨282889782378517989284768285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188593188252345326189845523 282889782378517989284768285)
        ·
          refine ⟨106083668391944245981788107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282889782378517989284768285 106083668391944245981788107)
          ·
            refine ⟨159125502587916368972682161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106083668391944245981788107 159125502587916368972682161)
            ·
              refine ⟨119344126940937276729511621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159125502587916368972682161 119344126940937276729511621)
              ·
                refine ⟨22377023801425739386783429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119344126940937276729511621 22377023801425739386783429)
                ·
                  refine ⟨4195691962767326135021893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22377023801425739386783429 4195691962767326135021893)
                  ·
                    refine ⟨786692243018873650316605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195691962767326135021893 786692243018873650316605)
                    ·
                      rfl

theorem cell23_4596233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_4596233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596233 prefixEnd_4596233 := by exact prefixLift 4596233
  have htrace : WordTrace (prefixWord ++ tailWord_4596233) baseStart_4596233 baseEnd_4596233 := by
    simpa [prefixWord, tailWord_4596233, baseEnd_4596233] using wordTrace_append hprefix tailTrace_4596233
  have hstable : (prefixWord ++ tailWord_4596233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596233).length < 2 ^ (prefixWord ++ tailWord_4596233).sum := by decide
  have hdescent : baseEnd_4596233 < baseStart_4596233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596244 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4596244 : Nat := 118140960795 + 4596244 * 2 ^ 59
def prefixEnd_4596244 : Nat := 4983230072969 + 3 ^ 40 * 4596244 * 2
def baseEnd_4596244 : Nat := 2360082377343820407912265

theorem tailTrace_4596244 : CollatzResearch.WordTrace tailWord_4596244 prefixEnd_4596244 2360082377343820407912265 := by
  unfold tailWord_4596244
  simp only [CollatzResearch.WordTrace]
  refine ⟨83819395380300219412589893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111759193840400292550119857 83819395380300219412589893)
  ·
    refine ⟨15716136633806291139860605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83819395380300219412589893 15716136633806291139860605)
    ·
      refine ⟨5893551237677359177447727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15716136633806291139860605 5893551237677359177447727)
      ·
        refine ⟨8840326856516038766171591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893551237677359177447727 8840326856516038766171591)
        ·
          refine ⟨13260490284774058149257387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8840326856516038766171591 13260490284774058149257387)
          ·
            refine ⟨19890735427161087223886081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13260490284774058149257387 19890735427161087223886081)
            ·
              refine ⟨14918051570370815417914561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19890735427161087223886081 14918051570370815417914561)
              ·
                refine ⟨11188538677778111563435921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14918051570370815417914561 11188538677778111563435921)
                ·
                  refine ⟨8391404008333583672576941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11188538677778111563435921 8391404008333583672576941)
                  ·
                    refine ⟨3146776503125093877216353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8391404008333583672576941 3146776503125093877216353)
                    ·
                      refine ⟨2360082377343820407912265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146776503125093877216353 2360082377343820407912265)
                      ·
                        rfl

theorem cell23_4596244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4596244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596244 prefixEnd_4596244 := by exact prefixLift 4596244
  have htrace : WordTrace (prefixWord ++ tailWord_4596244) baseStart_4596244 baseEnd_4596244 := by
    simpa [prefixWord, tailWord_4596244, baseEnd_4596244] using wordTrace_append hprefix tailTrace_4596244
  have hstable : (prefixWord ++ tailWord_4596244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596244).length < 2 ^ (prefixWord ++ tailWord_4596244).sum := by decide
  have hdescent : baseEnd_4596244 < baseStart_4596244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596250 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_4596250 : Nat := 118140960795 + 4596250 * 2 ^ 59
def prefixEnd_4596250 : Nat := 4983230072969 + 3 ^ 40 * 4596250 * 2
def baseEnd_4596250 : Nat := 786695152742582461479079

theorem tailTrace_4596250 : CollatzResearch.WordTrace tailWord_4596250 prefixEnd_4596250 786695152742582461479079 := by
  unfold tailWord_4596250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41909752399644675462474551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111759339732385801233265469 41909752399644675462474551)
  ·
    refine ⟨62864628599467013193711827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41909752399644675462474551 62864628599467013193711827)
    ·
      refine ⟨94296942899200519790567741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62864628599467013193711827 94296942899200519790567741)
      ·
        refine ⟨35361353587200194921462903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94296942899200519790567741 35361353587200194921462903)
        ·
          refine ⟨53042030380800292382194355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35361353587200194921462903 53042030380800292382194355)
          ·
            refine ⟨79563045571200438573291533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53042030380800292382194355 79563045571200438573291533)
            ·
              refine ⟨29836142089200164464984325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79563045571200438573291533 29836142089200164464984325)
              ·
                refine ⟨5594276641725030837184561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29836142089200164464984325 5594276641725030837184561)
                ·
                  refine ⟨4195707481293773127888421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5594276641725030837184561 4195707481293773127888421)
                  ·
                    refine ⟨786695152742582461479079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195707481293773127888421 786695152742582461479079)
                    ·
                      rfl

theorem cell23_4596250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_4596250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596250 prefixEnd_4596250 := by exact prefixLift 4596250
  have htrace : WordTrace (prefixWord ++ tailWord_4596250) baseStart_4596250 baseEnd_4596250 := by
    simpa [prefixWord, tailWord_4596250, baseEnd_4596250] using wordTrace_append hprefix tailTrace_4596250
  have hstable : (prefixWord ++ tailWord_4596250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596250).length < 2 ^ (prefixWord ++ tailWord_4596250).sum := by decide
  have hdescent : baseEnd_4596250 < baseStart_4596250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596257 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_4596257 : Nat := 118140960795 + 4596257 * 2 ^ 59
def prefixEnd_4596257 : Nat := 4983230072969 + 3 ^ 40 * 4596257 * 2
def baseEnd_4596257 : Nat := 2360089052592328857049705

theorem tailTrace_4596257 : CollatzResearch.WordTrace tailWord_4596257 prefixEnd_4596257 2360089052592328857049705 := by
  unfold tailWord_4596257
  simp only [CollatzResearch.WordTrace]
  refine ⟨167639264909553342045403025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111759509939702228030268683 167639264909553342045403025)
  ·
    refine ⟨125729448682165006534052269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167639264909553342045403025 125729448682165006534052269)
    ·
      refine ⟨47148543255811877450269601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125729448682165006534052269 47148543255811877450269601)
      ·
        refine ⟨35361407441858908087702201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47148543255811877450269601 35361407441858908087702201)
        ·
          refine ⟨26521055581394181065776651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35361407441858908087702201 26521055581394181065776651)
          ·
            refine ⟨39781583372091271598664977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26521055581394181065776651 39781583372091271598664977)
            ·
              refine ⟨29836187529068453698998733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39781583372091271598664977 29836187529068453698998733)
              ·
                refine ⟨11188570323400670137124525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29836187529068453698998733 11188570323400670137124525)
                ·
                  refine ⟨4195713871275251301421697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11188570323400670137124525 4195713871275251301421697)
                  ·
                    refine ⟨3146785403456438476066273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195713871275251301421697 3146785403456438476066273)
                    ·
                      refine ⟨2360089052592328857049705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146785403456438476066273 2360089052592328857049705)
                      ·
                        rfl

theorem cell23_4596257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_4596257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596257 prefixEnd_4596257 := by exact prefixLift 4596257
  have htrace : WordTrace (prefixWord ++ tailWord_4596257) baseStart_4596257 baseEnd_4596257 := by
    simpa [prefixWord, tailWord_4596257, baseEnd_4596257] using wordTrace_append hprefix tailTrace_4596257
  have hstable : (prefixWord ++ tailWord_4596257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596257).length < 2 ^ (prefixWord ++ tailWord_4596257).sum := by decide
  have hdescent : baseEnd_4596257 < baseStart_4596257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596318 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_4596318 : Nat := 118140960795 + 4596318 * 2 ^ 59
def prefixEnd_4596318 : Nat := 4983230072969 + 3 ^ 40 * 4596318 * 2
def baseEnd_4596318 : Nat := 786706791637417706128975

theorem tailTrace_4596318 : CollatzResearch.WordTrace tailWord_4596318 prefixEnd_4596318 786706791637417706128975 := by
  unfold tailWord_4596318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20955186220291543682921701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111760993174888232975582405 20955186220291543682921701)
  ·
    refine ⟨3929097416304664440547819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20955186220291543682921701 3929097416304664440547819)
    ·
      refine ⟨5893646124456996660821729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929097416304664440547819 5893646124456996660821729)
      ·
        refine ⟨4420234593342747495616297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5893646124456996660821729 4420234593342747495616297)
        ·
          refine ⟨3315175945007060621712223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4420234593342747495616297 3315175945007060621712223)
          ·
            refine ⟨4972763917510590932568335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315175945007060621712223 4972763917510590932568335)
            ·
              refine ⟨7459145876265886398852503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972763917510590932568335 7459145876265886398852503)
              ·
                refine ⟨11188718814398829598278755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459145876265886398852503 11188718814398829598278755)
                ·
                  refine ⟨16783078221598244397418133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11188718814398829598278755 16783078221598244397418133)
                  ·
                    refine ⟨786706791637417706128975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16783078221598244397418133 786706791637417706128975)
                    ·
                      rfl

theorem cell23_4596318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_4596318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596318 prefixEnd_4596318 := by exact prefixLift 4596318
  have htrace : WordTrace (prefixWord ++ tailWord_4596318) baseStart_4596318 baseEnd_4596318 := by
    simpa [prefixWord, tailWord_4596318, baseEnd_4596318] using wordTrace_append hprefix tailTrace_4596318
  have hstable : (prefixWord ++ tailWord_4596318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596318).length < 2 ^ (prefixWord ++ tailWord_4596318).sum := by decide
  have hdescent : baseEnd_4596318 < baseStart_4596318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596323 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 2, 6]
def baseStart_4596323 : Nat := 118140960795 + 4596323 * 2 ^ 59
def prefixEnd_4596323 : Nat := 4983230072969 + 3 ^ 40 * 4596323 * 2
def baseEnd_4596323 : Nat := 786707647438508532941467

theorem tailTrace_4596323 : CollatzResearch.WordTrace tailWord_4596323 prefixEnd_4596323 786707647438508532941467 := by
  unfold tailWord_4596323
  simp only [CollatzResearch.WordTrace]
  refine ⟨167641672127314235317305623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111761114751542823544870415 167641672127314235317305623)
  ·
    refine ⟨251462508190971352975958435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167641672127314235317305623 251462508190971352975958435)
    ·
      refine ⟨377193762286457029463937653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251462508190971352975958435 377193762286457029463937653)
      ·
        refine ⟨35361915214355346512244155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 377193762286457029463937653 35361915214355346512244155)
        ·
          refine ⟨53042872821533019768366233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35361915214355346512244155 53042872821533019768366233)
          ·
            refine ⟨39782154616149764826274675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53042872821533019768366233 39782154616149764826274675)
            ·
              refine ⟨59673231924224647239412013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39782154616149764826274675 59673231924224647239412013)
              ·
                refine ⟨22377461971584242714779505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59673231924224647239412013 22377461971584242714779505)
                ·
                  refine ⟨16783096478688182036084629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22377461971584242714779505 16783096478688182036084629)
                  ·
                    refine ⟨786707647438508532941467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16783096478688182036084629 786707647438508532941467)
                    ·
                      rfl

theorem cell23_4596323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_4596323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596323 prefixEnd_4596323 := by exact prefixLift 4596323
  have htrace : WordTrace (prefixWord ++ tailWord_4596323) baseStart_4596323 baseEnd_4596323 := by
    simpa [prefixWord, tailWord_4596323, baseEnd_4596323] using wordTrace_append hprefix tailTrace_4596323
  have hstable : (prefixWord ++ tailWord_4596323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596323).length < 2 ^ (prefixWord ++ tailWord_4596323).sum := by decide
  have hdescent : baseEnd_4596323 < baseStart_4596323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596324 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 2, 1, 3]
def baseStart_4596324 : Nat := 118140960795 + 4596324 * 2 ^ 59
def prefixEnd_4596324 : Nat := 4983230072969 + 3 ^ 40 * 4596324 * 2
def baseEnd_4596324 : Nat := 2360123455796180094911897

theorem tailTrace_4596324 : CollatzResearch.WordTrace tailWord_4596324 prefixEnd_4596324 2360123455796180094911897 := by
  unfold tailWord_4596324
  simp only [CollatzResearch.WordTrace]
  refine ⟨83820854300155306244046013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111761139066873741658728017 83820854300155306244046013)
  ·
    refine ⟨31432820362558239841517255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83820854300155306244046013 31432820362558239841517255)
    ·
      refine ⟨47149230543837359762275883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31432820362558239841517255 47149230543837359762275883)
      ·
        refine ⟨70723845815756039643413825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47149230543837359762275883 70723845815756039643413825)
        ·
          refine ⟨53042884361817029732560369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70723845815756039643413825 53042884361817029732560369)
          ·
            refine ⟨39782163271362772299420277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53042884361817029732560369 39782163271362772299420277)
            ·
              refine ⟨3729577806690259903070651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39782163271362772299420277 3729577806690259903070651)
              ·
                refine ⟨5594366710035389854605977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729577806690259903070651 5594366710035389854605977)
                ·
                  refine ⟨4195775032526542390954483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5594366710035389854605977 4195775032526542390954483)
                  ·
                    refine ⟨6293662548789813586431725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4195775032526542390954483 6293662548789813586431725)
                    ·
                      refine ⟨2360123455796180094911897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293662548789813586431725 2360123455796180094911897)
                      ·
                        rfl

theorem cell23_4596324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_4596324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596324 prefixEnd_4596324 := by exact prefixLift 4596324
  have htrace : WordTrace (prefixWord ++ tailWord_4596324) baseStart_4596324 baseEnd_4596324 := by
    simpa [prefixWord, tailWord_4596324, baseEnd_4596324] using wordTrace_append hprefix tailTrace_4596324
  have hstable : (prefixWord ++ tailWord_4596324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596324).length < 2 ^ (prefixWord ++ tailWord_4596324).sum := by decide
  have hdescent : baseEnd_4596324 < baseStart_4596324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596334 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4596334 : Nat := 118140960795 + 4596334 * 2 ^ 59
def prefixEnd_4596334 : Nat := 4983230072969 + 3 ^ 40 * 4596334 * 2
def baseEnd_4596334 : Nat := 2360128590602725055786851

theorem tailTrace_4596334 : CollatzResearch.WordTrace tailWord_4596334 prefixEnd_4596334 2360128590602725055786851 := by
  unfold tailWord_4596334
  simp only [CollatzResearch.WordTrace]
  refine ⟨20955259166284298024494507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111761382220182922797304037 20955259166284298024494507)
  ·
    refine ⟨31432888749426447036741761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20955259166284298024494507 31432888749426447036741761)
    ·
      refine ⟨23574666562069835277556321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31432888749426447036741761 23574666562069835277556321)
      ·
        refine ⟨17680999921552376458167241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23574666562069835277556321 17680999921552376458167241)
        ·
          refine ⟨13260749941164282343625431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17680999921552376458167241 13260749941164282343625431)
          ·
            refine ⟨19891124911746423515438147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13260749941164282343625431 19891124911746423515438147)
            ·
              refine ⟨29836687367619635273157221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19891124911746423515438147 29836687367619635273157221)
              ·
                refine ⟨5594378881428681613716979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29836687367619635273157221 5594378881428681613716979)
                ·
                  refine ⟨8391568322143022420575469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5594378881428681613716979 8391568322143022420575469)
                  ·
                    refine ⟨3146838120803633407715801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8391568322143022420575469 3146838120803633407715801)
                    ·
                      refine ⟨2360128590602725055786851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146838120803633407715801 2360128590602725055786851)
                      ·
                        rfl

theorem cell23_4596334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4596334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596334 prefixEnd_4596334 := by exact prefixLift 4596334
  have htrace : WordTrace (prefixWord ++ tailWord_4596334) baseStart_4596334 baseEnd_4596334 := by
    simpa [prefixWord, tailWord_4596334, baseEnd_4596334] using wordTrace_append hprefix tailTrace_4596334
  have hstable : (prefixWord ++ tailWord_4596334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596334).length < 2 ^ (prefixWord ++ tailWord_4596334).sum := by decide
  have hdescent : baseEnd_4596334 < baseStart_4596334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596343 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_4596343 : Nat := 118140960795 + 4596343 * 2 ^ 59
def prefixEnd_4596343 : Nat := 4983230072969 + 3 ^ 40 * 4596343 * 2
def baseEnd_4596343 : Nat := 2360133211928615520574309

theorem tailTrace_4596343 : CollatzResearch.WordTrace tailWord_4596343 prefixEnd_4596343 2360133211928615520574309 := by
  unfold tailWord_4596343
  simp only [CollatzResearch.WordTrace]
  refine ⟨167642401587241778733033683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111761601058161185822022455 167642401587241778733033683)
  ·
    refine ⟨251463602380862668099550525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167642401587241778733033683 251463602380862668099550525)
    ·
      refine ⟨94298850892823500537331447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251463602380862668099550525 94298850892823500537331447)
      ·
        refine ⟨141448276339235250805997171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94298850892823500537331447 141448276339235250805997171)
        ·
          refine ⟨212172414508852876208995757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141448276339235250805997171 212172414508852876208995757)
          ·
            refine ⟨79564655440819828578373409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212172414508852876208995757 79564655440819828578373409)
            ·
              refine ⟨59673491580614871433780057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79564655440819828578373409 59673491580614871433780057)
              ·
                refine ⟨44755118685461153575335043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59673491580614871433780057 44755118685461153575335043)
                ·
                  refine ⟨67132678028191730363002565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44755118685461153575335043 67132678028191730363002565)
                  ·
                    refine ⟨12587377130285949443062981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67132678028191730363002565 12587377130285949443062981)
                    ·
                      refine ⟨2360133211928615520574309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12587377130285949443062981 2360133211928615520574309)
                      ·
                        rfl

theorem cell23_4596343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_4596343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596343 prefixEnd_4596343 := by exact prefixLift 4596343
  have htrace : WordTrace (prefixWord ++ tailWord_4596343) baseStart_4596343 baseEnd_4596343 := by
    simpa [prefixWord, tailWord_4596343, baseEnd_4596343] using wordTrace_append hprefix tailTrace_4596343
  have hstable : (prefixWord ++ tailWord_4596343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596343).length < 2 ^ (prefixWord ++ tailWord_4596343).sum := by decide
  have hdescent : baseEnd_4596343 < baseStart_4596343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596381 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_4596381 : Nat := 118140960795 + 4596381 * 2 ^ 59
def prefixEnd_4596381 : Nat := 4983230072969 + 3 ^ 40 * 4596381 * 2
def baseEnd_4596381 : Nat := 2360152724193486371899135

theorem tailTrace_4596381 : CollatzResearch.WordTrace tailWord_4596381 prefixEnd_4596381 2360152724193486371899135 := by
  unfold tailWord_4596381
  simp only [CollatzResearch.WordTrace]
  refine ⟨167643787561104111222916997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111762525040736074148611331 167643787561104111222916997)
  ·
    refine ⟨31433210167707020854296937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167643787561104111222916997 31433210167707020854296937)
    ·
      refine ⟨23574907625780265640722703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31433210167707020854296937 23574907625780265640722703)
      ·
        refine ⟨35362361438670398461084055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23574907625780265640722703 35362361438670398461084055)
        ·
          refine ⟨53043542158005597691626083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35362361438670398461084055 53043542158005597691626083)
          ·
            refine ⟨79565313237008396537439125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53043542158005597691626083 79565313237008396537439125)
            ·
              refine ⟨3729624057984768587692459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79565313237008396537439125 3729624057984768587692459)
              ·
                refine ⟨5594436086977152881538689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729624057984768587692459 5594436086977152881538689)
                ·
                  refine ⟨4195827065232864661154017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5594436086977152881538689 4195827065232864661154017)
                  ·
                    refine ⟨3146870298924648495865513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195827065232864661154017 3146870298924648495865513)
                    ·
                      refine ⟨2360152724193486371899135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146870298924648495865513 2360152724193486371899135)
                      ·
                        rfl

theorem cell23_4596381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_4596381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596381 prefixEnd_4596381 := by exact prefixLift 4596381
  have htrace : WordTrace (prefixWord ++ tailWord_4596381) baseStart_4596381 baseEnd_4596381 := by
    simpa [prefixWord, tailWord_4596381, baseEnd_4596381] using wordTrace_append hprefix tailTrace_4596381
  have hstable : (prefixWord ++ tailWord_4596381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596381).length < 2 ^ (prefixWord ++ tailWord_4596381).sum := by decide
  have hdescent : baseEnd_4596381 < baseStart_4596381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596393 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_4596393 : Nat := 118140960795 + 4596393 * 2 ^ 59
def prefixEnd_4596393 : Nat := 4983230072969 + 3 ^ 40 * 4596393 * 2
def baseEnd_4596393 : Nat := 2360158885961340324949079

theorem tailTrace_4596393 : CollatzResearch.WordTrace tailWord_4596393 prefixEnd_4596393 2360158885961340324949079 := by
  unfold tailWord_4596393
  simp only [CollatzResearch.WordTrace]
  refine ⟨167644225237060637272353833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111762816824707091514902555 167644225237060637272353833)
  ·
    refine ⟨125733168927795477954265375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167644225237060637272353833 125733168927795477954265375)
    ·
      refine ⟨188599753391693216931398063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125733168927795477954265375 188599753391693216931398063)
      ·
        refine ⟨282899630087539825397097095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188599753391693216931398063 282899630087539825397097095)
        ·
          refine ⟨424349445131309738095645643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282899630087539825397097095 424349445131309738095645643)
          ·
            refine ⟨636524167696964607143468465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424349445131309738095645643 636524167696964607143468465)
            ·
              refine ⟨477393125772723455357601349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636524167696964607143468465 477393125772723455357601349)
              ·
                refine ⟨89511211082385647879550253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477393125772723455357601349 89511211082385647879550253)
                ·
                  refine ⟨33566704155894617954831345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89511211082385647879550253 33566704155894617954831345)
                  ·
                    refine ⟨25175028116920963466123509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33566704155894617954831345 25175028116920963466123509)
                    ·
                      refine ⟨2360158885961340324949079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25175028116920963466123509 2360158885961340324949079)
                      ·
                        rfl

theorem cell23_4596393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_4596393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596393 prefixEnd_4596393 := by exact prefixLift 4596393
  have htrace : WordTrace (prefixWord ++ tailWord_4596393) baseStart_4596393 baseEnd_4596393 := by
    simpa [prefixWord, tailWord_4596393, baseEnd_4596393] using wordTrace_append hprefix tailTrace_4596393
  have hstable : (prefixWord ++ tailWord_4596393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596393).length < 2 ^ (prefixWord ++ tailWord_4596393).sum := by decide
  have hdescent : baseEnd_4596393 < baseStart_4596393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596447 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 3, 4]
def baseStart_4596447 : Nat := 118140960795 + 4596447 * 2 ^ 59
def prefixEnd_4596447 : Nat := 4983230072969 + 3 ^ 40 * 4596447 * 2
def baseEnd_4596447 : Nat := 786728871305561037891277

theorem tailTrace_4596447 : CollatzResearch.WordTrace tailWord_4596447 prefixEnd_4596447 786728871305561037891277 := by
  unfold tailWord_4596447
  simp only [CollatzResearch.WordTrace]
  refine ⟨167646194778865004494819595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111764129852576669663213063 167646194778865004494819595)
  ·
    refine ⟨251469292168297506742229393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167646194778865004494819595 251469292168297506742229393)
    ·
      refine ⟨188601969126223130056672045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251469292168297506742229393 188601969126223130056672045)
      ·
        refine ⟨70725738422333673771252017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188601969126223130056672045 70725738422333673771252017)
        ·
          refine ⟨53044303816750255328439013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70725738422333673771252017 53044303816750255328439013)
          ·
            refine ⟨9945806965640672874082315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53044303816750255328439013 9945806965640672874082315)
            ·
              refine ⟨14918710448461009311123473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9945806965640672874082315 14918710448461009311123473)
              ·
                refine ⟨11189032836345756983342605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14918710448461009311123473 11189032836345756983342605)
                ·
                  refine ⟨4195887313629658868753477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11189032836345756983342605 4195887313629658868753477)
                  ·
                    refine ⟨786728871305561037891277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195887313629658868753477 786728871305561037891277)
                    ·
                      rfl

theorem cell23_4596447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_4596447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596447 prefixEnd_4596447 := by exact prefixLift 4596447
  have htrace : WordTrace (prefixWord ++ tailWord_4596447) baseStart_4596447 baseEnd_4596447 := by
    simpa [prefixWord, tailWord_4596447, baseEnd_4596447] using wordTrace_append hprefix tailTrace_4596447
  have hstable : (prefixWord ++ tailWord_4596447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596447).length < 2 ^ (prefixWord ++ tailWord_4596447).sum := by decide
  have hdescent : baseEnd_4596447 < baseStart_4596447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596457 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_4596457 : Nat := 118140960795 + 4596457 * 2 ^ 59
def prefixEnd_4596457 : Nat := 4983230072969 + 3 ^ 40 * 4596457 * 2
def baseEnd_4596457 : Nat := 2360191748723228074548785

theorem tailTrace_4596457 : CollatzResearch.WordTrace tailWord_4596457 prefixEnd_4596457 2360191748723228074548785 := by
  unfold tailWord_4596457
  simp only [CollatzResearch.WordTrace]
  refine ⟨167646559508828776202683625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111764373005885850801789083 167646559508828776202683625)
  ·
    refine ⟨125734919631621582152012719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167646559508828776202683625 125734919631621582152012719)
    ·
      refine ⟨188602379447432373228019079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125734919631621582152012719 188602379447432373228019079)
      ·
        refine ⟨282903569171148559842028619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188602379447432373228019079 282903569171148559842028619)
        ·
          refine ⟨424355353756722839763042929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282903569171148559842028619 424355353756722839763042929)
          ·
            refine ⟨318266515317542129822282197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424355353756722839763042929 318266515317542129822282197)
            ·
              refine ⟨7459371452754893667709739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 318266515317542129822282197 7459371452754893667709739)
              ·
                refine ⟨11189057179132340501564609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459371452754893667709739 11189057179132340501564609)
                ·
                  refine ⟨8391792884349255376173457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11189057179132340501564609 8391792884349255376173457)
                  ·
                    refine ⟨6293844663261941532130093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8391792884349255376173457 6293844663261941532130093)
                    ·
                      refine ⟨2360191748723228074548785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293844663261941532130093 2360191748723228074548785)
                      ·
                        rfl

theorem cell23_4596457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_4596457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596457 prefixEnd_4596457 := by exact prefixLift 4596457
  have htrace : WordTrace (prefixWord ++ tailWord_4596457) baseStart_4596457 baseEnd_4596457 := by
    simpa [prefixWord, tailWord_4596457, baseEnd_4596457] using wordTrace_append hprefix tailTrace_4596457
  have hstable : (prefixWord ++ tailWord_4596457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596457).length < 2 ^ (prefixWord ++ tailWord_4596457).sum := by decide
  have hdescent : baseEnd_4596457 < baseStart_4596457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596464 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 1, 4]
def baseStart_4596464 : Nat := 118140960795 + 4596464 * 2 ^ 59
def prefixEnd_4596464 : Nat := 4983230072969 + 3 ^ 40 * 4596464 * 2
def baseEnd_4596464 : Nat := 786731781029269849053751

theorem tailTrace_4596464 : CollatzResearch.WordTrace tailWord_4596464 prefixEnd_4596464 786731781029269849053751 := by
  unfold tailWord_4596464
  simp only [CollatzResearch.WordTrace]
  refine ⟨83823407409901708199094223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111764543213202277598792297 83823407409901708199094223)
  ·
    refine ⟨125735111114852562298641335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83823407409901708199094223 125735111114852562298641335)
    ·
      refine ⟨188602666672278843447962003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125735111114852562298641335 188602666672278843447962003)
      ·
        refine ⟨282904000008418265171943005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188602666672278843447962003 282904000008418265171943005)
        ·
          refine ⟨106089000003156849439478627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282904000008418265171943005 106089000003156849439478627)
          ·
            refine ⟨159133500004735274159217941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106089000003156849439478627 159133500004735274159217941)
            ·
              refine ⟨7459382812721965976213341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159133500004735274159217941 7459382812721965976213341)
              ·
                refine ⟨2797268554770737241080003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7459382812721965976213341 2797268554770737241080003)
                ·
                  refine ⟨4195902832156105861620005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797268554770737241080003 4195902832156105861620005)
                  ·
                    refine ⟨786731781029269849053751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4195902832156105861620005 786731781029269849053751)
                    ·
                      rfl

theorem cell23_4596464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 4].length) (baseStart_4596464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596464 prefixEnd_4596464 := by exact prefixLift 4596464
  have htrace : WordTrace (prefixWord ++ tailWord_4596464) baseStart_4596464 baseEnd_4596464 := by
    simpa [prefixWord, tailWord_4596464, baseEnd_4596464] using wordTrace_append hprefix tailTrace_4596464
  have hstable : (prefixWord ++ tailWord_4596464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596464).length < 2 ^ (prefixWord ++ tailWord_4596464).sum := by decide
  have hdescent : baseEnd_4596464 < baseStart_4596464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596497 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_4596497 : Nat := 118140960795 + 4596497 * 2 ^ 59
def prefixEnd_4596497 : Nat := 4983230072969 + 3 ^ 40 * 4596497 * 2
def baseEnd_4596497 : Nat := 2360212287949407918048601

theorem tailTrace_4596497 : CollatzResearch.WordTrace tailWord_4596497 prefixEnd_4596497 2360212287949407918048601 := by
  unfold tailWord_4596497
  simp only [CollatzResearch.WordTrace]
  refine ⟨167648018428683863034139745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111765345619122575356093163 167648018428683863034139745)
  ·
    refine ⟨125736013821512897275604809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167648018428683863034139745 125736013821512897275604809)
    ·
      refine ⟨94302010366134672956703607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125736013821512897275604809 94302010366134672956703607)
      ·
        refine ⟨141453015549202009435055411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94302010366134672956703607 141453015549202009435055411)
        ·
          refine ⟨212179523323803014152583117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141453015549202009435055411 212179523323803014152583117)
          ·
            refine ⟨79567321246426130307218669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212179523323803014152583117 79567321246426130307218669)
            ·
              refine ⟨29837745467409798865207001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79567321246426130307218669 29837745467409798865207001)
              ·
                refine ⟨22378309100557349148905251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29837745467409798865207001 22378309100557349148905251)
                ·
                  refine ⟨33567463650836023723357877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22378309100557349148905251 33567463650836023723357877)
                  ·
                    refine ⟨3146949717265877224064801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33567463650836023723357877 3146949717265877224064801)
                    ·
                      refine ⟨2360212287949407918048601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146949717265877224064801 2360212287949407918048601)
                      ·
                        rfl

theorem cell23_4596497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_4596497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596497 prefixEnd_4596497 := by exact prefixLift 4596497
  have htrace : WordTrace (prefixWord ++ tailWord_4596497) baseStart_4596497 baseEnd_4596497 := by
    simpa [prefixWord, tailWord_4596497, baseEnd_4596497] using wordTrace_append hprefix tailTrace_4596497
  have hstable : (prefixWord ++ tailWord_4596497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596497).length < 2 ^ (prefixWord ++ tailWord_4596497).sum := by decide
  have hdescent : baseEnd_4596497 < baseStart_4596497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596514 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_4596514 : Nat := 118140960795 + 4596514 * 2 ^ 59
def prefixEnd_4596514 : Nat := 4983230072969 + 3 ^ 40 * 4596514 * 2
def baseEnd_4596514 : Nat := 2360221017120534351536023

theorem tailTrace_4596514 : CollatzResearch.WordTrace tailWord_4596514 prefixEnd_4596514 2360221017120534351536023 := by
  unfold tailWord_4596514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912159617405568734377149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111765758979748183291672397 41912159617405568734377149)
  ·
    refine ⟨15717059856527088275391431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41912159617405568734377149 15717059856527088275391431)
    ·
      refine ⟨23575589784790632413087147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15717059856527088275391431 23575589784790632413087147)
      ·
        refine ⟨35363384677185948619630721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23575589784790632413087147 35363384677185948619630721)
        ·
          refine ⟨26522538507889461464723041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35363384677185948619630721 26522538507889461464723041)
          ·
            refine ⟨19891903880917096098542281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26522538507889461464723041 19891903880917096098542281)
            ·
              refine ⟨14918927910687822073906711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19891903880917096098542281 14918927910687822073906711)
              ·
                refine ⟨22378391866031733110860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14918927910687822073906711 22378391866031733110860067)
                ·
                  refine ⟨33567587799047599666290101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22378391866031733110860067 33567587799047599666290101)
                  ·
                    refine ⟨3146961356160712468714697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33567587799047599666290101 3146961356160712468714697)
                    ·
                      refine ⟨2360221017120534351536023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3146961356160712468714697 2360221017120534351536023)
                      ·
                        rfl

theorem cell23_4596514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_4596514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596514 prefixEnd_4596514 := by exact prefixLift 4596514
  have htrace : WordTrace (prefixWord ++ tailWord_4596514) baseStart_4596514 baseEnd_4596514 := by
    simpa [prefixWord, tailWord_4596514, baseEnd_4596514] using wordTrace_append hprefix tailTrace_4596514
  have hstable : (prefixWord ++ tailWord_4596514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596514).length < 2 ^ (prefixWord ++ tailWord_4596514).sum := by decide
  have hdescent : baseEnd_4596514 < baseStart_4596514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596538 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_4596538 : Nat := 118140960795 + 4596538 * 2 ^ 59
def prefixEnd_4596538 : Nat := 4983230072969 + 3 ^ 40 * 4596538 * 2
def baseEnd_4596538 : Nat := 2360233340656242257635913

theorem tailTrace_4596538 : CollatzResearch.WordTrace tailWord_4596538 prefixEnd_4596538 2360233340656242257635913 := by
  unfold tailWord_4596538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912378455383831759095567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111766342547690218024254845 41912378455383831759095567)
  ·
    refine ⟨62868567683075747638643351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41912378455383831759095567 62868567683075747638643351)
    ·
      refine ⟨94302851524613621457965027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62868567683075747638643351 94302851524613621457965027)
      ·
        refine ⟨141454277286920432186947541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94302851524613621457965027 141454277286920432186947541)
        ·
          refine ⟨3315334623912197629381583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141454277286920432186947541 3315334623912197629381583)
          ·
            refine ⟨4973001935868296444072375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315334623912197629381583 4973001935868296444072375)
            ·
              refine ⟨7459502903802444666108563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973001935868296444072375 7459502903802444666108563)
              ·
                refine ⟨11189254355703666999162845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459502903802444666108563 11189254355703666999162845)
                ·
                  refine ⟨4195970383388875124686067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11189254355703666999162845 4195970383388875124686067)
                  ·
                    refine ⟨6293955575083312687029101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4195970383388875124686067 6293955575083312687029101)
                    ·
                      refine ⟨2360233340656242257635913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293955575083312687029101 2360233340656242257635913)
                      ·
                        rfl

theorem cell23_4596538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_4596538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596538 prefixEnd_4596538 := by exact prefixLift 4596538
  have htrace : WordTrace (prefixWord ++ tailWord_4596538) baseStart_4596538 baseEnd_4596538 := by
    simpa [prefixWord, tailWord_4596538, baseEnd_4596538] using wordTrace_append hprefix tailTrace_4596538
  have hstable : (prefixWord ++ tailWord_4596538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596538).length < 2 ^ (prefixWord ++ tailWord_4596538).sum := by decide
  have hdescent : baseEnd_4596538 < baseStart_4596538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596547 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3]
def baseStart_4596547 : Nat := 118140960795 + 4596547 * 2 ^ 59
def prefixEnd_4596547 : Nat := 4983230072969 + 3 ^ 40 * 4596547 * 2
def baseEnd_4596547 : Nat := 2360237961982132722423371

theorem tailTrace_4596547 : CollatzResearch.WordTrace tailWord_4596547 prefixEnd_4596547 2360237961982132722423371 := by
  unfold tailWord_4596547
  simp only [CollatzResearch.WordTrace]
  refine ⟨167649842078502721573459895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111766561385668481048973263 167649842078502721573459895)
  ·
    refine ⟨251474763117754082360189843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167649842078502721573459895 251474763117754082360189843)
    ·
      refine ⟨377212144676631123540284765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251474763117754082360189843 377212144676631123540284765)
      ·
        refine ⟨141454554253736671327606787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377212144676631123540284765 141454554253736671327606787)
        ·
          refine ⟨212181831380605006991410181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141454554253736671327606787 212181831380605006991410181)
          ·
            refine ⟨39784093383863438810889409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212181831380605006991410181 39784093383863438810889409)
            ·
              refine ⟨29838070037897579108167057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39784093383863438810889409 29838070037897579108167057)
              ·
                refine ⟨22378552528423184331125293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29838070037897579108167057 22378552528423184331125293)
                ·
                  refine ⟨8391957198158694124171985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22378552528423184331125293 8391957198158694124171985)
                  ·
                    refine ⟨6293967898619020593128989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8391957198158694124171985 6293967898619020593128989)
                    ·
                      refine ⟨2360237961982132722423371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6293967898619020593128989 2360237961982132722423371)
                      ·
                        rfl

theorem cell23_4596547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_4596547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596547 prefixEnd_4596547 := by exact prefixLift 4596547
  have htrace : WordTrace (prefixWord ++ tailWord_4596547) baseStart_4596547 baseEnd_4596547 := by
    simpa [prefixWord, tailWord_4596547, baseEnd_4596547] using wordTrace_append hprefix tailTrace_4596547
  have hstable : (prefixWord ++ tailWord_4596547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596547).length < 2 ^ (prefixWord ++ tailWord_4596547).sum := by decide
  have hdescent : baseEnd_4596547 < baseStart_4596547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596561 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_4596561 : Nat := 118140960795 + 4596561 * 2 ^ 59
def prefixEnd_4596561 : Nat := 4983230072969 + 3 ^ 40 * 4596561 * 2
def baseEnd_4596561 : Nat := 2360245150711295667648307

theorem tailTrace_4596561 : CollatzResearch.WordTrace tailWord_4596561 prefixEnd_4596561 2360245150711295667648307 := by
  unfold tailWord_4596561
  simp only [CollatzResearch.WordTrace]
  refine ⟨167650352700452001964469537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111766901800301334642979691 167650352700452001964469537)
  ·
    refine ⟨125737764525339001473352153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167650352700452001964469537 125737764525339001473352153)
    ·
      refine ⟨94303323394004251105014115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125737764525339001473352153 94303323394004251105014115)
      ·
        refine ⟨141454985091006376657521173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94303323394004251105014115 141454985091006376657521173)
        ·
          refine ⟨6630702426140923905821305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 141454985091006376657521173 6630702426140923905821305)
          ·
            refine ⟨4973026819605692929365979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6630702426140923905821305 4973026819605692929365979)
            ·
              refine ⟨7459540229408539394048969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973026819605692929365979 7459540229408539394048969)
              ·
                refine ⟨5594655172056404545536727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7459540229408539394048969 5594655172056404545536727)
                ·
                  refine ⟨8391982758084606818305091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5594655172056404545536727 8391982758084606818305091)
                  ·
                    refine ⟨12587974137126910227457637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8391982758084606818305091 12587974137126910227457637)
                    ·
                      refine ⟨2360245150711295667648307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12587974137126910227457637 2360245150711295667648307)
                      ·
                        rfl

theorem cell23_4596561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_4596561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596561 prefixEnd_4596561 := by exact prefixLift 4596561
  have htrace : WordTrace (prefixWord ++ tailWord_4596561) baseStart_4596561 baseEnd_4596561 := by
    simpa [prefixWord, tailWord_4596561, baseEnd_4596561] using wordTrace_append hprefix tailTrace_4596561
  have hstable : (prefixWord ++ tailWord_4596561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596561).length < 2 ^ (prefixWord ++ tailWord_4596561).sum := by decide
  have hdescent : baseEnd_4596561 < baseStart_4596561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596578 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_4596578 : Nat := 118140960795 + 4596578 * 2 ^ 59
def prefixEnd_4596578 : Nat := 4983230072969 + 3 ^ 40 * 4596578 * 2
def baseEnd_4596578 : Nat := 2360253879882422101135729

theorem tailTrace_4596578 : CollatzResearch.WordTrace tailWord_4596578 prefixEnd_4596578 2360253879882422101135729 := by
  unfold tailWord_4596578
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912743185347603466959597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111767315160926942578558925 41912743185347603466959597)
  ·
    refine ⟨15717278694505351300109849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41912743185347603466959597 15717278694505351300109849)
    ·
      refine ⟨11787959020879013475082387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15717278694505351300109849 11787959020879013475082387)
      ·
        refine ⟨17681938531318520212623581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11787959020879013475082387 17681938531318520212623581)
        ·
          refine ⟨6630726949244445079733843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17681938531318520212623581 6630726949244445079733843)
          ·
            refine ⟨9946090423866667619600765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6630726949244445079733843 9946090423866667619600765)
            ·
              refine ⟨3729783908950000357350287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9946090423866667619600765 3729783908950000357350287)
              ·
                refine ⟨5594675863425000536025431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729783908950000357350287 5594675863425000536025431)
                ·
                  refine ⟨8392013795137500804038147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5594675863425000536025431 8392013795137500804038147)
                  ·
                    refine ⟨12588020692706251206057221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8392013795137500804038147 12588020692706251206057221)
                    ·
                      refine ⟨2360253879882422101135729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12588020692706251206057221 2360253879882422101135729)
                      ·
                        rfl

theorem cell23_4596578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_4596578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596578 prefixEnd_4596578 := by exact prefixLift 4596578
  have htrace : WordTrace (prefixWord ++ tailWord_4596578) baseStart_4596578 baseEnd_4596578 := by
    simpa [prefixWord, tailWord_4596578, baseEnd_4596578] using wordTrace_append hprefix tailTrace_4596578
  have hstable : (prefixWord ++ tailWord_4596578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596578).length < 2 ^ (prefixWord ++ tailWord_4596578).sum := by decide
  have hdescent : baseEnd_4596578 < baseStart_4596578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596594 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_4596594 : Nat := 118140960795 + 4596594 * 2 ^ 59
def prefixEnd_4596594 : Nat := 4983230072969 + 3 ^ 40 * 4596594 * 2
def baseEnd_4596594 : Nat := 2360262095572894038535655

theorem tailTrace_4596594 : CollatzResearch.WordTrace tailWord_4596594 prefixEnd_4596594 2360262095572894038535655 := by
  unfold tailWord_4596594
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912889077333112150105209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111767704206221632400280557 41912889077333112150105209)
  ·
    refine ⟨31434666807999834112578907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41912889077333112150105209 31434666807999834112578907)
    ·
      refine ⟨47152000211999751168868361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31434666807999834112578907 47152000211999751168868361)
      ·
        refine ⟨35364000158999813376651271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47152000211999751168868361 35364000158999813376651271)
        ·
          refine ⟨53046000238499720064976907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35364000158999813376651271 53046000238499720064976907)
          ·
            refine ⟨79569000357749580097465361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53046000238499720064976907 79569000357749580097465361)
            ·
              refine ⟨59676750268312185073099021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79569000357749580097465361 59676750268312185073099021)
              ·
                refine ⟨22378781350617069402412133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59676750268312185073099021 22378781350617069402412133)
                ·
                  refine ⟨4196021503240700512952275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22378781350617069402412133 4196021503240700512952275)
                  ·
                    refine ⟨6294032254861050769428413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196021503240700512952275 6294032254861050769428413)
                    ·
                      refine ⟨2360262095572894038535655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6294032254861050769428413 2360262095572894038535655)
                      ·
                        rfl

theorem cell23_4596594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_4596594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596594 prefixEnd_4596594 := by exact prefixLift 4596594
  have htrace : WordTrace (prefixWord ++ tailWord_4596594) baseStart_4596594 baseEnd_4596594 := by
    simpa [prefixWord, tailWord_4596594, baseEnd_4596594] using wordTrace_append hprefix tailTrace_4596594
  have hstable : (prefixWord ++ tailWord_4596594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596594).length < 2 ^ (prefixWord ++ tailWord_4596594).sum := by decide
  have hdescent : baseEnd_4596594 < baseStart_4596594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596597 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4596597 : Nat := 118140960795 + 4596597 * 2 ^ 59
def prefixEnd_4596597 : Nat := 4983230072969 + 3 ^ 40 * 4596597 * 2
def baseEnd_4596597 : Nat := 786754545338285842266047

theorem tailTrace_4596597 : CollatzResearch.WordTrace tailWord_4596597 prefixEnd_4596597 786754545338285842266047 := by
  unfold tailWord_4596597
  simp only [CollatzResearch.WordTrace]
  refine ⟨167651665728321580112780045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111767777152214386741853363 167651665728321580112780045)
  ·
    refine ⟨62869374648120592542292517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167651665728321580112780045 62869374648120592542292517)
    ·
      refine ⟨11788007746522611101679847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62869374648120592542292517 11788007746522611101679847)
      ·
        refine ⟨17682011619783916652519771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788007746522611101679847 17682011619783916652519771)
        ·
          refine ⟨26523017429675874978779657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17682011619783916652519771 26523017429675874978779657)
          ·
            refine ⟨19892263072256906234084743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26523017429675874978779657 19892263072256906234084743)
            ·
              refine ⟨29838394608385359351127115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19892263072256906234084743 29838394608385359351127115)
              ·
                refine ⟨44757591912578039026690673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29838394608385359351127115 44757591912578039026690673)
                ·
                  refine ⟨33568193934433529270018005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44757591912578039026690673 33568193934433529270018005)
                  ·
                    refine ⟨786754545338285842266047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33568193934433529270018005 786754545338285842266047)
                    ·
                      rfl

theorem cell23_4596597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4596597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596597 prefixEnd_4596597 := by exact prefixLift 4596597
  have htrace : WordTrace (prefixWord ++ tailWord_4596597) baseStart_4596597 baseEnd_4596597 := by
    simpa [prefixWord, tailWord_4596597, baseEnd_4596597] using wordTrace_append hprefix tailTrace_4596597
  have hstable : (prefixWord ++ tailWord_4596597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596597).length < 2 ^ (prefixWord ++ tailWord_4596597).sum := by decide
  have hdescent : baseEnd_4596597 < baseStart_4596597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596637 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4596637 : Nat := 118140960795 + 4596637 * 2 ^ 59
def prefixEnd_4596637 : Nat := 4983230072969 + 3 ^ 40 * 4596637 * 2
def baseEnd_4596637 : Nat := 2360284175241037370297957

theorem tailTrace_4596637 : CollatzResearch.WordTrace tailWord_4596637 prefixEnd_4596637 2360284175241037370297957 := by
  unfold tailWord_4596637
  simp only [CollatzResearch.WordTrace]
  refine ⟨167653124648176666944236165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111768749765451111296157443 167653124648176666944236165)
  ·
    refine ⟨31434960871533125052044281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167653124648176666944236165 31434960871533125052044281)
    ·
      refine ⟨23576220653649843789033211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31434960871533125052044281 23576220653649843789033211)
      ·
        refine ⟨35364330980474765683549817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23576220653649843789033211 35364330980474765683549817)
        ·
          refine ⟨26523248235356074262662363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35364330980474765683549817 26523248235356074262662363)
          ·
            refine ⟨39784872353034111393993545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26523248235356074262662363 39784872353034111393993545)
            ·
              refine ⟨29838654264775583545495159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39784872353034111393993545 29838654264775583545495159)
              ·
                refine ⟨44757981397163375318242739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29838654264775583545495159 44757981397163375318242739)
                ·
                  refine ⟨67136972095745062977364109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44757981397163375318242739 67136972095745062977364109)
                  ·
                    refine ⟨25176364535904398616511541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67136972095745062977364109 25176364535904398616511541)
                    ·
                      refine ⟨2360284175241037370297957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25176364535904398616511541 2360284175241037370297957)
                      ·
                        rfl

theorem cell23_4596637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4596637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596637 prefixEnd_4596637 := by exact prefixLift 4596637
  have htrace : WordTrace (prefixWord ++ tailWord_4596637) baseStart_4596637 baseEnd_4596637 := by
    simpa [prefixWord, tailWord_4596637, baseEnd_4596637] using wordTrace_append hprefix tailTrace_4596637
  have hstable : (prefixWord ++ tailWord_4596637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596637).length < 2 ^ (prefixWord ++ tailWord_4596637).sum := by decide
  have hdescent : baseEnd_4596637 < baseStart_4596637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596662 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4596662 : Nat := 118140960795 + 4596662 * 2 ^ 59
def prefixEnd_4596662 : Nat := 4983230072969 + 3 ^ 40 * 4596662 * 2
def baseEnd_4596662 : Nat := 2360297012257399772485343

theorem tailTrace_4596662 : CollatzResearch.WordTrace tailWord_4596662 prefixEnd_4596662 2360297012257399772485343 := by
  unfold tailWord_4596662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478377279567881013368515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111769357648724064142597493 10478377279567881013368515)
  ·
    refine ⟨15717565919351821520052773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10478377279567881013368515 15717565919351821520052773)
    ·
      refine ⟨2947043609878466535009895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15717565919351821520052773 2947043609878466535009895)
      ·
        refine ⟨4420565414817699802514843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947043609878466535009895 4420565414817699802514843)
        ·
          refine ⟨6630848122226549703772265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4420565414817699802514843 6630848122226549703772265)
          ·
            refine ⟨4973136091669912277829199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6630848122226549703772265 4973136091669912277829199)
            ·
              refine ⟨7459704137504868416743799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973136091669912277829199 7459704137504868416743799)
              ·
                refine ⟨11189556206257302625115699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459704137504868416743799 11189556206257302625115699)
                ·
                  refine ⟨16784334309385953937673549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11189556206257302625115699 16784334309385953937673549)
                  ·
                    refine ⟨6294125366019732726627581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16784334309385953937673549 6294125366019732726627581)
                    ·
                      refine ⟨2360297012257399772485343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6294125366019732726627581 2360297012257399772485343)
                      ·
                        rfl

theorem cell23_4596662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4596662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596662 prefixEnd_4596662 := by exact prefixLift 4596662
  have htrace : WordTrace (prefixWord ++ tailWord_4596662) baseStart_4596662 baseEnd_4596662 := by
    simpa [prefixWord, tailWord_4596662, baseEnd_4596662] using wordTrace_append hprefix tailTrace_4596662
  have hstable : (prefixWord ++ tailWord_4596662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596662).length < 2 ^ (prefixWord ++ tailWord_4596662).sum := by decide
  have hdescent : baseEnd_4596662 < baseStart_4596662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596667 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3]
def baseStart_4596667 : Nat := 118140960795 + 4596667 * 2 ^ 59
def prefixEnd_4596667 : Nat := 4983230072969 + 3 ^ 40 * 4596667 * 2
def baseEnd_4596667 : Nat := 2360299579660672252922819

theorem tailTrace_4596667 : CollatzResearch.WordTrace tailWord_4596667 prefixEnd_4596667 2360299579660672252922819 := by
  unfold tailWord_4596667
  simp only [CollatzResearch.WordTrace]
  refine ⟨167654218838067982067828255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111769479225378654711885503 167654218838067982067828255)
  ·
    refine ⟨251481328257101973101742383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167654218838067982067828255 251481328257101973101742383)
    ·
      refine ⟨377221992385652959652613575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251481328257101973101742383 377221992385652959652613575)
      ·
        refine ⟨565832988578479439478920363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377221992385652959652613575 565832988578479439478920363)
        ·
          refine ⟨848749482867719159218380545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565832988578479439478920363 848749482867719159218380545)
          ·
            refine ⟨636562112150789369413785409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 848749482867719159218380545 636562112150789369413785409)
            ·
              refine ⟨477421584113092027060339057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636562112150789369413785409 477421584113092027060339057)
              ·
                refine ⟨358066188084819020295254293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477421584113092027060339057 358066188084819020295254293)
                ·
                  refine ⟨16784352566475891576340045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 358066188084819020295254293 16784352566475891576340045)
                  ·
                    refine ⟨6294132212428459341127517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16784352566475891576340045 6294132212428459341127517)
                    ·
                      refine ⟨2360299579660672252922819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6294132212428459341127517 2360299579660672252922819)
                      ·
                        rfl

theorem cell23_4596667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3].length) (baseStart_4596667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596667 prefixEnd_4596667 := by exact prefixLift 4596667
  have htrace : WordTrace (prefixWord ++ tailWord_4596667) baseStart_4596667 baseEnd_4596667 := by
    simpa [prefixWord, tailWord_4596667, baseEnd_4596667] using wordTrace_append hprefix tailTrace_4596667
  have hstable : (prefixWord ++ tailWord_4596667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596667).length < 2 ^ (prefixWord ++ tailWord_4596667).sum := by decide
  have hdescent : baseEnd_4596667 < baseStart_4596667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596687 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 7]
def baseStart_4596687 : Nat := 118140960795 + 4596687 * 2 ^ 59
def prefixEnd_4596687 : Nat := 4983230072969 + 3 ^ 40 * 4596687 * 2
def baseEnd_4596687 : Nat := 786769949757920724890909

theorem tailTrace_4596687 : CollatzResearch.WordTrace tailWord_4596687 prefixEnd_4596687 786769949757920724890909 := by
  unfold tailWord_4596687
  simp only [CollatzResearch.WordTrace]
  refine ⟨167654948297995525483556315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111769965531997016989037543 167654948297995525483556315)
  ·
    refine ⟨251482422446993288225334473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167654948297995525483556315 251482422446993288225334473)
    ·
      refine ⟨188611816835244966169000855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251482422446993288225334473 188611816835244966169000855)
      ·
        refine ⟨282917725252867449253501283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188611816835244966169000855 282917725252867449253501283)
        ·
          refine ⟨424376587879301173880251925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282917725252867449253501283 424376587879301173880251925)
          ·
            refine ⟨19892652556842242525636809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 424376587879301173880251925 19892652556842242525636809)
            ·
              refine ⟨14919489417631681894227607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19892652556842242525636809 14919489417631681894227607)
              ·
                refine ⟨22379234126447522841341411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14919489417631681894227607 22379234126447522841341411)
                ·
                  refine ⟨33568851189671284262012117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22379234126447522841341411 33568851189671284262012117)
                  ·
                    refine ⟨786769949757920724890909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33568851189671284262012117 786769949757920724890909)
                    ·
                      rfl

theorem cell23_4596687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_4596687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596687 prefixEnd_4596687 := by exact prefixLift 4596687
  have htrace : WordTrace (prefixWord ++ tailWord_4596687) baseStart_4596687 baseEnd_4596687 := by
    simpa [prefixWord, tailWord_4596687, baseEnd_4596687] using wordTrace_append hprefix tailTrace_4596687
  have hstable : (prefixWord ++ tailWord_4596687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596687).length < 2 ^ (prefixWord ++ tailWord_4596687).sum := by decide
  have hdescent : baseEnd_4596687 < baseStart_4596687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596714 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_4596714 : Nat := 118140960795 + 4596714 * 2 ^ 59
def prefixEnd_4596714 : Nat := 4983230072969 + 3 ^ 40 * 4596714 * 2
def baseEnd_4596714 : Nat := 2360323713251433569035103

theorem tailTrace_4596714 : CollatzResearch.WordTrace tailWord_4596714 prefixEnd_4596714 2360323713251433569035103 := by
  unfold tailWord_4596714
  simp only [CollatzResearch.WordTrace]
  refine ⟨41913983267224427273697299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111770622045931806063192797 41913983267224427273697299)
  ·
    refine ⟨62870974900836640910545949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41913983267224427273697299 62870974900836640910545949)
    ·
      refine ⟨23576615587813740341454731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62870974900836640910545949 23576615587813740341454731)
      ·
        refine ⟨35364923381720610512182097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23576615587813740341454731 35364923381720610512182097)
        ·
          refine ⟨26523692536290457884136573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35364923381720610512182097 26523692536290457884136573)
          ·
            refine ⟨9946384701108921706551215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26523692536290457884136573 9946384701108921706551215)
            ·
              refine ⟨14919577051663382559826823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9946384701108921706551215 14919577051663382559826823)
              ·
                refine ⟨22379365577495073839740235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14919577051663382559826823 22379365577495073839740235)
                ·
                  refine ⟨33569048366242610759610353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22379365577495073839740235 33569048366242610759610353)
                  ·
                    refine ⟨25176786274681958069707765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33569048366242610759610353 25176786274681958069707765)
                    ·
                      refine ⟨2360323713251433569035103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25176786274681958069707765 2360323713251433569035103)
                      ·
                        rfl

theorem cell23_4596714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_4596714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596714 prefixEnd_4596714 := by exact prefixLift 4596714
  have htrace : WordTrace (prefixWord ++ tailWord_4596714) baseStart_4596714 baseEnd_4596714 := by
    simpa [prefixWord, tailWord_4596714, baseEnd_4596714] using wordTrace_append hprefix tailTrace_4596714
  have hstable : (prefixWord ++ tailWord_4596714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596714).length < 2 ^ (prefixWord ++ tailWord_4596714).sum := by decide
  have hdescent : baseEnd_4596714 < baseStart_4596714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596787 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_4596787 : Nat := 118140960795 + 4596787 * 2 ^ 59
def prefixEnd_4596787 : Nat := 4983230072969 + 3 ^ 40 * 4596787 * 2
def baseEnd_4596787 : Nat := 2360361197339211783422267

theorem tailTrace_4596787 : CollatzResearch.WordTrace tailWord_4596787 prefixEnd_4596787 2360361197339211783422267 := by
  unfold tailWord_4596787
  simp only [CollatzResearch.WordTrace]
  refine ⟨167658595597633242562196615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111772397065088828374797743 167658595597633242562196615)
  ·
    refine ⟨251487893396449863843294923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167658595597633242562196615 251487893396449863843294923)
    ·
      refine ⟨377231840094674795764942385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251487893396449863843294923 377231840094674795764942385)
      ·
        refine ⟨282923880071006096823706789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377231840094674795764942385 282923880071006096823706789)
        ·
          refine ⟨53048227513313643154445023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282923880071006096823706789 53048227513313643154445023)
          ·
            refine ⟨79572341269970464731667535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53048227513313643154445023 79572341269970464731667535)
            ·
              refine ⟨119358511904955697097501303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79572341269970464731667535 119358511904955697097501303)
              ·
                refine ⟨179037767857433545646251955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119358511904955697097501303 179037767857433545646251955)
                ·
                  refine ⟨268556651786150318469377933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179037767857433545646251955 268556651786150318469377933)
                  ·
                    refine ⟨100708744419806369426016725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268556651786150318469377933 100708744419806369426016725)
                    ·
                      refine ⟨2360361197339211783422267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100708744419806369426016725 2360361197339211783422267)
                      ·
                        rfl

theorem cell23_4596787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_4596787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596787 prefixEnd_4596787 := by exact prefixLift 4596787
  have htrace : WordTrace (prefixWord ++ tailWord_4596787) baseStart_4596787 baseEnd_4596787 := by
    simpa [prefixWord, tailWord_4596787, baseEnd_4596787] using wordTrace_append hprefix tailTrace_4596787
  have hstable : (prefixWord ++ tailWord_4596787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596787).length < 2 ^ (prefixWord ++ tailWord_4596787).sum := by decide
  have hdescent : baseEnd_4596787 < baseStart_4596787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596794 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_4596794 : Nat := 118140960795 + 4596794 * 2 ^ 59
def prefixEnd_4596794 : Nat := 4983230072969 + 3 ^ 40 * 4596794 * 2
def baseEnd_4596794 : Nat := 786788263901264418678245

theorem tailTrace_4596794 : CollatzResearch.WordTrace tailWord_4596794 prefixEnd_4596794 786788263901264418678245 := by
  unfold tailWord_4596794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41914712727151970689425359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111772567272405255171800957 41914712727151970689425359)
  ·
    refine ⟨62872069090727956034138039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41914712727151970689425359 62872069090727956034138039)
    ·
      refine ⟨94308103636091934051207059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62872069090727956034138039 94308103636091934051207059)
      ·
        refine ⟨141462155454137901076810589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94308103636091934051207059 141462155454137901076810589)
        ·
          refine ⟨53048308295301712903803971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141462155454137901076810589 53048308295301712903803971)
          ·
            refine ⟨79572462442952569355705957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53048308295301712903803971 79572462442952569355705957)
            ·
              refine ⟨14919836708053606754194867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79572462442952569355705957 14919836708053606754194867)
              ·
                refine ⟨22379755062080410131292301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14919836708053606754194867 22379755062080410131292301)
                ·
                  refine ⟨8392408148280153799234613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22379755062080410131292301 8392408148280153799234613)
                  ·
                    refine ⟨786788263901264418678245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8392408148280153799234613 786788263901264418678245)
                    ·
                      rfl

theorem cell23_4596794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_4596794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596794 prefixEnd_4596794 := by exact prefixLift 4596794
  have htrace : WordTrace (prefixWord ++ tailWord_4596794) baseStart_4596794 baseEnd_4596794 := by
    simpa [prefixWord, tailWord_4596794, baseEnd_4596794] using wordTrace_append hprefix tailTrace_4596794
  have hstable : (prefixWord ++ tailWord_4596794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596794).length < 2 ^ (prefixWord ++ tailWord_4596794).sum := by decide
  have hdescent : baseEnd_4596794 < baseStart_4596794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596841 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_4596841 : Nat := 118140960795 + 4596841 * 2 ^ 59
def prefixEnd_4596841 : Nat := 4983230072969 + 3 ^ 40 * 4596841 * 2
def baseEnd_4596841 : Nat := 786796308431518190715673

theorem tailTrace_4596841 : CollatzResearch.WordTrace tailWord_4596841 prefixEnd_4596841 786796308431518190715673 := by
  unfold tailWord_4596841
  simp only [CollatzResearch.WordTrace]
  refine ⟨167660565139437609784662377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111773710092958406523108251 167660565139437609784662377)
  ·
    refine ⟨125745423854578207338496783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167660565139437609784662377 125745423854578207338496783)
    ·
      refine ⟨188618135781867311007745175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125745423854578207338496783 188618135781867311007745175)
      ·
        refine ⟨282927203672800966511617763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188618135781867311007745175 282927203672800966511617763)
        ·
          refine ⟨424390805509201449767426645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282927203672800966511617763 424390805509201449767426645)
          ·
            refine ⟨4973329752060954489462031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 424390805509201449767426645 4973329752060954489462031)
            ·
              refine ⟨7459994628091431734193047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973329752060954489462031 7459994628091431734193047)
              ·
                refine ⟨11189991942137147601289571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459994628091431734193047 11189991942137147601289571)
                ·
                  refine ⟨16784987913205721401934357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11189991942137147601289571 16784987913205721401934357)
                  ·
                    refine ⟨786796308431518190715673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16784987913205721401934357 786796308431518190715673)
                    ·
                      rfl

theorem cell23_4596841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_4596841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596841 prefixEnd_4596841 := by exact prefixLift 4596841
  have htrace : WordTrace (prefixWord ++ tailWord_4596841) baseStart_4596841 baseEnd_4596841 := by
    simpa [prefixWord, tailWord_4596841, baseEnd_4596841] using wordTrace_append hprefix tailTrace_4596841
  have hstable : (prefixWord ++ tailWord_4596841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596841).length < 2 ^ (prefixWord ++ tailWord_4596841).sum := by decide
  have hdescent : baseEnd_4596841 < baseStart_4596841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596844 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_4596844 : Nat := 118140960795 + 4596844 * 2 ^ 59
def prefixEnd_4596844 : Nat := 4983230072969 + 3 ^ 40 * 4596844 * 2
def baseEnd_4596844 : Nat := 2360390465736518060409505

theorem tailTrace_4596844 : CollatzResearch.WordTrace tailWord_4596844 prefixEnd_4596844 2360390465736518060409505 := by
  unfold tailWord_4596844
  simp only [CollatzResearch.WordTrace]
  refine ⟨83830337279213370648510793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111773783038951160864681057 83830337279213370648510793)
  ·
    refine ⟨62872752959410027986383095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83830337279213370648510793 62872752959410027986383095)
    ·
      refine ⟨94309129439115041979574643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62872752959410027986383095 94309129439115041979574643)
      ·
        refine ⟨141463694158672562969361965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94309129439115041979574643 141463694158672562969361965)
        ·
          refine ⟨53048885309502211113510737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141463694158672562969361965 53048885309502211113510737)
          ·
            refine ⟨39786663982126658335133053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53048885309502211113510737 39786663982126658335133053)
            ·
              refine ⟨14919998993297496875674895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39786663982126658335133053 14919998993297496875674895)
              ·
                refine ⟨22379998489946245313512343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14919998993297496875674895 22379998489946245313512343)
                ·
                  refine ⟨33569997734919367970268515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22379998489946245313512343 33569997734919367970268515)
                  ·
                    refine ⟨50354996602379051955402773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33569997734919367970268515 50354996602379051955402773)
                    ·
                      refine ⟨2360390465736518060409505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50354996602379051955402773 2360390465736518060409505)
                      ·
                        rfl

theorem cell23_4596844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_4596844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596844 prefixEnd_4596844 := by exact prefixLift 4596844
  have htrace : WordTrace (prefixWord ++ tailWord_4596844) baseStart_4596844 baseEnd_4596844 := by
    simpa [prefixWord, tailWord_4596844, baseEnd_4596844] using wordTrace_append hprefix tailTrace_4596844
  have hstable : (prefixWord ++ tailWord_4596844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596844).length < 2 ^ (prefixWord ++ tailWord_4596844).sum := by decide
  have hdescent : baseEnd_4596844 < baseStart_4596844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596848 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2]
def baseStart_4596848 : Nat := 118140960795 + 4596848 * 2 ^ 59
def prefixEnd_4596848 : Nat := 4983230072969 + 3 ^ 40 * 4596848 * 2
def baseEnd_4596848 : Nat := 2360392519659136044759487

theorem tailTrace_4596848 : CollatzResearch.WordTrace tailWord_4596848 prefixEnd_4596848 2360392519659136044759487 := by
  unfold tailWord_4596848
  simp only [CollatzResearch.WordTrace]
  refine ⟨83830410225206124990083599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111773880300274833320111465 83830410225206124990083599)
  ·
    refine ⟨125745615337809187485125399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83830410225206124990083599 125745615337809187485125399)
    ·
      refine ⟨188618423006713781227688099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125745615337809187485125399 188618423006713781227688099)
      ·
        refine ⟨282927634510070671841532149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188618423006713781227688099 282927634510070671841532149)
        ·
          refine ⟨26524465735319125485143639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282927634510070671841532149 26524465735319125485143639)
          ·
            refine ⟨39786698602978688227715459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26524465735319125485143639 39786698602978688227715459)
            ·
              refine ⟨59680047904468032341573189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39786698602978688227715459 59680047904468032341573189)
              ·
                refine ⟨11190008982087756064044973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59680047904468032341573189 11190008982087756064044973)
                ·
                  refine ⟨4196253368282908524016865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11190008982087756064044973 4196253368282908524016865)
                  ·
                    refine ⟨3147190026212181393012649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4196253368282908524016865 3147190026212181393012649)
                    ·
                      refine ⟨2360392519659136044759487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147190026212181393012649 2360392519659136044759487)
                      ·
                        rfl

theorem cell23_4596848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2].length) (baseStart_4596848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596848 prefixEnd_4596848 := by exact prefixLift 4596848
  have htrace : WordTrace (prefixWord ++ tailWord_4596848) baseStart_4596848 baseEnd_4596848 := by
    simpa [prefixWord, tailWord_4596848, baseEnd_4596848] using wordTrace_append hprefix tailTrace_4596848
  have hstable : (prefixWord ++ tailWord_4596848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596848).length < 2 ^ (prefixWord ++ tailWord_4596848).sum := by decide
  have hdescent : baseEnd_4596848 < baseStart_4596848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596868 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4596868 : Nat := 118140960795 + 4596868 * 2 ^ 59
def prefixEnd_4596868 : Nat := 4983230072969 + 3 ^ 40 * 4596868 * 2
def baseEnd_4596868 : Nat := 2360402789272225966509395

theorem tailTrace_4596868 : CollatzResearch.WordTrace tailWord_4596868 prefixEnd_4596868 2360402789272225966509395 := by
  unfold tailWord_4596868
  simp only [CollatzResearch.WordTrace]
  refine ⟨83830774955169896697947629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111774366606893195597263505 83830774955169896697947629)
  ·
    refine ⟨31436540608188711261730361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83830774955169896697947629 31436540608188711261730361)
    ·
      refine ⟨23577405456141533446297771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31436540608188711261730361 23577405456141533446297771)
      ·
        refine ⟨35366108184212300169446657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23577405456141533446297771 35366108184212300169446657)
        ·
          refine ⟨26524581138159225127084993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35366108184212300169446657 26524581138159225127084993)
          ·
            refine ⟨19893435853619418845313745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26524581138159225127084993 19893435853619418845313745)
            ·
              refine ⟨14920076890214564133985309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19893435853619418845313745 14920076890214564133985309)
              ·
                refine ⟨5595028833830461550244491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14920076890214564133985309 5595028833830461550244491)
                ·
                  refine ⟨8392543250745692325366737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5595028833830461550244491 8392543250745692325366737)
                  ·
                    refine ⟨6294407438059269244025053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8392543250745692325366737 6294407438059269244025053)
                    ·
                      refine ⟨2360402789272225966509395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6294407438059269244025053 2360402789272225966509395)
                      ·
                        rfl

theorem cell23_4596868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4596868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596868 prefixEnd_4596868 := by exact prefixLift 4596868
  have htrace : WordTrace (prefixWord ++ tailWord_4596868) baseStart_4596868 baseEnd_4596868 := by
    simpa [prefixWord, tailWord_4596868, baseEnd_4596868] using wordTrace_append hprefix tailTrace_4596868
  have hstable : (prefixWord ++ tailWord_4596868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596868).length < 2 ^ (prefixWord ++ tailWord_4596868).sum := by decide
  have hdescent : baseEnd_4596868 < baseStart_4596868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596882 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4596882 : Nat := 118140960795 + 4596882 * 2 ^ 59
def prefixEnd_4596882 : Nat := 4983230072969 + 3 ^ 40 * 4596882 * 2
def baseEnd_4596882 : Nat := 2360409978001388911734331

theorem tailTrace_4596882 : CollatzResearch.WordTrace tailWord_4596882 prefixEnd_4596882 2360409978001388911734331 := by
  unfold tailWord_4596882
  simp only [CollatzResearch.WordTrace]
  refine ⟨41915515133072268446726225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111774707021526049191269933 41915515133072268446726225)
  ·
    refine ⟨31436636349804201335044669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41915515133072268446726225 31436636349804201335044669)
    ·
      refine ⟨11788738631176575500641751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31436636349804201335044669 11788738631176575500641751)
      ·
        refine ⟨17683107946764863250962627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788738631176575500641751 17683107946764863250962627)
        ·
          refine ⟨26524661920147294876443941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17683107946764863250962627 26524661920147294876443941)
          ·
            refine ⟨4973374110027617789333239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26524661920147294876443941 4973374110027617789333239)
            ·
              refine ⟨7460061165041426683999859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973374110027617789333239 7460061165041426683999859)
              ·
                refine ⟨11190091747562140025999789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7460061165041426683999859 11190091747562140025999789)
                ·
                  refine ⟨4196284405335802509749921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11190091747562140025999789 4196284405335802509749921)
                  ·
                    refine ⟨3147213304001851882312441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4196284405335802509749921 3147213304001851882312441)
                    ·
                      refine ⟨2360409978001388911734331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147213304001851882312441 2360409978001388911734331)
                      ·
                        rfl

theorem cell23_4596882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4596882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596882 prefixEnd_4596882 := by exact prefixLift 4596882
  have htrace : WordTrace (prefixWord ++ tailWord_4596882) baseStart_4596882 baseEnd_4596882 := by
    simpa [prefixWord, tailWord_4596882, baseEnd_4596882] using wordTrace_append hprefix tailTrace_4596882
  have hstable : (prefixWord ++ tailWord_4596882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596882).length < 2 ^ (prefixWord ++ tailWord_4596882).sum := by decide
  have hdescent : baseEnd_4596882 < baseStart_4596882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596908 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_4596908 : Nat := 118140960795 + 4596908 * 2 ^ 59
def prefixEnd_4596908 : Nat := 4983230072969 + 3 ^ 40 * 4596908 * 2
def baseEnd_4596908 : Nat := 2360423328498405810009211

theorem tailTrace_4596908 : CollatzResearch.WordTrace tailWord_4596908 prefixEnd_4596908 2360423328498405810009211 := by
  unfold tailWord_4596908
  simp only [CollatzResearch.WordTrace]
  refine ⟨83831504415097440113675689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111775339220129920151567585 83831504415097440113675689)
  ·
    refine ⟨62873628311323080085256767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83831504415097440113675689 62873628311323080085256767)
    ·
      refine ⟨94310442466984620127885151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62873628311323080085256767 94310442466984620127885151)
      ·
        refine ⟨141465663700476930191827727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94310442466984620127885151 141465663700476930191827727)
        ·
          refine ⟨212198495550715395287741591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141465663700476930191827727 212198495550715395287741591)
          ·
            refine ⟨318297743326073092931612387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212198495550715395287741591 318297743326073092931612387)
            ·
              refine ⟨477446614989109639397418581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318297743326073092931612387 477446614989109639397418581)
              ·
                refine ⟨5595077519403628586688499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 477446614989109639397418581 5595077519403628586688499)
                ·
                  refine ⟨8392616279105442880032749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5595077519403628586688499 8392616279105442880032749)
                  ·
                    refine ⟨3147231104664541080012281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8392616279105442880032749 3147231104664541080012281)
                    ·
                      refine ⟨2360423328498405810009211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147231104664541080012281 2360423328498405810009211)
                      ·
                        rfl

theorem cell23_4596908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_4596908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596908 prefixEnd_4596908 := by exact prefixLift 4596908
  have htrace : WordTrace (prefixWord ++ tailWord_4596908) baseStart_4596908 baseEnd_4596908 := by
    simpa [prefixWord, tailWord_4596908, baseEnd_4596908] using wordTrace_append hprefix tailTrace_4596908
  have hstable : (prefixWord ++ tailWord_4596908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596908).length < 2 ^ (prefixWord ++ tailWord_4596908).sum := by decide
  have hdescent : baseEnd_4596908 < baseStart_4596908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596932 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4596932 : Nat := 118140960795 + 4596932 * 2 ^ 59
def prefixEnd_4596932 : Nat := 4983230072969 + 3 ^ 40 * 4596932 * 2
def baseEnd_4596932 : Nat := 2360435652034113716109101

theorem tailTrace_4596932 : CollatzResearch.WordTrace tailWord_4596932 prefixEnd_4596932 2360435652034113716109101 := by
  unfold tailWord_4596932
  simp only [CollatzResearch.WordTrace]
  refine ⟨83831942091053966163112525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111775922788071954884150033 83831942091053966163112525)
  ·
    refine ⟨31436978284145237311167197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83831942091053966163112525 31436978284145237311167197)
    ·
      refine ⟨11788866856554463991687699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31436978284145237311167197 11788866856554463991687699)
      ·
        refine ⟨17683300284831695987531549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788866856554463991687699 17683300284831695987531549)
        ·
          refine ⟨6631237606811885995324331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17683300284831695987531549 6631237606811885995324331)
          ·
            refine ⟨9946856410217828992986497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631237606811885995324331 9946856410217828992986497)
            ·
              refine ⟨7460142307663371744739873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9946856410217828992986497 7460142307663371744739873)
              ·
                refine ⟨5595106730747528808554905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7460142307663371744739873 5595106730747528808554905)
                ·
                  refine ⟨4196330048060646606416179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5595106730747528808554905 4196330048060646606416179)
                  ·
                    refine ⟨6294495072090969909624269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196330048060646606416179 6294495072090969909624269)
                    ·
                      refine ⟨2360435652034113716109101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6294495072090969909624269 2360435652034113716109101)
                      ·
                        rfl

theorem cell23_4596932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4596932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596932 prefixEnd_4596932 := by exact prefixLift 4596932
  have htrace : WordTrace (prefixWord ++ tailWord_4596932) baseStart_4596932 baseEnd_4596932 := by
    simpa [prefixWord, tailWord_4596932, baseEnd_4596932] using wordTrace_append hprefix tailTrace_4596932
  have hstable : (prefixWord ++ tailWord_4596932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596932).length < 2 ^ (prefixWord ++ tailWord_4596932).sum := by decide
  have hdescent : baseEnd_4596932 < baseStart_4596932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4596961 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 7]
def baseStart_4596961 : Nat := 118140960795 + 4596961 * 2 ^ 59
def prefixEnd_4596961 : Nat := 4983230072969 + 3 ^ 40 * 4596961 * 2
def baseEnd_4596961 : Nat := 262272282552566011405163

theorem tailTrace_4596961 : CollatzResearch.WordTrace tailWord_4596961 prefixEnd_4596961 262272282552566011405163 := by
  unfold tailWord_4596961
  simp only [CollatzResearch.WordTrace]
  refine ⟨167664941899002870279030737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111776627932668580186020491 167664941899002870279030737)
  ·
    refine ⟨125748706424252152709273053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167664941899002870279030737 125748706424252152709273053)
    ·
      refine ⟨47155764909094557265977395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125748706424252152709273053 47155764909094557265977395)
      ·
        refine ⟨70733647363641835898966093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47155764909094557265977395 70733647363641835898966093)
        ·
          refine ⟨26525117761365688462112285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70733647363641835898966093 26525117761365688462112285)
          ·
            refine ⟨9946919160512133173292107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26525117761365688462112285 9946919160512133173292107)
            ·
              refine ⟨14920378740768199759938161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9946919160512133173292107 14920378740768199759938161)
              ·
                refine ⟨11190284055576149819953621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14920378740768199759938161 11190284055576149819953621)
                ·
                  refine ⟨262272282552566011405163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11190284055576149819953621 262272282552566011405163)
                  ·
                    rfl

theorem cell23_4596961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_4596961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4596961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4596961 prefixEnd_4596961 := by exact prefixLift 4596961
  have htrace : WordTrace (prefixWord ++ tailWord_4596961) baseStart_4596961 baseEnd_4596961 := by
    simpa [prefixWord, tailWord_4596961, baseEnd_4596961] using wordTrace_append hprefix tailTrace_4596961
  have hstable : (prefixWord ++ tailWord_4596961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4596961).length < 2 ^ (prefixWord ++ tailWord_4596961).sum := by decide
  have hdescent : baseEnd_4596961 < baseStart_4596961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4596961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597028 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4597028 : Nat := 118140960795 + 4597028 * 2 ^ 59
def prefixEnd_4597028 : Nat := 4983230072969 + 3 ^ 40 * 4597028 * 2
def baseEnd_4597028 : Nat := 2360484946176945340508659

theorem tailTrace_4597028 : CollatzResearch.WordTrace tailWord_4597028 prefixEnd_4597028 2360484946176945340508659 := by
  unfold tailWord_4597028
  simp only [CollatzResearch.WordTrace]
  refine ⟨83833692794880070360859869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111778257059840093814479825 83833692794880070360859869)
  ·
    refine ⟨31437634798080026385322451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83833692794880070360859869 31437634798080026385322451)
    ·
      refine ⟨47156452197120039577983677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31437634798080026385322451 47156452197120039577983677)
      ·
        refine ⟨17683669573920014841743879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47156452197120039577983677 17683669573920014841743879)
        ·
          refine ⟨26525504360880022262615819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17683669573920014841743879 26525504360880022262615819)
          ·
            refine ⟨39788256541320033393923729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26525504360880022262615819 39788256541320033393923729)
            ·
              refine ⟨29841192405990025045442797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39788256541320033393923729 29841192405990025045442797)
              ·
                refine ⟨11190447152246259392041049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29841192405990025045442797 11190447152246259392041049)
                ·
                  refine ⟨8392835364184694544030787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11190447152246259392041049 8392835364184694544030787)
                  ·
                    refine ⟨12589253046277041816046181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8392835364184694544030787 12589253046277041816046181)
                    ·
                      refine ⟨2360484946176945340508659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12589253046277041816046181 2360484946176945340508659)
                      ·
                        rfl

theorem cell23_4597028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4597028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597028 prefixEnd_4597028 := by exact prefixLift 4597028
  have htrace : WordTrace (prefixWord ++ tailWord_4597028) baseStart_4597028 baseEnd_4597028 := by
    simpa [prefixWord, tailWord_4597028, baseEnd_4597028] using wordTrace_append hprefix tailTrace_4597028
  have hstable : (prefixWord ++ tailWord_4597028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597028).length < 2 ^ (prefixWord ++ tailWord_4597028).sum := by decide
  have hdescent : baseEnd_4597028 < baseStart_4597028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597055 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 3, 4]
def baseStart_4597055 : Nat := 118140960795 + 4597055 * 2 ^ 59
def prefixEnd_4597055 : Nat := 4983230072969 + 3 ^ 40 * 4597055 * 2
def baseEnd_4597055 : Nat := 786832936718205578290345

theorem tailTrace_4597055 : CollatzResearch.WordTrace tailWord_4597055 prefixEnd_4597055 786832936718205578290345 := by
  unfold tailWord_4597055
  simp only [CollatzResearch.WordTrace]
  refine ⟨167668370360662324332952619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111778913573774882888635079 167668370360662324332952619)
  ·
    refine ⟨251502555540993486499428929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167668370360662324332952619 251502555540993486499428929)
    ·
      refine ⟨188626916655745114874571697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251502555540993486499428929 188626916655745114874571697)
      ·
        refine ⟨141470187491808836155928773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188626916655745114874571697 141470187491808836155928773)
        ·
          refine ⟨26525660154714156779236645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141470187491808836155928773 26525660154714156779236645)
          ·
            refine ⟨4973561279008904396106871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26525660154714156779236645 4973561279008904396106871)
            ·
              refine ⟨7460341918513356594160307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973561279008904396106871 7460341918513356594160307)
              ·
                refine ⟨11190512877770034891240461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7460341918513356594160307 11190512877770034891240461)
                ·
                  refine ⟨4196442329163763084215173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11190512877770034891240461 4196442329163763084215173)
                  ·
                    refine ⟨786832936718205578290345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4196442329163763084215173 786832936718205578290345)
                    ·
                      rfl

theorem cell23_4597055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_4597055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597055 prefixEnd_4597055 := by exact prefixLift 4597055
  have htrace : WordTrace (prefixWord ++ tailWord_4597055) baseStart_4597055 baseEnd_4597055 := by
    simpa [prefixWord, tailWord_4597055, baseEnd_4597055] using wordTrace_append hprefix tailTrace_4597055
  have hstable : (prefixWord ++ tailWord_4597055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597055).length < 2 ^ (prefixWord ++ tailWord_4597055).sum := by decide
  have hdescent : baseEnd_4597055 < baseStart_4597055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597068 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 6]
def baseStart_4597068 : Nat := 118140960795 + 4597068 * 2 ^ 59
def prefixEnd_4597068 : Nat := 4983230072969 + 3 ^ 40 * 4597068 * 2
def baseEnd_4597068 : Nat := 262278387267013909334275

theorem tailTrace_4597068 : CollatzResearch.WordTrace tailWord_4597068 prefixEnd_4597068 262278387267013909334275 := by
  unfold tailWord_4597068
  simp only [CollatzResearch.WordTrace]
  refine ⟨83834422254807613776587929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111779229673076818368783905 83834422254807613776587929)
  ·
    refine ⟨62875816691105710332440947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83834422254807613776587929 62875816691105710332440947)
    ·
      refine ⟨94313725036658565498661421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62875816691105710332440947 94313725036658565498661421)
      ·
        refine ⟨35367646888746962061998033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94313725036658565498661421 35367646888746962061998033)
        ·
          refine ⟨26525735166560221546498525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35367646888746962061998033 26525735166560221546498525)
          ·
            refine ⟨9947150687460083079936947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26525735166560221546498525 9947150687460083079936947)
            ·
              refine ⟨14920726031190124619905421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9947150687460083079936947 14920726031190124619905421)
              ·
                refine ⟨5595272261696296732464533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14920726031190124619905421 5595272261696296732464533)
                ·
                  refine ⟨262278387267013909334275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5595272261696296732464533 262278387267013909334275)
                  ·
                    rfl

theorem cell23_4597068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_4597068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597068 prefixEnd_4597068 := by exact prefixLift 4597068
  have htrace : WordTrace (prefixWord ++ tailWord_4597068) baseStart_4597068 baseEnd_4597068 := by
    simpa [prefixWord, tailWord_4597068, baseEnd_4597068] using wordTrace_append hprefix tailTrace_4597068
  have hstable : (prefixWord ++ tailWord_4597068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597068).length < 2 ^ (prefixWord ++ tailWord_4597068).sum := by decide
  have hdescent : baseEnd_4597068 < baseStart_4597068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597102 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_4597102 : Nat := 118140960795 + 4597102 * 2 ^ 59
def prefixEnd_4597102 : Nat := 4983230072969 + 3 ^ 40 * 4597102 * 2
def baseEnd_4597102 : Nat := 262280327082819783442591

theorem tailTrace_4597102 : CollatzResearch.WordTrace tailWord_4597102 prefixEnd_4597102 262280327082819783442591 := by
  unfold tailWord_4597102
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958760573936506419989195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111780056394328034239942373 20958760573936506419989195)
  ·
    refine ⟨31438140860904759629983793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20958760573936506419989195 31438140860904759629983793)
    ·
      refine ⟨23578605645678569722487845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31438140860904759629983793 23578605645678569722487845)
      ·
        refine ⟨4420988558564731822966471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23578605645678569722487845 4420988558564731822966471)
        ·
          refine ⟨6631482837847097734449707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4420988558564731822966471 6631482837847097734449707)
          ·
            refine ⟨9947224256770646601674561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631482837847097734449707 9947224256770646601674561)
            ·
              refine ⟨7460418192577984951255921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9947224256770646601674561 7460418192577984951255921)
              ·
                refine ⟨5595313644433488713441941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7460418192577984951255921 5595313644433488713441941)
                ·
                  refine ⟨262280327082819783442591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5595313644433488713441941 262280327082819783442591)
                  ·
                    rfl

theorem cell23_4597102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_4597102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597102 prefixEnd_4597102 := by exact prefixLift 4597102
  have htrace : WordTrace (prefixWord ++ tailWord_4597102) baseStart_4597102 baseEnd_4597102 := by
    simpa [prefixWord, tailWord_4597102, baseEnd_4597102] using wordTrace_append hprefix tailTrace_4597102
  have hstable : (prefixWord ++ tailWord_4597102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597102).length < 2 ^ (prefixWord ++ tailWord_4597102).sum := by decide
  have hdescent : baseEnd_4597102 < baseStart_4597102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597105 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_4597105 : Nat := 118140960795 + 4597105 * 2 ^ 59
def prefixEnd_4597105 : Nat := 4983230072969 + 3 ^ 40 * 4597105 * 2
def baseEnd_4597105 : Nat := 2360524484187341539245805

theorem tailTrace_4597105 : CollatzResearch.WordTrace tailWord_4597105 prefixEnd_4597105 2360524484187341539245805 := by
  unfold tailWord_4597105
  simp only [CollatzResearch.WordTrace]
  refine ⟨167670194010481182872272769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111780129340320788581515179 167670194010481182872272769)
  ·
    refine ⟨125752645507860887154204577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167670194010481182872272769 125752645507860887154204577)
    ·
      refine ⟨94314484130895665365653433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125752645507860887154204577 94314484130895665365653433)
      ·
        refine ⟨70735863098171749024240075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94314484130895665365653433 70735863098171749024240075)
        ·
          refine ⟨106103794647257623536360113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70735863098171749024240075 106103794647257623536360113)
          ·
            refine ⟨79577845985443217652270085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106103794647257623536360113 79577845985443217652270085)
            ·
              refine ⟨14920846122270603309800641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79577845985443217652270085 14920846122270603309800641)
              ·
                refine ⟨11190634591702952482350481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14920846122270603309800641 11190634591702952482350481)
                ·
                  refine ⟨8392975943777214361762861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11190634591702952482350481 8392975943777214361762861)
                  ·
                    refine ⟨3147365978916455385661073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8392975943777214361762861 3147365978916455385661073)
                    ·
                      refine ⟨2360524484187341539245805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147365978916455385661073 2360524484187341539245805)
                      ·
                        rfl

theorem cell23_4597105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_4597105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597105 prefixEnd_4597105 := by exact prefixLift 4597105
  have htrace : WordTrace (prefixWord ++ tailWord_4597105) baseStart_4597105 baseEnd_4597105 := by
    simpa [prefixWord, tailWord_4597105, baseEnd_4597105] using wordTrace_append hprefix tailTrace_4597105
  have hstable : (prefixWord ++ tailWord_4597105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597105).length < 2 ^ (prefixWord ++ tailWord_4597105).sum := by decide
  have hdescent : baseEnd_4597105 < baseStart_4597105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597111 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 3, 6]
def baseStart_4597111 : Nat := 118140960795 + 4597111 * 2 ^ 59
def prefixEnd_4597111 : Nat := 4983230072969 + 3 ^ 40 * 4597111 * 2
def baseEnd_4597111 : Nat := 786842521690422838590259

theorem tailTrace_4597111 : CollatzResearch.WordTrace tailWord_4597111 prefixEnd_4597111 786842521690422838590259 := by
  unfold tailWord_4597111
  simp only [CollatzResearch.WordTrace]
  refine ⟨167670412848459445896991187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111780275232306297264660791 167670412848459445896991187)
  ·
    refine ⟨251505619272689168845486781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167670412848459445896991187 251505619272689168845486781)
    ·
      refine ⟨94314607227258438317057543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251505619272689168845486781 94314607227258438317057543)
      ·
        refine ⟨141471910840887657475586315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94314607227258438317057543 141471910840887657475586315)
        ·
          refine ⟨212207866261331486213379473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141471910840887657475586315 212207866261331486213379473)
          ·
            refine ⟨159155899695998614660034605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212207866261331486213379473 159155899695998614660034605)
            ·
              refine ⟨59683462385999480497512977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159155899695998614660034605 59683462385999480497512977)
              ·
                refine ⟨44762596789499610373134733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59683462385999480497512977 44762596789499610373134733)
                ·
                  refine ⟨16785973796062353889925525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44762596789499610373134733 16785973796062353889925525)
                  ·
                    refine ⟨786842521690422838590259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16785973796062353889925525 786842521690422838590259)
                    ·
                      rfl

theorem cell23_4597111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_4597111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597111 prefixEnd_4597111 := by exact prefixLift 4597111
  have htrace : WordTrace (prefixWord ++ tailWord_4597111) baseStart_4597111 baseEnd_4597111 := by
    simpa [prefixWord, tailWord_4597111, baseEnd_4597111] using wordTrace_append hprefix tailTrace_4597111
  have hstable : (prefixWord ++ tailWord_4597111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597111).length < 2 ^ (prefixWord ++ tailWord_4597111).sum := by decide
  have hdescent : baseEnd_4597111 < baseStart_4597111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597128 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_4597128 : Nat := 118140960795 + 4597128 * 2 ^ 59
def prefixEnd_4597128 : Nat := 4983230072969 + 3 ^ 40 * 4597128 * 2
def baseEnd_4597128 : Nat := 786845431414131649752733

theorem tailTrace_4597128 : CollatzResearch.WordTrace tailWord_4597128 prefixEnd_4597128 786845431414131649752733 := by
  unfold tailWord_4597128
  simp only [CollatzResearch.WordTrace]
  refine ⟨83835516444698928900180019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111780688592931905200240025 83835516444698928900180019)
  ·
    refine ⟨125753274667048393350270029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83835516444698928900180019 125753274667048393350270029)
    ·
      refine ⟨47157478000143147506351261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125753274667048393350270029 47157478000143147506351261)
      ·
        refine ⟨17684054250053680314881723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47157478000143147506351261 17684054250053680314881723)
        ·
          refine ⟨26526081375080520472322585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17684054250053680314881723 26526081375080520472322585)
          ·
            refine ⟨19894561031310390354241939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26526081375080520472322585 19894561031310390354241939)
            ·
              refine ⟨29841841546965585531362909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19894561031310390354241939 29841841546965585531362909)
              ·
                refine ⟨11190690580112094574261091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29841841546965585531362909 11190690580112094574261091)
                ·
                  refine ⟨16786035870168141861391637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11190690580112094574261091 16786035870168141861391637)
                  ·
                    refine ⟨786845431414131649752733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16786035870168141861391637 786845431414131649752733)
                    ·
                      rfl

theorem cell23_4597128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_4597128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597128 prefixEnd_4597128 := by exact prefixLift 4597128
  have htrace : WordTrace (prefixWord ++ tailWord_4597128) baseStart_4597128 baseEnd_4597128 := by
    simpa [prefixWord, tailWord_4597128, baseEnd_4597128] using wordTrace_append hprefix tailTrace_4597128
  have hstable : (prefixWord ++ tailWord_4597128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597128).length < 2 ^ (prefixWord ++ tailWord_4597128).sum := by decide
  have hdescent : baseEnd_4597128 < baseStart_4597128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597141 : List Nat := [1, 3, 2, 1, 1, 2, 2, 11]
def baseStart_4597141 : Nat := 118140960795 + 4597141 * 2 ^ 59
def prefixEnd_4597141 : Nat := 4983230072969 + 3 ^ 40 * 4597141 * 2
def baseEnd_4597141 : Nat := 87427517388551977718357

theorem tailTrace_4597141 : CollatzResearch.WordTrace tailWord_4597141 prefixEnd_4597141 87427517388551977718357 := by
  unfold tailWord_4597141
  simp only [CollatzResearch.WordTrace]
  refine ⟨167671507038350761020583277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111781004692233840680388851 167671507038350761020583277)
  ·
    refine ⟨62876815139381535382718729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167671507038350761020583277 62876815139381535382718729)
    ·
      refine ⟨47157611354536151537039047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62876815139381535382718729 47157611354536151537039047)
      ·
        refine ⟨70736417031804227305558571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47157611354536151537039047 70736417031804227305558571)
        ·
          refine ⟨106104625547706340958337857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70736417031804227305558571 106104625547706340958337857)
          ·
            refine ⟨79578469160779755718753393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106104625547706340958337857 79578469160779755718753393)
            ·
              refine ⟨59683851870584816789065045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79578469160779755718753393 59683851870584816789065045)
              ·
                refine ⟨87427517388551977718357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59683851870584816789065045 87427517388551977718357)
                ·
                  rfl

theorem cell23_4597141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 11].length) (baseStart_4597141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597141 prefixEnd_4597141 := by exact prefixLift 4597141
  have htrace : WordTrace (prefixWord ++ tailWord_4597141) baseStart_4597141 baseEnd_4597141 := by
    simpa [prefixWord, tailWord_4597141, baseEnd_4597141] using wordTrace_append hprefix tailTrace_4597141
  have hstable : (prefixWord ++ tailWord_4597141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597141).length < 2 ^ (prefixWord ++ tailWord_4597141).sum := by decide
  have hdescent : baseEnd_4597141 < baseStart_4597141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597155 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 3]
def baseStart_4597155 : Nat := 118140960795 + 4597155 * 2 ^ 59
def prefixEnd_4597155 : Nat := 4983230072969 + 3 ^ 40 * 4597155 * 2
def baseEnd_4597155 : Nat := 2360550158220066343620575

theorem tailTrace_4597155 : CollatzResearch.WordTrace tailWord_4597155 prefixEnd_4597155 2360550158220066343620575 := by
  unfold tailWord_4597155
  simp only [CollatzResearch.WordTrace]
  refine ⟨167672017660300041411592919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111781345106866694274395279 167672017660300041411592919)
  ·
    refine ⟨251508026490450062117389379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167672017660300041411592919 251508026490450062117389379)
    ·
      refine ⟨377262039735675093176084069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251508026490450062117389379 377262039735675093176084069)
      ·
        refine ⟨70736632450439079970515763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377262039735675093176084069 70736632450439079970515763)
        ·
          refine ⟨106104948675658619955773645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70736632450439079970515763 106104948675658619955773645)
          ·
            refine ⟨39789355753371982483415117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106104948675658619955773645 39789355753371982483415117)
            ·
              refine ⟨14921008407514493431280669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39789355753371982483415117 14921008407514493431280669)
              ·
                refine ⟨5595378152817935036730251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14921008407514493431280669 5595378152817935036730251)
                ·
                  refine ⟨8393067229226902555095377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5595378152817935036730251 8393067229226902555095377)
                  ·
                    refine ⟨6294800421920176916321533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8393067229226902555095377 6294800421920176916321533)
                    ·
                      refine ⟨2360550158220066343620575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6294800421920176916321533 2360550158220066343620575)
                      ·
                        rfl

theorem cell23_4597155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_4597155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597155 prefixEnd_4597155 := by exact prefixLift 4597155
  have htrace : WordTrace (prefixWord ++ tailWord_4597155) baseStart_4597155 baseEnd_4597155 := by
    simpa [prefixWord, tailWord_4597155, baseEnd_4597155] using wordTrace_append hprefix tailTrace_4597155
  have hstable : (prefixWord ++ tailWord_4597155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597155).length < 2 ^ (prefixWord ++ tailWord_4597155).sum := by decide
  have hdescent : baseEnd_4597155 < baseStart_4597155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597161 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_4597161 : Nat := 118140960795 + 4597161 * 2 ^ 59
def prefixEnd_4597161 : Nat := 4983230072969 + 3 ^ 40 * 4597161 * 2
def baseEnd_4597161 : Nat := 2360553239103993320145547

theorem tailTrace_4597161 : CollatzResearch.WordTrace tailWord_4597161 prefixEnd_4597161 2360553239103993320145547 := by
  unfold tailWord_4597161
  simp only [CollatzResearch.WordTrace]
  refine ⟨167672236498278304436311337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111781490998852202957540891 167672236498278304436311337)
  ·
    refine ⟨125754177373708728327233503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167672236498278304436311337 125754177373708728327233503)
    ·
      refine ⟨188631266060563092490850255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125754177373708728327233503 188631266060563092490850255)
      ·
        refine ⟨282946899090844638736275383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188631266060563092490850255 282946899090844638736275383)
        ·
          refine ⟨424420348636266958104413075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282946899090844638736275383 424420348636266958104413075)
          ·
            refine ⟨636630522954400437156619613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424420348636266958104413075 636630522954400437156619613)
            ·
              refine ⟨238736446107900163933732355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 636630522954400437156619613 238736446107900163933732355)
              ·
                refine ⟨358104669161850245900598533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238736446107900163933732355 358104669161850245900598533)
                ·
                  refine ⟨67144625467846921106362225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 358104669161850245900598533 67144625467846921106362225)
                  ·
                    refine ⟨50358469100885190829771669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67144625467846921106362225 50358469100885190829771669)
                    ·
                      refine ⟨2360553239103993320145547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50358469100885190829771669 2360553239103993320145547)
                      ·
                        rfl

theorem cell23_4597161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_4597161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597161 prefixEnd_4597161 := by exact prefixLift 4597161
  have htrace : WordTrace (prefixWord ++ tailWord_4597161) baseStart_4597161 baseEnd_4597161 := by
    simpa [prefixWord, tailWord_4597161, baseEnd_4597161] using wordTrace_append hprefix tailTrace_4597161
  have hstable : (prefixWord ++ tailWord_4597161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597161).length < 2 ^ (prefixWord ++ tailWord_4597161).sum := by decide
  have hdescent : baseEnd_4597161 < baseStart_4597161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597169 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4597169 : Nat := 118140960795 + 4597169 * 2 ^ 59
def prefixEnd_4597169 : Nat := 4983230072969 + 3 ^ 40 * 4597169 * 2
def baseEnd_4597169 : Nat := 2360557346949229288845511

theorem tailTrace_4597169 : CollatzResearch.WordTrace tailWord_4597169 prefixEnd_4597169 2360557346949229288845511 := by
  unfold tailWord_4597169
  simp only [CollatzResearch.WordTrace]
  refine ⟨167672528282249321802602561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111781685521499547868401707 167672528282249321802602561)
  ·
    refine ⟨125754396211686991351951921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167672528282249321802602561 125754396211686991351951921)
    ·
      refine ⟨94315797158765243513963941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125754396211686991351951921 94315797158765243513963941)
      ·
        refine ⟨17684211967268483158868239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94315797158765243513963941 17684211967268483158868239)
        ·
          refine ⟨26526317950902724738302359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17684211967268483158868239 26526317950902724738302359)
          ·
            refine ⟨39789476926354087107453539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26526317950902724738302359 39789476926354087107453539)
            ·
              refine ⟨59684215389531130661180309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39789476926354087107453539 59684215389531130661180309)
              ·
                refine ⟨2797697596384271749742827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59684215389531130661180309 2797697596384271749742827)
                ·
                  refine ⟨4196546394576407624614241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797697596384271749742827 4196546394576407624614241)
                  ·
                    refine ⟨3147409795932305718460681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4196546394576407624614241 3147409795932305718460681)
                    ·
                      refine ⟨2360557346949229288845511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147409795932305718460681 2360557346949229288845511)
                      ·
                        rfl

theorem cell23_4597169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4597169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597169 prefixEnd_4597169 := by exact prefixLift 4597169
  have htrace : WordTrace (prefixWord ++ tailWord_4597169) baseStart_4597169 baseEnd_4597169 := by
    simpa [prefixWord, tailWord_4597169, baseEnd_4597169] using wordTrace_append hprefix tailTrace_4597169
  have hstable : (prefixWord ++ tailWord_4597169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597169).length < 2 ^ (prefixWord ++ tailWord_4597169).sum := by decide
  have hdescent : baseEnd_4597169 < baseStart_4597169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597171 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 9]
def baseStart_4597171 : Nat := 118140960795 + 4597171 * 2 ^ 59
def prefixEnd_4597171 : Nat := 4983230072969 + 3 ^ 40 * 4597171 * 2
def baseEnd_4597171 : Nat := 786852791303512760340167

theorem tailTrace_4597171 : CollatzResearch.WordTrace tailWord_4597171 prefixEnd_4597171 786852791303512760340167 := by
  unfold tailWord_4597171
  simp only [CollatzResearch.WordTrace]
  refine ⟨167672601228242076144175367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111781734152161384096116911 167672601228242076144175367)
  ·
    refine ⟨251508901842363114216263051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167672601228242076144175367 251508901842363114216263051)
    ·
      refine ⟨377263352763544671324394577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251508901842363114216263051 377263352763544671324394577)
      ·
        refine ⟨282947514572658503493295933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377263352763544671324394577 282947514572658503493295933)
        ·
          refine ⟨106105317964746938809985975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282947514572658503493295933 106105317964746938809985975)
          ·
            refine ⟨159157976947120408214978963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106105317964746938809985975 159157976947120408214978963)
            ·
              refine ⟨238736965420680612322468445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159157976947120408214978963 238736965420680612322468445)
              ·
                refine ⟨89526362032755229620925667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238736965420680612322468445 89526362032755229620925667)
                ·
                  refine ⟨134289543049132844431388501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89526362032755229620925667 134289543049132844431388501)
                  ·
                    refine ⟨786852791303512760340167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134289543049132844431388501 786852791303512760340167)
                    ·
                      rfl

theorem cell23_4597171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_4597171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597171 prefixEnd_4597171 := by exact prefixLift 4597171
  have htrace : WordTrace (prefixWord ++ tailWord_4597171) baseStart_4597171 baseEnd_4597171 := by
    simpa [prefixWord, tailWord_4597171, baseEnd_4597171] using wordTrace_append hprefix tailTrace_4597171
  have hstable : (prefixWord ++ tailWord_4597171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597171).length < 2 ^ (prefixWord ++ tailWord_4597171).sum := by decide
  have hdescent : baseEnd_4597171 < baseStart_4597171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597195 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 3, 3, 2]
def baseStart_4597195 : Nat := 118140960795 + 4597195 * 2 ^ 59
def prefixEnd_4597195 : Nat := 4983230072969 + 3 ^ 40 * 4597195 * 2
def baseEnd_4597195 : Nat := 2360570697446246187120391

theorem tailTrace_4597195 : CollatzResearch.WordTrace tailWord_4597195 prefixEnd_4597195 2360570697446246187120391 := by
  unfold tailWord_4597195
  simp only [CollatzResearch.WordTrace]
  refine ⟨167673476580155128243049039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111782317720103418828699359 167673476580155128243049039)
  ·
    refine ⟨251510214870232692364573559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167673476580155128243049039 251510214870232692364573559)
    ·
      refine ⟨377265322305349038546860339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251510214870232692364573559 377265322305349038546860339)
      ·
        refine ⟨565897983458023557820290509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377265322305349038546860339 565897983458023557820290509)
        ·
          refine ⟨212211743796758834182608941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565897983458023557820290509 212211743796758834182608941)
          ·
            refine ⟨79579403923784562818478353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212211743796758834182608941 79579403923784562818478353)
            ·
              refine ⟨59684552942838422113858765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79579403923784562818478353 59684552942838422113858765)
              ·
                refine ⟨22381707353564408292697037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59684552942838422113858765 22381707353564408292697037)
                ·
                  refine ⟨8393140257586653109761389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22381707353564408292697037 8393140257586653109761389)
                  ·
                    refine ⟨3147427596594994916160521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8393140257586653109761389 3147427596594994916160521)
                    ·
                      refine ⟨2360570697446246187120391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147427596594994916160521 2360570697446246187120391)
                      ·
                        rfl

theorem cell23_4597195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3, 2].length) (baseStart_4597195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597195 prefixEnd_4597195 := by exact prefixLift 4597195
  have htrace : WordTrace (prefixWord ++ tailWord_4597195) baseStart_4597195 baseEnd_4597195 := by
    simpa [prefixWord, tailWord_4597195, baseEnd_4597195] using wordTrace_append hprefix tailTrace_4597195
  have hstable : (prefixWord ++ tailWord_4597195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597195).length < 2 ^ (prefixWord ++ tailWord_4597195).sum := by decide
  have hdescent : baseEnd_4597195 < baseStart_4597195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597198 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4597198 : Nat := 118140960795 + 4597198 * 2 ^ 59
def prefixEnd_4597198 : Nat := 4983230072969 + 3 ^ 40 * 4597198 * 2
def baseEnd_4597198 : Nat := 2360572237888209675382877

theorem tailTrace_4597198 : CollatzResearch.WordTrace tailWord_4597198 prefixEnd_4597198 2360572237888209675382877 := by
  unfold tailWord_4597198
  simp only [CollatzResearch.WordTrace]
  refine ⟨20959198249893032469426031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111782390666096173170272165 20959198249893032469426031)
  ·
    refine ⟨31438797374839548704139047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20959198249893032469426031 31438797374839548704139047)
    ·
      refine ⟨47158196062259323056208571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31438797374839548704139047 47158196062259323056208571)
      ·
        refine ⟨70737294093388984584312857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47158196062259323056208571 70737294093388984584312857)
        ·
          refine ⟨53052970570041738438234643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70737294093388984584312857 53052970570041738438234643)
          ·
            refine ⟨79579455855062607657351965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53052970570041738438234643 79579455855062607657351965)
            ·
              refine ⟨29842295945648477871506987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79579455855062607657351965 29842295945648477871506987)
              ·
                refine ⟨44763443918472716807260481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29842295945648477871506987 44763443918472716807260481)
                ·
                  refine ⟨33572582938854537605445361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44763443918472716807260481 33572582938854537605445361)
                  ·
                    refine ⟨25179437204140903204084021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33572582938854537605445361 25179437204140903204084021)
                    ·
                      refine ⟨2360572237888209675382877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25179437204140903204084021 2360572237888209675382877)
                      ·
                        rfl

theorem cell23_4597198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4597198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597198 prefixEnd_4597198 := by exact prefixLift 4597198
  have htrace : WordTrace (prefixWord ++ tailWord_4597198) baseStart_4597198 baseEnd_4597198 := by
    simpa [prefixWord, tailWord_4597198, baseEnd_4597198] using wordTrace_append hprefix tailTrace_4597198
  have hstable : (prefixWord ++ tailWord_4597198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597198).length < 2 ^ (prefixWord ++ tailWord_4597198).sum := by decide
  have hdescent : baseEnd_4597198 < baseStart_4597198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597246 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4597246 : Nat := 118140960795 + 4597246 * 2 ^ 59
def prefixEnd_4597246 : Nat := 4983230072969 + 3 ^ 40 * 4597246 * 2
def baseEnd_4597246 : Nat := 2360596884959625487582657

theorem tailTrace_4597246 : CollatzResearch.WordTrace tailWord_4597246 prefixEnd_4597246 2360596884959625487582657 := by
  unfold tailWord_4597246
  simp only [CollatzResearch.WordTrace]
  refine ⟨20959417087871295494144449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111783557801980242635437061 20959417087871295494144449)
  ·
    refine ⟨15719562815903471620608337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20959417087871295494144449 15719562815903471620608337)
    ·
      refine ⟨11789672111927603715456253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15719562815903471620608337 11789672111927603715456253)
      ·
        refine ⟨4421127041972851393296095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11789672111927603715456253 4421127041972851393296095)
        ·
          refine ⟨6631690562959277089944143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4421127041972851393296095 6631690562959277089944143)
          ·
            refine ⟨9947535844438915634916215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631690562959277089944143 9947535844438915634916215)
            ·
              refine ⟨14921303766658373452374323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9947535844438915634916215 14921303766658373452374323)
              ·
                refine ⟨22381955649987560178561485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14921303766658373452374323 22381955649987560178561485)
                ·
                  refine ⟨8393233368745335066960557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22381955649987560178561485 8393233368745335066960557)
                  ·
                    refine ⟨3147462513279500650110209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8393233368745335066960557 3147462513279500650110209)
                    ·
                      refine ⟨2360596884959625487582657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147462513279500650110209 2360596884959625487582657)
                      ·
                        rfl

theorem cell23_4597246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4597246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597246 prefixEnd_4597246 := by exact prefixLift 4597246
  have htrace : WordTrace (prefixWord ++ tailWord_4597246) baseStart_4597246 baseEnd_4597246 := by
    simpa [prefixWord, tailWord_4597246, baseEnd_4597246] using wordTrace_append hprefix tailTrace_4597246
  have hstable : (prefixWord ++ tailWord_4597246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597246).length < 2 ^ (prefixWord ++ tailWord_4597246).sum := by decide
  have hdescent : baseEnd_4597246 < baseStart_4597246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597265 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 5]
def baseStart_4597265 : Nat := 118140960795 + 4597265 * 2 ^ 59
def prefixEnd_4597265 : Nat := 4983230072969 + 3 ^ 40 * 4597265 * 2
def baseEnd_4597265 : Nat := 262289626788006768138341

theorem tailTrace_4597265 : CollatzResearch.WordTrace tailWord_4597265 prefixEnd_4597265 262289626788006768138341 := by
  unfold tailWord_4597265
  simp only [CollatzResearch.WordTrace]
  refine ⟨167676029689901530198097249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111784019793267686798731499 167676029689901530198097249)
  ·
    refine ⟨125757022267426147648572937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167676029689901530198097249 125757022267426147648572937)
    ·
      refine ⟨94317766700569610736429703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125757022267426147648572937 94317766700569610736429703)
      ·
        refine ⟨141476650050854416104644555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94317766700569610736429703 141476650050854416104644555)
        ·
          refine ⟨212214975076281624156966833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141476650050854416104644555 212214975076281624156966833)
          ·
            refine ⟨159161231307211218117725125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212214975076281624156966833 159161231307211218117725125)
            ·
              refine ⟨29842730870102103397073461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159161231307211218117725125 29842730870102103397073461)
              ·
                refine ⟨2797756019072072193475637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29842730870102103397073461 2797756019072072193475637)
                ·
                  refine ⟨262289626788006768138341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2797756019072072193475637 262289626788006768138341)
                  ·
                    rfl

theorem cell23_4597265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 5].length) (baseStart_4597265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597265 prefixEnd_4597265 := by exact prefixLift 4597265
  have htrace : WordTrace (prefixWord ++ tailWord_4597265) baseStart_4597265 baseEnd_4597265 := by
    simpa [prefixWord, tailWord_4597265, baseEnd_4597265] using wordTrace_append hprefix tailTrace_4597265
  have hstable : (prefixWord ++ tailWord_4597265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597265).length < 2 ^ (prefixWord ++ tailWord_4597265).sum := by decide
  have hdescent : baseEnd_4597265 < baseStart_4597265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597328 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_4597328 : Nat := 118140960795 + 4597328 * 2 ^ 59
def prefixEnd_4597328 : Nat := 4983230072969 + 3 ^ 40 * 4597328 * 2
def baseEnd_4597328 : Nat := 2360638990373294166757279

theorem tailTrace_4597328 : CollatzResearch.WordTrace tailWord_4597328 prefixEnd_4597328 2360638990373294166757279 := by
  unfold tailWord_4597328
  simp only [CollatzResearch.WordTrace]
  refine ⟨83839163744336645978820319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111785551659115527971760425 83839163744336645978820319)
  ·
    refine ⟨125758745616504968968230479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83839163744336645978820319 125758745616504968968230479)
    ·
      refine ⟨188638118424757453452345719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125758745616504968968230479 188638118424757453452345719)
      ·
        refine ⟨282957177637136180178518579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188638118424757453452345719 282957177637136180178518579)
        ·
          refine ⟨424435766455704270267777869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282957177637136180178518579 424435766455704270267777869)
          ·
            refine ⟨159163412420889101350416701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424435766455704270267777869 159163412420889101350416701)
            ·
              refine ⟨59686279657833413006406263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159163412420889101350416701 59686279657833413006406263)
              ·
                refine ⟨89529419486750119509609395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59686279657833413006406263 89529419486750119509609395)
                ·
                  refine ⟨134294129230125179264414093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89529419486750119509609395 134294129230125179264414093)
                  ·
                    refine ⟨50360298461296942224155285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134294129230125179264414093 50360298461296942224155285)
                    ·
                      refine ⟨2360638990373294166757279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50360298461296942224155285 2360638990373294166757279)
                      ·
                        rfl

theorem cell23_4597328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_4597328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597328 prefixEnd_4597328 := by exact prefixLift 4597328
  have htrace : WordTrace (prefixWord ++ tailWord_4597328) baseStart_4597328 baseEnd_4597328 := by
    simpa [prefixWord, tailWord_4597328, baseEnd_4597328] using wordTrace_append hprefix tailTrace_4597328
  have hstable : (prefixWord ++ tailWord_4597328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597328).length < 2 ^ (prefixWord ++ tailWord_4597328).sum := by decide
  have hdescent : baseEnd_4597328 < baseStart_4597328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597332 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_4597332 : Nat := 118140960795 + 4597332 * 2 ^ 59
def prefixEnd_4597332 : Nat := 4983230072969 + 3 ^ 40 * 4597332 * 2
def baseEnd_4597332 : Nat := 2360641044295912151107261

theorem tailTrace_4597332 : CollatzResearch.WordTrace tailWord_4597332 prefixEnd_4597332 2360641044295912151107261 := by
  unfold tailWord_4597332
  simp only [CollatzResearch.WordTrace]
  refine ⟨83839236690329400320393125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111785648920439200427190833 83839236690329400320393125)
  ·
    refine ⟨15719856879436762560073711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83839236690329400320393125 15719856879436762560073711)
    ·
      refine ⟨23579785319155143840110567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719856879436762560073711 23579785319155143840110567)
      ·
        refine ⟨35369677978732715760165851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23579785319155143840110567 35369677978732715760165851)
        ·
          refine ⟨53054516968099073640248777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35369677978732715760165851 53054516968099073640248777)
          ·
            refine ⟨39790887726074305230186583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53054516968099073640248777 39790887726074305230186583)
            ·
              refine ⟨59686331589111457845279875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39790887726074305230186583 59686331589111457845279875)
              ·
                refine ⟨89529497383667186767919813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59686331589111457845279875 89529497383667186767919813)
                ·
                  refine ⟨16786780759437597518984965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89529497383667186767919813 16786780759437597518984965)
                  ·
                    refine ⟨3147521392394549534809681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16786780759437597518984965 3147521392394549534809681)
                    ·
                      refine ⟨2360641044295912151107261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147521392394549534809681 2360641044295912151107261)
                      ·
                        rfl

theorem cell23_4597332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_4597332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597332 prefixEnd_4597332 := by exact prefixLift 4597332
  have htrace : WordTrace (prefixWord ++ tailWord_4597332) baseStart_4597332 baseEnd_4597332 := by
    simpa [prefixWord, tailWord_4597332, baseEnd_4597332] using wordTrace_append hprefix tailTrace_4597332
  have hstable : (prefixWord ++ tailWord_4597332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597332).length < 2 ^ (prefixWord ++ tailWord_4597332).sum := by decide
  have hdescent : baseEnd_4597332 < baseStart_4597332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597352 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4597352 : Nat := 118140960795 + 4597352 * 2 ^ 59
def prefixEnd_4597352 : Nat := 4983230072969 + 3 ^ 40 * 4597352 * 2
def baseEnd_4597352 : Nat := 2360651313909002072857169

theorem tailTrace_4597352 : CollatzResearch.WordTrace tailWord_4597352 prefixEnd_4597352 2360651313909002072857169 := by
  unfold tailWord_4597352
  simp only [CollatzResearch.WordTrace]
  refine ⟨83839601420293172028257155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111786135227057562704342873 83839601420293172028257155)
  ·
    refine ⟨125759402130439758042385733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83839601420293172028257155 125759402130439758042385733)
    ·
      refine ⟨23579887899457454632947325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125759402130439758042385733 23579887899457454632947325)
      ·
        refine ⟨8842457962296545487355247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23579887899457454632947325 8842457962296545487355247)
        ·
          refine ⟨13263686943444818231032871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8842457962296545487355247 13263686943444818231032871)
          ·
            refine ⟨19895530415167227346549307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13263686943444818231032871 19895530415167227346549307)
            ·
              refine ⟨29843295622750841019823961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19895530415167227346549307 29843295622750841019823961)
              ·
                refine ⟨22382471717063130764867971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29843295622750841019823961 22382471717063130764867971)
                ·
                  refine ⟨33573707575594696147301957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22382471717063130764867971 33573707575594696147301957)
                  ·
                    refine ⟨6295070170424005527619117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33573707575594696147301957 6295070170424005527619117)
                    ·
                      refine ⟨2360651313909002072857169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295070170424005527619117 2360651313909002072857169)
                      ·
                        rfl

theorem cell23_4597352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4597352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597352 prefixEnd_4597352 := by exact prefixLift 4597352
  have htrace : WordTrace (prefixWord ++ tailWord_4597352) baseStart_4597352 baseEnd_4597352 := by
    simpa [prefixWord, tailWord_4597352, baseEnd_4597352] using wordTrace_append hprefix tailTrace_4597352
  have hstable : (prefixWord ++ tailWord_4597352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597352).length < 2 ^ (prefixWord ++ tailWord_4597352).sum := by decide
  have hdescent : baseEnd_4597352 < baseStart_4597352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597399 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_4597399 : Nat := 118140960795 + 4597399 * 2 ^ 59
def prefixEnd_4597399 : Nat := 4983230072969 + 3 ^ 40 * 4597399 * 2
def baseEnd_4597399 : Nat := 2360675447499763388969453

theorem tailTrace_4597399 : CollatzResearch.WordTrace tailWord_4597399 prefixEnd_4597399 2360675447499763388969453 := by
  unfold tailWord_4597399
  simp only [CollatzResearch.WordTrace]
  refine ⟨167680917071416071083475251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111787278047610714055650167 167680917071416071083475251)
  ·
    refine ⟨251521375607124106625212877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167680917071416071083475251 251521375607124106625212877)
    ·
      refine ⟨94320515852671539984454829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251521375607124106625212877 94320515852671539984454829)
      ·
        refine ⟨35370193444751827494170561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94320515852671539984454829 35370193444751827494170561)
        ·
          refine ⟨26527645083563870620627921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35370193444751827494170561 26527645083563870620627921)
          ·
            refine ⟨19895733812672902965470941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26527645083563870620627921 19895733812672902965470941)
            ·
              refine ⟨7460900179752338612051603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19895733812672902965470941 7460900179752338612051603)
              ·
                refine ⟨11191350269628507918077405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7460900179752338612051603 11191350269628507918077405)
                ·
                  refine ⟨4196756351110690469279027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11191350269628507918077405 4196756351110690469279027)
                  ·
                    refine ⟨6295134526666035703918541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196756351110690469279027 6295134526666035703918541)
                    ·
                      refine ⟨2360675447499763388969453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295134526666035703918541 2360675447499763388969453)
                      ·
                        rfl

theorem cell23_4597399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_4597399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597399 prefixEnd_4597399 := by exact prefixLift 4597399
  have htrace : WordTrace (prefixWord ++ tailWord_4597399) baseStart_4597399 baseEnd_4597399 := by
    simpa [prefixWord, tailWord_4597399, baseEnd_4597399] using wordTrace_append hprefix tailTrace_4597399
  have hstable : (prefixWord ++ tailWord_4597399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597399).length < 2 ^ (prefixWord ++ tailWord_4597399).sum := by decide
  have hdescent : baseEnd_4597399 < baseStart_4597399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597405 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4597405 : Nat := 118140960795 + 4597405 * 2 ^ 59
def prefixEnd_4597405 : Nat := 4983230072969 + 3 ^ 40 * 4597405 * 2
def baseEnd_4597405 : Nat := 2360678528383690365494425

theorem tailTrace_4597405 : CollatzResearch.WordTrace tailWord_4597405 prefixEnd_4597405 2360678528383690365494425 := by
  unfold tailWord_4597405
  simp only [CollatzResearch.WordTrace]
  refine ⟨167681135909394334108193669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111787423939596222738795779 167681135909394334108193669)
  ·
    refine ⟨31440212983011437645286313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167681135909394334108193669 31440212983011437645286313)
    ·
      refine ⟨23580159737258578233964735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31440212983011437645286313 23580159737258578233964735)
      ·
        refine ⟨35370239605887867350947103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23580159737258578233964735 35370239605887867350947103)
        ·
          refine ⟨53055359408831801026420655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35370239605887867350947103 53055359408831801026420655)
          ·
            refine ⟨79583039113247701539630983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53055359408831801026420655 79583039113247701539630983)
            ·
              refine ⟨119374558669871552309446475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79583039113247701539630983 119374558669871552309446475)
              ·
                refine ⟨179061838004807328464169713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119374558669871552309446475 179061838004807328464169713)
                ·
                  refine ⟨134296378503605496348127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179061838004807328464169713 134296378503605496348127285)
                  ·
                    refine ⟨12590285484713015282636933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134296378503605496348127285 12590285484713015282636933)
                    ·
                      refine ⟨2360678528383690365494425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12590285484713015282636933 2360678528383690365494425)
                      ·
                        rfl

theorem cell23_4597405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4597405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597405 prefixEnd_4597405 := by exact prefixLift 4597405
  have htrace : WordTrace (prefixWord ++ tailWord_4597405) baseStart_4597405 baseEnd_4597405 := by
    simpa [prefixWord, tailWord_4597405, baseEnd_4597405] using wordTrace_append hprefix tailTrace_4597405
  have hstable : (prefixWord ++ tailWord_4597405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597405).length < 2 ^ (prefixWord ++ tailWord_4597405).sum := by decide
  have hdescent : baseEnd_4597405 < baseStart_4597405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597406 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_4597406 : Nat := 118140960795 + 4597406 * 2 ^ 59
def prefixEnd_4597406 : Nat := 4983230072969 + 3 ^ 40 * 4597406 * 2
def baseEnd_4597406 : Nat := 262297671318260540175769

theorem tailTrace_4597406 : CollatzResearch.WordTrace tailWord_4597406 prefixEnd_4597406 262297671318260540175769 := by
  unfold tailWord_4597406
  simp only [CollatzResearch.WordTrace]
  refine ⟨20960146547798838909872509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111787448254927140852653381 20960146547798838909872509)
  ·
    refine ⟨7860054955424564591202191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20960146547798838909872509 7860054955424564591202191)
    ·
      refine ⟨11790082433136846886803287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860054955424564591202191 11790082433136846886803287)
      ·
        refine ⟨17685123649705270330204931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11790082433136846886803287 17685123649705270330204931)
        ·
          refine ⟨26527685474557905495307397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17685123649705270330204931 26527685474557905495307397)
          ·
            refine ⟨4973941026479607280370137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26527685474557905495307397 4973941026479607280370137)
            ·
              refine ⟨3730455769859705460277603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4973941026479607280370137 3730455769859705460277603)
              ·
                refine ⟨5595683654789558190416405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730455769859705460277603 5595683654789558190416405)
                ·
                  refine ⟨262297671318260540175769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5595683654789558190416405 262297671318260540175769)
                  ·
                    rfl

theorem cell23_4597406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_4597406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597406 prefixEnd_4597406 := by exact prefixLift 4597406
  have htrace : WordTrace (prefixWord ++ tailWord_4597406) baseStart_4597406 baseEnd_4597406 := by
    simpa [prefixWord, tailWord_4597406, baseEnd_4597406] using wordTrace_append hprefix tailTrace_4597406
  have hstable : (prefixWord ++ tailWord_4597406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597406).length < 2 ^ (prefixWord ++ tailWord_4597406).sum := by decide
  have hdescent : baseEnd_4597406 < baseStart_4597406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597439 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 1, 1, 4]
def baseStart_4597439 : Nat := 118140960795 + 4597439 * 2 ^ 59
def prefixEnd_4597439 : Nat := 4983230072969 + 3 ^ 40 * 4597439 * 2
def baseEnd_4597439 : Nat := 2360695986725943232469269

theorem tailTrace_4597439 : CollatzResearch.WordTrace tailWord_4597439 prefixEnd_4597439 2360695986725943232469269 := by
  unfold tailWord_4597439
  simp only [CollatzResearch.WordTrace]
  refine ⟨167682375991271157914931371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111788250660847438609954247 167682375991271157914931371)
  ·
    refine ⟨251523563986906736872397057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167682375991271157914931371 251523563986906736872397057)
    ·
      refine ⟨188642672990180052654297793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251523563986906736872397057 188642672990180052654297793)
      ·
        refine ⟨141482004742635039490723345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188642672990180052654297793 141482004742635039490723345)
        ·
          refine ⟨106111503556976279618042509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141482004742635039490723345 106111503556976279618042509)
          ·
            refine ⟨39791813833866104856765941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106111503556976279618042509 39791813833866104856765941)
            ·
              refine ⟨3730482546924947330321807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39791813833866104856765941 3730482546924947330321807)
              ·
                refine ⟨5595723820387420995482711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730482546924947330321807 5595723820387420995482711)
                ·
                  refine ⟨8393585730581131493224067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5595723820387420995482711 8393585730581131493224067)
                  ·
                    refine ⟨12590378595871697239836101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8393585730581131493224067 12590378595871697239836101)
                    ·
                      refine ⟨2360695986725943232469269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12590378595871697239836101 2360695986725943232469269)
                      ·
                        rfl

theorem cell23_4597439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_4597439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597439 prefixEnd_4597439 := by exact prefixLift 4597439
  have htrace : WordTrace (prefixWord ++ tailWord_4597439) baseStart_4597439 baseEnd_4597439 := by
    simpa [prefixWord, tailWord_4597439, baseEnd_4597439] using wordTrace_append hprefix tailTrace_4597439
  have hstable : (prefixWord ++ tailWord_4597439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597439).length < 2 ^ (prefixWord ++ tailWord_4597439).sum := by decide
  have hdescent : baseEnd_4597439 < baseStart_4597439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597450 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_4597450 : Nat := 118140960795 + 4597450 * 2 ^ 59
def prefixEnd_4597450 : Nat := 4983230072969 + 3 ^ 40 * 4597450 * 2
def baseEnd_4597450 : Nat := 2360701635013142689431719

theorem tailTrace_4597450 : CollatzResearch.WordTrace tailWord_4597450 prefixEnd_4597450 2360701635013142689431719 := by
  unfold tailWord_4597450
  simp only [CollatzResearch.WordTrace]
  refine ⟨41920694298557826698395451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111788518129487537862387869 41920694298557826698395451)
  ·
    refine ⟨62881041447836740047593177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41920694298557826698395451 62881041447836740047593177)
    ·
      refine ⟨47160781085877555035694883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62881041447836740047593177 47160781085877555035694883)
      ·
        refine ⟨70741171628816332553542325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47160781085877555035694883 70741171628816332553542325)
        ·
          refine ⟨6631984840201531176894593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70741171628816332553542325 6631984840201531176894593)
          ·
            refine ⟨4973988630151148382670945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6631984840201531176894593 4973988630151148382670945)
            ·
              refine ⟨3730491472613361287003209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4973988630151148382670945 3730491472613361287003209)
              ·
                refine ⟨2797868604460020965252407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3730491472613361287003209 2797868604460020965252407)
                ·
                  refine ⟨4196802906690031447878611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797868604460020965252407 4196802906690031447878611)
                  ·
                    refine ⟨6295204360035047171817917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196802906690031447878611 6295204360035047171817917)
                    ·
                      refine ⟨2360701635013142689431719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295204360035047171817917 2360701635013142689431719)
                      ·
                        rfl

theorem cell23_4597450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_4597450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597450 prefixEnd_4597450 := by exact prefixLift 4597450
  have htrace : WordTrace (prefixWord ++ tailWord_4597450) baseStart_4597450 baseEnd_4597450 := by
    simpa [prefixWord, tailWord_4597450, baseEnd_4597450] using wordTrace_append hprefix tailTrace_4597450
  have hstable : (prefixWord ++ tailWord_4597450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597450).length < 2 ^ (prefixWord ++ tailWord_4597450).sum := by decide
  have hdescent : baseEnd_4597450 < baseStart_4597450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597472 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_4597472 : Nat := 118140960795 + 4597472 * 2 ^ 59
def prefixEnd_4597472 : Nat := 4983230072969 + 3 ^ 40 * 4597472 * 2
def baseEnd_4597472 : Nat := 2360712931587541603356617

theorem tailTrace_4597472 : CollatzResearch.WordTrace tailWord_4597472 prefixEnd_4597472 2360712931587541603356617 := by
  unfold tailWord_4597472
  simp only [CollatzResearch.WordTrace]
  refine ⟨83841789800075802275441335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111789053066767736367255113 83841789800075802275441335)
  ·
    refine ⟨125762684700113703413162003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83841789800075802275441335 125762684700113703413162003)
    ·
      refine ⟨188644027050170555119743005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125762684700113703413162003 188644027050170555119743005)
      ·
        refine ⟨70741510143813958169903627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188644027050170555119743005 70741510143813958169903627)
        ·
          refine ⟨106112265215720937254855441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70741510143813958169903627 106112265215720937254855441)
          ·
            refine ⟨79584198911790702941141581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106112265215720937254855441 79584198911790702941141581)
            ·
              refine ⟨29844074591921513602928093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79584198911790702941141581 29844074591921513602928093)
              ·
                refine ⟨11191527971970567601098035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29844074591921513602928093 11191527971970567601098035)
                ·
                  refine ⟨16787291957955851401647053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11191527971970567601098035 16787291957955851401647053)
                  ·
                    refine ⟨6295234484233444275617645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16787291957955851401647053 6295234484233444275617645)
                    ·
                      refine ⟨2360712931587541603356617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295234484233444275617645 2360712931587541603356617)
                      ·
                        rfl

theorem cell23_4597472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_4597472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597472 prefixEnd_4597472 := by exact prefixLift 4597472
  have htrace : WordTrace (prefixWord ++ tailWord_4597472) baseStart_4597472 baseEnd_4597472 := by
    simpa [prefixWord, tailWord_4597472, baseEnd_4597472] using wordTrace_append hprefix tailTrace_4597472
  have hstable : (prefixWord ++ tailWord_4597472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597472).length < 2 ^ (prefixWord ++ tailWord_4597472).sum := by decide
  have hdescent : baseEnd_4597472 < baseStart_4597472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597506 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_4597506 : Nat := 118140960795 + 4597506 * 2 ^ 59
def prefixEnd_4597506 : Nat := 4983230072969 + 3 ^ 40 * 4597506 * 2
def baseEnd_4597506 : Nat := 2360730389929794470331461

theorem tailTrace_4597506 : CollatzResearch.WordTrace tailWord_4597506 prefixEnd_4597506 2360730389929794470331461 := by
  unfold tailWord_4597506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41921204920507107089405093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111789879788018952238413581 41921204920507107089405093)
  ·
    refine ⟨7860225922595082579263455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41921204920507107089405093 7860225922595082579263455)
    ·
      refine ⟨11790338883892623868895183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860225922595082579263455 11790338883892623868895183)
      ·
        refine ⟨17685508325838935803342775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11790338883892623868895183 17685508325838935803342775)
        ·
          refine ⟨26528262488758403705014163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17685508325838935803342775 26528262488758403705014163)
          ·
            refine ⟨39792393733137605557521245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26528262488758403705014163 39792393733137605557521245)
            ·
              refine ⟨14922147649926602084070467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39792393733137605557521245 14922147649926602084070467)
              ·
                refine ⟨22383221474889903126105701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14922147649926602084070467 22383221474889903126105701)
                ·
                  refine ⟨4196854026541856836144819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22383221474889903126105701 4196854026541856836144819)
                  ·
                    refine ⟨6295281039812785254217229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196854026541856836144819 6295281039812785254217229)
                    ·
                      refine ⟨2360730389929794470331461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295281039812785254217229 2360730389929794470331461)
                      ·
                        rfl

theorem cell23_4597506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_4597506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597506 prefixEnd_4597506 := by exact prefixLift 4597506
  have htrace : WordTrace (prefixWord ++ tailWord_4597506) baseStart_4597506 baseEnd_4597506 := by
    simpa [prefixWord, tailWord_4597506, baseEnd_4597506] using wordTrace_append hprefix tailTrace_4597506
  have hstable : (prefixWord ++ tailWord_4597506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597506).length < 2 ^ (prefixWord ++ tailWord_4597506).sum := by decide
  have hdescent : baseEnd_4597506 < baseStart_4597506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597517 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4597517 : Nat := 118140960795 + 4597517 * 2 ^ 59
def prefixEnd_4597517 : Nat := 4983230072969 + 3 ^ 40 * 4597517 * 2
def baseEnd_4597517 : Nat := 786912012738997975764637

theorem tailTrace_4597517 : CollatzResearch.WordTrace tailWord_4597517 prefixEnd_4597517 786912012738997975764637 := by
  unfold tailWord_4597517
  simp only [CollatzResearch.WordTrace]
  refine ⟨167685220884988577236270805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111790147256659051490847203 167685220884988577236270805)
  ·
    refine ⟨3930122364491919778975097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 167685220884988577236270805 3930122364491919778975097)
    ·
      refine ⟨2947591773368939834231323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3930122364491919778975097 2947591773368939834231323)
      ·
        refine ⟨4421387660053409751346985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947591773368939834231323 4421387660053409751346985)
        ·
          refine ⟨3316040745040057313510239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4421387660053409751346985 3316040745040057313510239)
          ·
            refine ⟨4974061117560085970265359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316040745040057313510239 4974061117560085970265359)
            ·
              refine ⟨7461091676340128955398039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974061117560085970265359 7461091676340128955398039)
              ·
                refine ⟨11191637514510193433097059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461091676340128955398039 11191637514510193433097059)
                ·
                  refine ⟨16787456271765290149645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11191637514510193433097059 16787456271765290149645589)
                  ·
                    refine ⟨786912012738997975764637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16787456271765290149645589 786912012738997975764637)
                    ·
                      rfl

theorem cell23_4597517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4597517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597517 prefixEnd_4597517 := by exact prefixLift 4597517
  have htrace : WordTrace (prefixWord ++ tailWord_4597517) baseStart_4597517 baseEnd_4597517 := by
    simpa [prefixWord, tailWord_4597517, baseEnd_4597517] using wordTrace_append hprefix tailTrace_4597517
  have hstable : (prefixWord ++ tailWord_4597517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597517).length < 2 ^ (prefixWord ++ tailWord_4597517).sum := by decide
  have hdescent : baseEnd_4597517 < baseStart_4597517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597532 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4597532 : Nat := 118140960795 + 4597532 * 2 ^ 59
def prefixEnd_4597532 : Nat := 4983230072969 + 3 ^ 40 * 4597532 * 2
def baseEnd_4597532 : Nat := 2360743740426811368606341

theorem tailTrace_4597532 : CollatzResearch.WordTrace tailWord_4597532 prefixEnd_4597532 2360743740426811368606341 := by
  unfold tailWord_4597532
  simp only [CollatzResearch.WordTrace]
  refine ⟨83842883989967117399033425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111790511986622823198711233 83842883989967117399033425)
  ·
    refine ⟨62882162992475338049275069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83842883989967117399033425 62882162992475338049275069)
    ·
      refine ⟨23580811122178251768478151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62882162992475338049275069 23580811122178251768478151)
      ·
        refine ⟨35371216683267377652717227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23580811122178251768478151 35371216683267377652717227)
        ·
          refine ⟨53056825024901066479075841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35371216683267377652717227 53056825024901066479075841)
          ·
            refine ⟨39792618768675799859306881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53056825024901066479075841 39792618768675799859306881)
            ·
              refine ⟨29844464076506849894480161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39792618768675799859306881 29844464076506849894480161)
              ·
                refine ⟨22383348057380137420860121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29844464076506849894480161 22383348057380137420860121)
                ·
                  refine ⟨16787511043035103065645091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22383348057380137420860121 16787511043035103065645091)
                  ·
                    refine ⟨25181266564552654598467637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16787511043035103065645091 25181266564552654598467637)
                    ·
                      refine ⟨2360743740426811368606341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25181266564552654598467637 2360743740426811368606341)
                      ·
                        rfl

theorem cell23_4597532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4597532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597532 prefixEnd_4597532 := by exact prefixLift 4597532
  have htrace : WordTrace (prefixWord ++ tailWord_4597532) baseStart_4597532 baseEnd_4597532 := by
    simpa [prefixWord, tailWord_4597532, baseEnd_4597532] using wordTrace_append hprefix tailTrace_4597532
  have hstable : (prefixWord ++ tailWord_4597532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597532).length < 2 ^ (prefixWord ++ tailWord_4597532).sum := by decide
  have hdescent : baseEnd_4597532 < baseStart_4597532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597545 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_4597545 : Nat := 118140960795 + 4597545 * 2 ^ 59
def prefixEnd_4597545 : Nat := 4983230072969 + 3 ^ 40 * 4597545 * 2
def baseEnd_4597545 : Nat := 2360750415675319817743781

theorem tailTrace_4597545 : CollatzResearch.WordTrace tailWord_4597545 prefixEnd_4597545 2360750415675319817743781 := by
  unfold tailWord_4597545
  simp only [CollatzResearch.WordTrace]
  refine ⟨167686242128887138018290089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111790828085924758678860059 167686242128887138018290089)
  ·
    refine ⟨125764681596665353513717567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167686242128887138018290089 125764681596665353513717567)
    ·
      refine ⟨188647022394998030270576351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125764681596665353513717567 188647022394998030270576351)
      ·
        refine ⟨282970533592497045405864527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188647022394998030270576351 282970533592497045405864527)
        ·
          refine ⟨424455800388745568108796791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282970533592497045405864527 424455800388745568108796791)
          ·
            refine ⟨636683700583118352163195187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424455800388745568108796791 636683700583118352163195187)
            ·
              refine ⟨955025550874677528244792781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636683700583118352163195187 955025550874677528244792781)
              ·
                refine ⟨358134581578004073091797293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955025550874677528244792781 358134581578004073091797293)
                ·
                  refine ⟨134300468091751527409423985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358134581578004073091797293 134300468091751527409423985)
                  ·
                    refine ⟨100725351068813645557067989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134300468091751527409423985 100725351068813645557067989)
                    ·
                      refine ⟨2360750415675319817743781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100725351068813645557067989 2360750415675319817743781)
                      ·
                        rfl

theorem cell23_4597545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_4597545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597545 prefixEnd_4597545 := by exact prefixLift 4597545
  have htrace : WordTrace (prefixWord ++ tailWord_4597545) baseStart_4597545 baseEnd_4597545 := by
    simpa [prefixWord, tailWord_4597545, baseEnd_4597545] using wordTrace_append hprefix tailTrace_4597545
  have hstable : (prefixWord ++ tailWord_4597545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597545).length < 2 ^ (prefixWord ++ tailWord_4597545).sum := by decide
  have hdescent : baseEnd_4597545 < baseStart_4597545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597599 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 2, 5]
def baseStart_4597599 : Nat := 118140960795 + 4597599 * 2 ^ 59
def prefixEnd_4597599 : Nat := 4983230072969 + 3 ^ 40 * 4597599 * 2
def baseEnd_4597599 : Nat := 786926047876887535489511

theorem tailTrace_4597599 : CollatzResearch.WordTrace tailWord_4597599 prefixEnd_4597599 786926047876887535489511 := by
  unfold tailWord_4597599
  simp only [CollatzResearch.WordTrace]
  refine ⟨167688211670691505240755851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111792141113794336827170567 167688211670691505240755851)
  ·
    refine ⟨251532317506037257861133777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167688211670691505240755851 251532317506037257861133777)
    ·
      refine ⟨188649238129527943395850333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251532317506037257861133777 188649238129527943395850333)
      ·
        refine ⟨70743464298572978773443875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188649238129527943395850333 70743464298572978773443875)
        ·
          refine ⟨106115196447859468160165813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70743464298572978773443875 106115196447859468160165813)
          ·
            refine ⟨9948299666986825140015545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106115196447859468160165813 9948299666986825140015545)
            ·
              refine ⟨7461224750240118855011659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9948299666986825140015545 7461224750240118855011659)
              ·
                refine ⟨11191837125360178282517489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461224750240118855011659 11191837125360178282517489)
                ·
                  refine ⟨8393877844020133711888117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11191837125360178282517489 8393877844020133711888117)
                  ·
                    refine ⟨786926047876887535489511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8393877844020133711888117 786926047876887535489511)
                    ·
                      rfl

theorem cell23_4597599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_4597599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597599 prefixEnd_4597599 := by exact prefixLift 4597599
  have htrace : WordTrace (prefixWord ++ tailWord_4597599) baseStart_4597599 baseEnd_4597599 := by
    simpa [prefixWord, tailWord_4597599, baseEnd_4597599] using wordTrace_append hprefix tailTrace_4597599
  have hstable : (prefixWord ++ tailWord_4597599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597599).length < 2 ^ (prefixWord ++ tailWord_4597599).sum := by decide
  have hdescent : baseEnd_4597599 < baseStart_4597599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597619 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 2, 4, 2]
def baseStart_4597619 : Nat := 118140960795 + 4597619 * 2 ^ 59
def prefixEnd_4597619 : Nat := 4983230072969 + 3 ^ 40 * 4597619 * 2
def baseEnd_4597619 : Nat := 2360788413243752528218441

theorem tailTrace_4597619 : CollatzResearch.WordTrace tailWord_4597619 prefixEnd_4597619 2360788413243752528218441 := by
  unfold tailWord_4597619
  simp only [CollatzResearch.WordTrace]
  refine ⟨167688941130619048656483911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111792627420412699104322607 167688941130619048656483911)
  ·
    refine ⟨251533411695928572984725867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167688941130619048656483911 251533411695928572984725867)
    ·
      refine ⟨377300117543892859477088801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251533411695928572984725867 377300117543892859477088801)
      ·
        refine ⟨282975088157919644607816601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377300117543892859477088801 282975088157919644607816601)
        ·
          refine ⟨212231316118439733455862451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282975088157919644607816601 212231316118439733455862451)
          ·
            refine ⟨318346974177659600183793677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212231316118439733455862451 318346974177659600183793677)
            ·
              refine ⟨119380115316622350068922629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318346974177659600183793677 119380115316622350068922629)
              ·
                refine ⟨22383771621866690637922993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119380115316622350068922629 22383771621866690637922993)
                ·
                  refine ⟨16787828716400017978442245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22383771621866690637922993 16787828716400017978442245)
                  ·
                    refine ⟨3147717884325003370957921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16787828716400017978442245 3147717884325003370957921)
                    ·
                      refine ⟨2360788413243752528218441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147717884325003370957921 2360788413243752528218441)
                      ·
                        rfl

theorem cell23_4597619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4, 2].length) (baseStart_4597619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597619 prefixEnd_4597619 := by exact prefixLift 4597619
  have htrace : WordTrace (prefixWord ++ tailWord_4597619) baseStart_4597619 baseEnd_4597619 := by
    simpa [prefixWord, tailWord_4597619, baseEnd_4597619] using wordTrace_append hprefix tailTrace_4597619
  have hstable : (prefixWord ++ tailWord_4597619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597619).length < 2 ^ (prefixWord ++ tailWord_4597619).sum := by decide
  have hdescent : baseEnd_4597619 < baseStart_4597619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597629 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_4597629 : Nat := 118140960795 + 4597629 * 2 ^ 59
def prefixEnd_4597629 : Nat := 4983230072969 + 3 ^ 40 * 4597629 * 2
def baseEnd_4597629 : Nat := 786931182683432496364465

theorem tailTrace_4597629 : CollatzResearch.WordTrace tailWord_4597629 prefixEnd_4597629 786931182683432496364465 := by
  unfold tailWord_4597629
  simp only [CollatzResearch.WordTrace]
  refine ⟨167689305860582820364347941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111792870573721880242898627 167689305860582820364347941)
  ·
    refine ⟨31441744848859278818315239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167689305860582820364347941 31441744848859278818315239)
    ·
      refine ⟨47162617273288918227472859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31441744848859278818315239 47162617273288918227472859)
      ·
        refine ⟨70743925909933377341209289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47162617273288918227472859 70743925909933377341209289)
        ·
          refine ⟨53057944432450033005906967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70743925909933377341209289 53057944432450033005906967)
          ·
            refine ⟨79586916648675049508860451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53057944432450033005906967 79586916648675049508860451)
            ·
              refine ⟨119380374973012574263290677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79586916648675049508860451 119380374973012574263290677)
              ·
                refine ⟨11191910153719928837183501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119380374973012574263290677 11191910153719928837183501)
                ·
                  refine ⟨4196966307644973313943813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11191910153719928837183501 4196966307644973313943813)
                  ·
                    refine ⟨786931182683432496364465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4196966307644973313943813 786931182683432496364465)
                    ·
                      rfl

theorem cell23_4597629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_4597629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597629 prefixEnd_4597629 := by exact prefixLift 4597629
  have htrace : WordTrace (prefixWord ++ tailWord_4597629) baseStart_4597629 baseEnd_4597629 := by
    simpa [prefixWord, tailWord_4597629, baseEnd_4597629] using wordTrace_append hprefix tailTrace_4597629
  have hstable : (prefixWord ++ tailWord_4597629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597629).length < 2 ^ (prefixWord ++ tailWord_4597629).sum := by decide
  have hdescent : baseEnd_4597629 < baseStart_4597629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597719 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 6, 4]
def baseStart_4597719 : Nat := 118140960795 + 4597719 * 2 ^ 59
def prefixEnd_4597719 : Nat := 4983230072969 + 3 ^ 40 * 4597719 * 2
def baseEnd_4597719 : Nat := 786946587103067378989327

theorem tailTrace_4597719 : CollatzResearch.WordTrace tailWord_4597719 prefixEnd_4597719 786946587103067378989327 := by
  unfold tailWord_4597719
  simp only [CollatzResearch.WordTrace]
  refine ⟨167692588430256765735124211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111795058953504510490082807 167692588430256765735124211)
  ·
    refine ⟨251538882645385148602686317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167692588430256765735124211 251538882645385148602686317)
    ·
      refine ⟨94327080992019430726007369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251538882645385148602686317 94327080992019430726007369)
      ·
        refine ⟨70745310744014573044505527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94327080992019430726007369 70745310744014573044505527)
        ·
          refine ⟨106117966116021859566758291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70745310744014573044505527 106117966116021859566758291)
          ·
            refine ⟨159176949174032789350137437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106117966116021859566758291 159176949174032789350137437)
            ·
              refine ⟨59691355940262296006301539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159176949174032789350137437 59691355940262296006301539)
              ·
                refine ⟨89537033910393444009452309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59691355940262296006301539 89537033910393444009452309)
                ·
                  refine ⟨4197048464549692687943077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89537033910393444009452309 4197048464549692687943077)
                  ·
                    refine ⟨786946587103067378989327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197048464549692687943077 786946587103067378989327)
                    ·
                      rfl

theorem cell23_4597719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_4597719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597719 prefixEnd_4597719 := by exact prefixLift 4597719
  have htrace : WordTrace (prefixWord ++ tailWord_4597719) baseStart_4597719 baseEnd_4597719 := by
    simpa [prefixWord, tailWord_4597719, baseEnd_4597719] using wordTrace_append hprefix tailTrace_4597719
  have hstable : (prefixWord ++ tailWord_4597719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597719).length < 2 ^ (prefixWord ++ tailWord_4597719).sum := by decide
  have hdescent : baseEnd_4597719 < baseStart_4597719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597729 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_4597729 : Nat := 118140960795 + 4597729 * 2 ^ 59
def prefixEnd_4597729 : Nat := 4983230072969 + 3 ^ 40 * 4597729 * 2
def baseEnd_4597729 : Nat := 2360844896115747097842935

theorem tailTrace_4597729 : CollatzResearch.WordTrace tailWord_4597729 prefixEnd_4597729 2360844896115747097842935 := by
  unfold tailWord_4597729
  simp only [CollatzResearch.WordTrace]
  refine ⟨167692953160220537442988241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111795302106813691628658827 167692953160220537442988241)
  ·
    refine ⟨125769714870165403082241181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167692953160220537442988241 125769714870165403082241181)
    ·
      refine ⟨47163643076312026155840443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125769714870165403082241181 47163643076312026155840443)
      ·
        refine ⟨70745464614468039233760665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47163643076312026155840443 70745464614468039233760665)
        ·
          refine ⟨53059098460851029425320499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70745464614468039233760665 53059098460851029425320499)
          ·
            refine ⟨79588647691276544137980749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53059098460851029425320499 79588647691276544137980749)
            ·
              refine ⟨29845742884228704051742781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79588647691276544137980749 29845742884228704051742781)
              ·
                refine ⟨11192153581585764019403543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29845742884228704051742781 11192153581585764019403543)
                ·
                  refine ⟨16788230372378646029105315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11192153581585764019403543 16788230372378646029105315)
                  ·
                    refine ⟨25182345558567969043657973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16788230372378646029105315 25182345558567969043657973)
                    ·
                      refine ⟨2360844896115747097842935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25182345558567969043657973 2360844896115747097842935)
                      ·
                        rfl

theorem cell23_4597729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_4597729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597729 prefixEnd_4597729 := by exact prefixLift 4597729
  have htrace : WordTrace (prefixWord ++ tailWord_4597729) baseStart_4597729 baseEnd_4597729 := by
    simpa [prefixWord, tailWord_4597729, baseEnd_4597729] using wordTrace_append hprefix tailTrace_4597729
  have hstable : (prefixWord ++ tailWord_4597729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597729).length < 2 ^ (prefixWord ++ tailWord_4597729).sum := by decide
  have hdescent : baseEnd_4597729 < baseStart_4597729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597736 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_4597736 : Nat := 118140960795 + 4597736 * 2 ^ 59
def prefixEnd_4597736 : Nat := 4983230072969 + 3 ^ 40 * 4597736 * 2
def baseEnd_4597736 : Nat := 786949496826776190151801

theorem tailTrace_4597736 : CollatzResearch.WordTrace tailWord_4597736 prefixEnd_4597736 786949496826776190151801 := by
  unfold tailWord_4597736
  simp only [CollatzResearch.WordTrace]
  refine ⟨83846604235597588819246531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111795472314130118425662041 83846604235597588819246531)
  ·
    refine ⟨125769906353396383228869797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83846604235597588819246531 125769906353396383228869797)
    ·
      refine ⟨23581857441261821855413087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125769906353396383228869797 23581857441261821855413087)
      ·
        refine ⟨35372786161892732783119631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23581857441261821855413087 35372786161892732783119631)
        ·
          refine ⟨53059179242839099174679447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35372786161892732783119631 53059179242839099174679447)
          ·
            refine ⟨79588768864258648762019171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53059179242839099174679447 79588768864258648762019171)
            ·
              refine ⟨119383153296387973143028757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79588768864258648762019171 119383153296387973143028757)
              ·
                refine ⟨5596085310768186241079473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119383153296387973143028757 5596085310768186241079473)
                ·
                  refine ⟨4197063983076139680809605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596085310768186241079473 4197063983076139680809605)
                  ·
                    refine ⟨786949496826776190151801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197063983076139680809605 786949496826776190151801)
                    ·
                      rfl

theorem cell23_4597736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_4597736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597736 prefixEnd_4597736 := by exact prefixLift 4597736
  have htrace : WordTrace (prefixWord ++ tailWord_4597736) baseStart_4597736 baseEnd_4597736 := by
    simpa [prefixWord, tailWord_4597736, baseEnd_4597736] using wordTrace_append hprefix tailTrace_4597736
  have hstable : (prefixWord ++ tailWord_4597736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597736).length < 2 ^ (prefixWord ++ tailWord_4597736).sum := by decide
  have hdescent : baseEnd_4597736 < baseStart_4597736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597753 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 2, 4]
def baseStart_4597753 : Nat := 118140960795 + 4597753 * 2 ^ 59
def prefixEnd_4597753 : Nat := 4983230072969 + 3 ^ 40 * 4597753 * 2
def baseEnd_4597753 : Nat := 786952406550485001314275

theorem tailTrace_4597753 : CollatzResearch.WordTrace tailWord_4597753 prefixEnd_4597753 786952406550485001314275 := by
  unfold tailWord_4597753
  simp only [CollatzResearch.WordTrace]
  refine ⟨167693828512133589541861913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111795885674755726361241275 167693828512133589541861913)
  ·
    refine ⟨125770371384100192156396435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167693828512133589541861913 125770371384100192156396435)
    ·
      refine ⟨188655557076150288234594653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125770371384100192156396435 188655557076150288234594653)
      ·
        refine ⟨70745833903556358087972995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188655557076150288234594653 70745833903556358087972995)
        ·
          refine ⟨106118750855334537131959493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70745833903556358087972995 106118750855334537131959493)
          ·
            refine ⟨19897265785375225712242405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106118750855334537131959493 19897265785375225712242405)
            ·
              refine ⟨3730737334757854821045451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19897265785375225712242405 3730737334757854821045451)
              ·
                refine ⟨5596106002136782231568177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730737334757854821045451 5596106002136782231568177)
                ·
                  refine ⟨4197079501602586673676133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596106002136782231568177 4197079501602586673676133)
                  ·
                    refine ⟨786952406550485001314275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197079501602586673676133 786952406550485001314275)
                    ·
                      rfl

theorem cell23_4597753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_4597753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597753 prefixEnd_4597753 := by exact prefixLift 4597753
  have htrace : WordTrace (prefixWord ++ tailWord_4597753) baseStart_4597753 baseEnd_4597753 := by
    simpa [prefixWord, tailWord_4597753, baseEnd_4597753] using wordTrace_append hprefix tailTrace_4597753
  have hstable : (prefixWord ++ tailWord_4597753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597753).length < 2 ^ (prefixWord ++ tailWord_4597753).sum := by decide
  have hdescent : baseEnd_4597753 < baseStart_4597753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597759 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3]
def baseStart_4597759 : Nat := 118140960795 + 4597759 * 2 ^ 59
def prefixEnd_4597759 : Nat := 4983230072969 + 3 ^ 40 * 4597759 * 2
def baseEnd_4597759 : Nat := 2360860300535381980467797

theorem tailTrace_4597759 : CollatzResearch.WordTrace tailWord_4597759 prefixEnd_4597759 2360860300535381980467797 := by
  unfold tailWord_4597759
  simp only [CollatzResearch.WordTrace]
  refine ⟨167694047350111852566580331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111796031566741235044386887 167694047350111852566580331)
  ·
    refine ⟨251541071025167778849870497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167694047350111852566580331 251541071025167778849870497)
    ·
      refine ⟨188655803268875834137402873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251541071025167778849870497 188655803268875834137402873)
      ·
        refine ⟨141491852451656875603052155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188655803268875834137402873 141491852451656875603052155)
        ·
          refine ⟨212237778677485313404578233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141491852451656875603052155 212237778677485313404578233)
          ·
            refine ⟨159178334008113985053433675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212237778677485313404578233 159178334008113985053433675)
            ·
              refine ⟨238767501012170977580150513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159178334008113985053433675 238767501012170977580150513)
              ·
                refine ⟨179075625759128233185112885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238767501012170977580150513 179075625759128233185112885)
                ·
                  refine ⟨16788339914918271861104333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179075625759128233185112885 16788339914918271861104333)
                  ·
                    refine ⟨6295627468094351947914125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16788339914918271861104333 6295627468094351947914125)
                    ·
                      refine ⟨2360860300535381980467797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295627468094351947914125 2360860300535381980467797)
                      ·
                        rfl

theorem cell23_4597759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_4597759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597759 prefixEnd_4597759 := by exact prefixLift 4597759
  have htrace : WordTrace (prefixWord ++ tailWord_4597759) baseStart_4597759 baseEnd_4597759 := by
    simpa [prefixWord, tailWord_4597759, baseEnd_4597759] using wordTrace_append hprefix tailTrace_4597759
  have hstable : (prefixWord ++ tailWord_4597759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597759).length < 2 ^ (prefixWord ++ tailWord_4597759).sum := by decide
  have hdescent : baseEnd_4597759 < baseStart_4597759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597800 : List Nat := [2, 1, 5, 3, 2, 1, 1, 8]
def baseStart_4597800 : Nat := 118140960795 + 4597800 * 2 ^ 59
def prefixEnd_4597800 : Nat := 4983230072969 + 3 ^ 40 * 4597800 * 2
def baseEnd_4597800 : Nat := 87440050120082085927967

theorem tailTrace_4597800 : CollatzResearch.WordTrace tailWord_4597800 prefixEnd_4597800 87440050120082085927967 := by
  unfold tailWord_4597800
  simp only [CollatzResearch.WordTrace]
  refine ⟨83847771371481658284411427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111797028495308877712548569 83847771371481658284411427)
  ·
    refine ⟨125771657057222487426617141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83847771371481658284411427 125771657057222487426617141)
    ·
      refine ⟨11791092849114608196245357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125771657057222487426617141 11791092849114608196245357)
      ·
        refine ⟨4421659818417978073592009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11791092849114608196245357 4421659818417978073592009)
        ·
          refine ⟨3316244863813483555194007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4421659818417978073592009 3316244863813483555194007)
          ·
            refine ⟨4974367295720225332791011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316244863813483555194007 4974367295720225332791011)
            ·
              refine ⟨7461550943580337999186517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974367295720225332791011 7461550943580337999186517)
              ·
                refine ⟨87440050120082085927967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7461550943580337999186517 87440050120082085927967)
                ·
                  rfl

theorem cell23_4597800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 8].length) (baseStart_4597800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597800 prefixEnd_4597800 := by exact prefixLift 4597800
  have htrace : WordTrace (prefixWord ++ tailWord_4597800) baseStart_4597800 baseEnd_4597800 := by
    simpa [prefixWord, tailWord_4597800, baseEnd_4597800] using wordTrace_append hprefix tailTrace_4597800
  have hstable : (prefixWord ++ tailWord_4597800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597800).length < 2 ^ (prefixWord ++ tailWord_4597800).sum := by decide
  have hdescent : baseEnd_4597800 < baseStart_4597800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597809 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_4597809 : Nat := 118140960795 + 4597809 * 2 ^ 59
def prefixEnd_4597809 : Nat := 4983230072969 + 3 ^ 40 * 4597809 * 2
def baseEnd_4597809 : Nat := 786961991522702261614189

theorem tailTrace_4597809 : CollatzResearch.WordTrace tailWord_4597809 prefixEnd_4597809 786961991522702261614189 := by
  unfold tailWord_4597809
  simp only [CollatzResearch.WordTrace]
  refine ⟨167695870999930711105900481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111797247333287140737266987 167695870999930711105900481)
  ·
    refine ⟨125771903249948033329425361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167695870999930711105900481 125771903249948033329425361)
    ·
      refine ⟨94328927437461024997069021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125771903249948033329425361 94328927437461024997069021)
      ·
        refine ⟨35373347789047884373900883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94328927437461024997069021 35373347789047884373900883)
        ·
          refine ⟨53060021683571826560851325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35373347789047884373900883 53060021683571826560851325)
          ·
            refine ⟨19897508131339434960319247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53060021683571826560851325 19897508131339434960319247)
            ·
              refine ⟨29846262197009152440478871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19897508131339434960319247 29846262197009152440478871)
              ·
                refine ⟨44769393295513728660718307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29846262197009152440478871 44769393295513728660718307)
                ·
                  refine ⟨67154089943270592991077461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44769393295513728660718307 67154089943270592991077461)
                  ·
                    refine ⟨786961991522702261614189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67154089943270592991077461 786961991522702261614189)
                    ·
                      rfl

theorem cell23_4597809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_4597809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597809 prefixEnd_4597809 := by exact prefixLift 4597809
  have htrace : WordTrace (prefixWord ++ tailWord_4597809) baseStart_4597809 baseEnd_4597809 := by
    simpa [prefixWord, tailWord_4597809, baseEnd_4597809] using wordTrace_append hprefix tailTrace_4597809
  have hstable : (prefixWord ++ tailWord_4597809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597809).length < 2 ^ (prefixWord ++ tailWord_4597809).sum := by decide
  have hdescent : baseEnd_4597809 < baseStart_4597809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597829 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_4597829 : Nat := 118140960795 + 4597829 * 2 ^ 59
def prefixEnd_4597829 : Nat := 4983230072969 + 3 ^ 40 * 4597829 * 2
def baseEnd_4597829 : Nat := 2360896244181196706592475

theorem tailTrace_4597829 : CollatzResearch.WordTrace tailWord_4597829 prefixEnd_4597829 2360896244181196706592475 := by
  unfold tailWord_4597829
  simp only [CollatzResearch.WordTrace]
  refine ⟨167696600459858254521628541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111797733639905503014419027 167696600459858254521628541)
  ·
    refine ⟨62886225172446845445610703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167696600459858254521628541 62886225172446845445610703)
    ·
      refine ⟨94329337758670268168416055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62886225172446845445610703 94329337758670268168416055)
      ·
        refine ⟨141494006638005402252624083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94329337758670268168416055 141494006638005402252624083)
        ·
          refine ⟨212241009957008103378936125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141494006638005402252624083 212241009957008103378936125)
          ·
            refine ⟨79590378733878038767101047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212241009957008103378936125 79590378733878038767101047)
            ·
              refine ⟨119385568100817058150651571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79590378733878038767101047 119385568100817058150651571)
              ·
                refine ⟨179078352151225587225977357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119385568100817058150651571 179078352151225587225977357)
                ·
                  refine ⟨67154382056709595209741509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179078352151225587225977357 67154382056709595209741509)
                  ·
                    refine ⟨12591446635633049101826533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67154382056709595209741509 12591446635633049101826533)
                    ·
                      refine ⟨2360896244181196706592475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12591446635633049101826533 2360896244181196706592475)
                      ·
                        rfl

theorem cell23_4597829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_4597829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597829 prefixEnd_4597829 := by exact prefixLift 4597829
  have htrace : WordTrace (prefixWord ++ tailWord_4597829) baseStart_4597829 baseEnd_4597829 := by
    simpa [prefixWord, tailWord_4597829, baseEnd_4597829] using wordTrace_append hprefix tailTrace_4597829
  have hstable : (prefixWord ++ tailWord_4597829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597829).length < 2 ^ (prefixWord ++ tailWord_4597829).sum := by decide
  have hdescent : baseEnd_4597829 < baseStart_4597829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597833 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 4, 2, 2]
def baseStart_4597833 : Nat := 118140960795 + 4597833 * 2 ^ 59
def prefixEnd_4597833 : Nat := 4983230072969 + 3 ^ 40 * 4597833 * 2
def baseEnd_4597833 : Nat := 2360898298103814690942457

theorem tailTrace_4597833 : CollatzResearch.WordTrace tailWord_4597833 prefixEnd_4597833 2360898298103814690942457 := by
  unfold tailWord_4597833
  simp only [CollatzResearch.WordTrace]
  refine ⟨167696746351843763204774153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111797830901229175469849435 167696746351843763204774153)
  ·
    refine ⟨125772559763882822403580615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167696746351843763204774153 125772559763882822403580615)
    ·
      refine ⟨188658839645824233605370923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125772559763882822403580615 188658839645824233605370923)
      ·
        refine ⟨282988259468736350408056385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188658839645824233605370923 282988259468736350408056385)
        ·
          refine ⟨212241194601552262806042289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282988259468736350408056385 212241194601552262806042289)
          ·
            refine ⟨159180895951164197104531717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212241194601552262806042289 159180895951164197104531717)
            ·
              refine ⟨29846417990843286957099697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159180895951164197104531717 29846417990843286957099697)
              ·
                refine ⟨22384813493132465217824773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29846417990843286957099697 22384813493132465217824773)
                ·
                  refine ⟨4197152529962337228342145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22384813493132465217824773 4197152529962337228342145)
                  ·
                    refine ⟨3147864397471752921256609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4197152529962337228342145 3147864397471752921256609)
                    ·
                      refine ⟨2360898298103814690942457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147864397471752921256609 2360898298103814690942457)
                      ·
                        rfl

theorem cell23_4597833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 2, 2].length) (baseStart_4597833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597833 prefixEnd_4597833 := by exact prefixLift 4597833
  have htrace : WordTrace (prefixWord ++ tailWord_4597833) baseStart_4597833 baseEnd_4597833 := by
    simpa [prefixWord, tailWord_4597833, baseEnd_4597833] using wordTrace_append hprefix tailTrace_4597833
  have hstable : (prefixWord ++ tailWord_4597833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597833).length < 2 ^ (prefixWord ++ tailWord_4597833).sum := by decide
  have hdescent : baseEnd_4597833 < baseStart_4597833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597856 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 7]
def baseStart_4597856 : Nat := 118140960795 + 4597856 * 2 ^ 59
def prefixEnd_4597856 : Nat := 4983230072969 + 3 ^ 40 * 4597856 * 2
def baseEnd_4597856 : Nat := 262323345350985344550539

theorem tailTrace_4597856 : CollatzResearch.WordTrace tailWord_4597856 prefixEnd_4597856 262323345350985344550539 := by
  unfold tailWord_4597856
  simp only [CollatzResearch.WordTrace]
  refine ⟨83848792615380219066430711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111798390153840292088574281 83848792615380219066430711)
  ·
    refine ⟨125773188923070328599646067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83848792615380219066430711 125773188923070328599646067)
    ·
      refine ⟨188659783384605492899469101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125773188923070328599646067 188659783384605492899469101)
      ·
        refine ⟨70747418769227059837300913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188659783384605492899469101 70747418769227059837300913)
        ·
          refine ⟨53060564076920294877975685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70747418769227059837300913 53060564076920294877975685)
          ·
            refine ⟨9948855764422555289620441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53060564076920294877975685 9948855764422555289620441)
            ·
              refine ⟨7461641823316916467215331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9948855764422555289620441 7461641823316916467215331)
              ·
                refine ⟨11192462734975374700822997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461641823316916467215331 11192462734975374700822997)
                ·
                  refine ⟨262323345350985344550539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11192462734975374700822997 262323345350985344550539)
                  ·
                    rfl

theorem cell23_4597856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_4597856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597856 prefixEnd_4597856 := by exact prefixLift 4597856
  have htrace : WordTrace (prefixWord ++ tailWord_4597856) baseStart_4597856 baseEnd_4597856 := by
    simpa [prefixWord, tailWord_4597856, baseEnd_4597856] using wordTrace_append hprefix tailTrace_4597856
  have hstable : (prefixWord ++ tailWord_4597856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597856).length < 2 ^ (prefixWord ++ tailWord_4597856).sum := by decide
  have hdescent : baseEnd_4597856 < baseStart_4597856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597918 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4597918 : Nat := 118140960795 + 4597918 * 2 ^ 59
def prefixEnd_4597918 : Nat := 4983230072969 + 3 ^ 40 * 4597918 * 2
def baseEnd_4597918 : Nat := 2360941943959446858379567

theorem tailTrace_4597918 : CollatzResearch.WordTrace tailWord_4597918 prefixEnd_4597918 2360941943959446858379567 := by
  unfold tailWord_4597918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20962480819566977840202301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111799897704357215147745605 20962480819566977840202301)
  ·
    refine ⟨7860930307337616690075863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20962480819566977840202301 7860930307337616690075863)
    ·
      refine ⟨11791395461006425035113795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860930307337616690075863 11791395461006425035113795)
      ·
        refine ⟨17687093191509637552670693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11791395461006425035113795 17687093191509637552670693)
        ·
          refine ⟨3316329973408057041125755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17687093191509637552670693 3316329973408057041125755)
          ·
            refine ⟨4974494960112085561688633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316329973408057041125755 4974494960112085561688633)
            ·
              refine ⟨3730871220084064171266475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4974494960112085561688633 3730871220084064171266475)
              ·
                refine ⟨5596306830126096256899713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730871220084064171266475 5596306830126096256899713)
                ·
                  refine ⟨4197230122594572192674785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596306830126096256899713 4197230122594572192674785)
                  ·
                    refine ⟨3147922591945929144506089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4197230122594572192674785 3147922591945929144506089)
                    ·
                      refine ⟨2360941943959446858379567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147922591945929144506089 2360941943959446858379567)
                      ·
                        rfl

theorem cell23_4597918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4597918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597918 prefixEnd_4597918 := by exact prefixLift 4597918
  have htrace : WordTrace (prefixWord ++ tailWord_4597918) baseStart_4597918 baseEnd_4597918 := by
    simpa [prefixWord, tailWord_4597918, baseEnd_4597918] using wordTrace_append hprefix tailTrace_4597918
  have hstable : (prefixWord ++ tailWord_4597918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597918).length < 2 ^ (prefixWord ++ tailWord_4597918).sum := by decide
  have hdescent : baseEnd_4597918 < baseStart_4597918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597943 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_4597943 : Nat := 118140960795 + 4597943 * 2 ^ 59
def prefixEnd_4597943 : Nat := 4983230072969 + 3 ^ 40 * 4597943 * 2
def baseEnd_4597943 : Nat := 2360954780975809260566951

theorem tailTrace_4597943 : CollatzResearch.WordTrace tailWord_4597943 prefixEnd_4597943 2360954780975809260566951 := by
  unfold tailWord_4597943
  simp only [CollatzResearch.WordTrace]
  refine ⟨167700758381445251991278483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111800505587630167994185655 167700758381445251991278483)
  ·
    refine ⟨251551137572167877986917725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167700758381445251991278483 251551137572167877986917725)
    ·
      refine ⟨94331676589562954245094147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251551137572167877986917725 94331676589562954245094147)
      ·
        refine ⟨141497514884344431367641221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94331676589562954245094147 141497514884344431367641221)
        ·
          refine ⟨26530784040814580881432729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141497514884344431367641221 26530784040814580881432729)
          ·
            refine ⟨19898088030610935661074547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26530784040814580881432729 19898088030610935661074547)
            ·
              refine ⟨29847132045916403491611821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19898088030610935661074547 29847132045916403491611821)
              ·
                refine ⟨11192674517218651309354433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29847132045916403491611821 11192674517218651309354433)
                ·
                  refine ⟨8394505887913988482015825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11192674517218651309354433 8394505887913988482015825)
                  ·
                    refine ⟨6295879415935491361511869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8394505887913988482015825 6295879415935491361511869)
                    ·
                      refine ⟨2360954780975809260566951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6295879415935491361511869 2360954780975809260566951)
                      ·
                        rfl

theorem cell23_4597943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_4597943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597943 prefixEnd_4597943 := by exact prefixLift 4597943
  have htrace : WordTrace (prefixWord ++ tailWord_4597943) baseStart_4597943 baseEnd_4597943 := by
    simpa [prefixWord, tailWord_4597943, baseEnd_4597943] using wordTrace_append hprefix tailTrace_4597943
  have hstable : (prefixWord ++ tailWord_4597943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597943).length < 2 ^ (prefixWord ++ tailWord_4597943).sum := by decide
  have hdescent : baseEnd_4597943 < baseStart_4597943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4597983 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 5, 2]
def baseStart_4597983 : Nat := 118140960795 + 4597983 * 2 ^ 59
def prefixEnd_4597983 : Nat := 4983230072969 + 3 ^ 40 * 4597983 * 2
def baseEnd_4597983 : Nat := 2360975320201989104066767

theorem tailTrace_4597983 : CollatzResearch.WordTrace tailWord_4597983 prefixEnd_4597983 2360975320201989104066767 := by
  unfold tailWord_4597983
  simp only [CollatzResearch.WordTrace]
  refine ⟨167702217301300338822734603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111801478200866892548489735 167702217301300338822734603)
  ·
    refine ⟨251553325951950508234101905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167702217301300338822734603 251553325951950508234101905)
    ·
      refine ⟨188664994463962881175576429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251553325951950508234101905 188664994463962881175576429)
      ·
        refine ⟨70749372923986080440841161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188664994463962881175576429 70749372923986080440841161)
        ·
          refine ⟨53062029692989560330630871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70749372923986080440841161 53062029692989560330630871)
          ·
            refine ⟨79593044539484340495946307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53062029692989560330630871 79593044539484340495946307)
            ·
              refine ⟨119389566809226510743919461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79593044539484340495946307 119389566809226510743919461)
              ·
                refine ⟨22385543776729970764484899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119389566809226510743919461 22385543776729970764484899)
                ·
                  refine ⟨33578315665094956146727349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22385543776729970764484899 33578315665094956146727349)
                  ·
                    refine ⟨3147967093602652138755689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33578315665094956146727349 3147967093602652138755689)
                    ·
                      refine ⟨2360975320201989104066767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147967093602652138755689 2360975320201989104066767)
                      ·
                        rfl

theorem cell23_4597983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_4597983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4597983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4597983 prefixEnd_4597983 := by exact prefixLift 4597983
  have htrace : WordTrace (prefixWord ++ tailWord_4597983) baseStart_4597983 baseEnd_4597983 := by
    simpa [prefixWord, tailWord_4597983, baseEnd_4597983] using wordTrace_append hprefix tailTrace_4597983
  have hstable : (prefixWord ++ tailWord_4597983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4597983).length < 2 ^ (prefixWord ++ tailWord_4597983).sum := by decide
  have hdescent : baseEnd_4597983 < baseStart_4597983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4597983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598010 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_4598010 : Nat := 118140960795 + 4598010 * 2 ^ 59
def prefixEnd_4598010 : Nat := 4983230072969 + 3 ^ 40 * 4598010 * 2
def baseEnd_4598010 : Nat := 786996394726553499476381

theorem tailTrace_4598010 : CollatzResearch.WordTrace tailWord_4598010 prefixEnd_4598010 786996394726553499476381 := by
  unfold tailWord_4598010
  simp only [CollatzResearch.WordTrace]
  refine ⟨41925800518050630608491871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111802134714801681622644989 41925800518050630608491871)
  ·
    refine ⟨62888700777075945912737807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41925800518050630608491871 62888700777075945912737807)
    ·
      refine ⟨94333051165613918869106711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62888700777075945912737807 94333051165613918869106711)
      ·
        refine ⟨141499576748420878303660067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94333051165613918869106711 141499576748420878303660067)
        ·
          refine ⟨212249365122631317455490101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141499576748420878303660067 212249365122631317455490101)
          ·
            refine ⟨19898377980246686011452197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 212249365122631317455490101 19898377980246686011452197)
            ·
              refine ⟨3730945871296253627147287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19898377980246686011452197 3730945871296253627147287)
              ·
                refine ⟨5596418806944380440720931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730945871296253627147287 5596418806944380440720931)
                ·
                  refine ⟨8394628210416570661081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5596418806944380440720931 8394628210416570661081397)
                  ·
                    refine ⟨786996394726553499476381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8394628210416570661081397 786996394726553499476381)
                    ·
                      rfl

theorem cell23_4598010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_4598010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598010 prefixEnd_4598010 := by exact prefixLift 4598010
  have htrace : WordTrace (prefixWord ++ tailWord_4598010) baseStart_4598010 baseEnd_4598010 := by
    simpa [prefixWord, tailWord_4598010, baseEnd_4598010] using wordTrace_append hprefix tailTrace_4598010
  have hstable : (prefixWord ++ tailWord_4598010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598010).length < 2 ^ (prefixWord ++ tailWord_4598010).sum := by decide
  have hdescent : baseEnd_4598010 < baseStart_4598010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598013 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_4598013 : Nat := 118140960795 + 4598013 * 2 ^ 59
def prefixEnd_4598013 : Nat := 4983230072969 + 3 ^ 40 * 4598013 * 2
def baseEnd_4598013 : Nat := 2360990724621623986691629

theorem tailTrace_4598013 : CollatzResearch.WordTrace tailWord_4598013 prefixEnd_4598013 2360990724621623986691629 := by
  unfold tailWord_4598013
  simp only [CollatzResearch.WordTrace]
  refine ⟨167703311491191653946326693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111802207660794435964217795 167703311491191653946326693)
  ·
    refine ⟨31444370904598435114936255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167703311491191653946326693 31444370904598435114936255)
    ·
      refine ⟨47166556356897652672404383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31444370904598435114936255 47166556356897652672404383)
      ·
        refine ⟨70749834535346479008606575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47166556356897652672404383 70749834535346479008606575)
        ·
          refine ⟨106124751803019718512909863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70749834535346479008606575 106124751803019718512909863)
          ·
            refine ⟨159187127704529577769364795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106124751803019718512909863 159187127704529577769364795)
            ·
              refine ⟨238780691556794366654047193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159187127704529577769364795 238780691556794366654047193)
              ·
                refine ⟨179085518667595774990535395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238780691556794366654047193 179085518667595774990535395)
                ·
                  refine ⟨268628278001393662485803093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179085518667595774990535395 268628278001393662485803093)
                  ·
                    refine ⟨3147987632828831982255505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 268628278001393662485803093 3147987632828831982255505)
                    ·
                      refine ⟨2360990724621623986691629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3147987632828831982255505 2360990724621623986691629)
                      ·
                        rfl

theorem cell23_4598013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_4598013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598013 prefixEnd_4598013 := by exact prefixLift 4598013
  have htrace : WordTrace (prefixWord ++ tailWord_4598013) baseStart_4598013 baseEnd_4598013 := by
    simpa [prefixWord, tailWord_4598013, baseEnd_4598013] using wordTrace_append hprefix tailTrace_4598013
  have hstable : (prefixWord ++ tailWord_4598013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598013).length < 2 ^ (prefixWord ++ tailWord_4598013).sum := by decide
  have hdescent : baseEnd_4598013 < baseStart_4598013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598033 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_4598033 : Nat := 118140960795 + 4598033 * 2 ^ 59
def prefixEnd_4598033 : Nat := 4983230072969 + 3 ^ 40 * 4598033 * 2
def baseEnd_4598033 : Nat := 2361000994234713908441537

theorem tailTrace_4598033 : CollatzResearch.WordTrace tailWord_4598033 prefixEnd_4598033 2361000994234713908441537 := by
  unfold tailWord_4598033
  simp only [CollatzResearch.WordTrace]
  refine ⟨167704040951119197362054753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111802693967412798241369835 167704040951119197362054753)
  ·
    refine ⟨125778030713339398021541065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167704040951119197362054753 125778030713339398021541065)
    ·
      refine ⟨94333523035004548516155799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125778030713339398021541065 94333523035004548516155799)
      ·
        refine ⟨141500284552506822774233699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94333523035004548516155799 141500284552506822774233699)
        ·
          refine ⟨212250426828760234161350549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141500284552506822774233699 212250426828760234161350549)
          ·
            refine ⟨9949238757598135976313307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212250426828760234161350549 9949238757598135976313307)
            ·
              refine ⟨14923858136397203964469961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949238757598135976313307 14923858136397203964469961)
              ·
                refine ⟨11192893602297902973352471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14923858136397203964469961 11192893602297902973352471)
                ·
                  refine ⟨16789340403446854460028707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11192893602297902973352471 16789340403446854460028707)
                  ·
                    refine ⟨25184010605170281690043061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16789340403446854460028707 25184010605170281690043061)
                    ·
                      refine ⟨2361000994234713908441537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25184010605170281690043061 2361000994234713908441537)
                      ·
                        rfl

theorem cell23_4598033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_4598033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598033 prefixEnd_4598033 := by exact prefixLift 4598033
  have htrace : WordTrace (prefixWord ++ tailWord_4598033) baseStart_4598033 baseEnd_4598033 := by
    simpa [prefixWord, tailWord_4598033, baseEnd_4598033] using wordTrace_append hprefix tailTrace_4598033
  have hstable : (prefixWord ++ tailWord_4598033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598033).length < 2 ^ (prefixWord ++ tailWord_4598033).sum := by decide
  have hdescent : baseEnd_4598033 < baseStart_4598033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598043 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4]
def baseStart_4598043 : Nat := 118140960795 + 4598043 * 2 ^ 59
def prefixEnd_4598043 : Nat := 4983230072969 + 3 ^ 40 * 4598043 * 2
def baseEnd_4598043 : Nat := 2361006129041258869316491

theorem tailTrace_4598043 : CollatzResearch.WordTrace tailWord_4598043 prefixEnd_4598043 2361006129041258869316491 := by
  unfold tailWord_4598043
  simp only [CollatzResearch.WordTrace]
  refine ⟨167704405681082969069918783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111802937120721979379945855 167704405681082969069918783)
  ·
    refine ⟨251556608521624453604878175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167704405681082969069918783 251556608521624453604878175)
    ·
      refine ⟨377334912782436680407317263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251556608521624453604878175 377334912782436680407317263)
      ·
        refine ⟨566002369173655020610975895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377334912782436680407317263 566002369173655020610975895)
        ·
          refine ⟨849003553760482530916463843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566002369173655020610975895 849003553760482530916463843)
          ·
            refine ⟨1273505330640723796374695765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849003553760482530916463843 1273505330640723796374695765)
            ·
              refine ⟨7461945296722990994382983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1273505330640723796374695765 7461945296722990994382983)
              ·
                refine ⟨11192917945084486491574475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461945296722990994382983 11192917945084486491574475)
                ·
                  refine ⟨16789376917626729737361713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11192917945084486491574475 16789376917626729737361713)
                  ·
                    refine ⟨12592032688220047303021285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16789376917626729737361713 12592032688220047303021285)
                    ·
                      refine ⟨2361006129041258869316491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12592032688220047303021285 2361006129041258869316491)
                      ·
                        rfl

theorem cell23_4598043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 4].length) (baseStart_4598043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598043 prefixEnd_4598043 := by exact prefixLift 4598043
  have htrace : WordTrace (prefixWord ++ tailWord_4598043) baseStart_4598043 baseEnd_4598043 := by
    simpa [prefixWord, tailWord_4598043, baseEnd_4598043] using wordTrace_append hprefix tailTrace_4598043
  have hstable : (prefixWord ++ tailWord_4598043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598043).length < 2 ^ (prefixWord ++ tailWord_4598043).sum := by decide
  have hdescent : baseEnd_4598043 < baseStart_4598043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598047 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 3, 2, 2]
def baseStart_4598047 : Nat := 118140960795 + 4598047 * 2 ^ 59
def prefixEnd_4598047 : Nat := 4983230072969 + 3 ^ 40 * 4598047 * 2
def baseEnd_4598047 : Nat := 2361008182963876853666473

theorem tailTrace_4598047 : CollatzResearch.WordTrace tailWord_4598047 prefixEnd_4598047 2361008182963876853666473 := by
  unfold tailWord_4598047
  simp only [CollatzResearch.WordTrace]
  refine ⟨167704551573068477753064395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111803034382045651835376263 167704551573068477753064395)
  ·
    refine ⟨251556827359602716629596593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167704551573068477753064395 251556827359602716629596593)
    ·
      refine ⟨188667620519702037472197445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251556827359602716629596593 188667620519702037472197445)
      ·
        refine ⟨35375178847444132026037021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188667620519702037472197445 35375178847444132026037021)
        ·
          refine ⟨13265692067791549509763883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35375178847444132026037021 13265692067791549509763883)
          ·
            refine ⟨19898538101687324264645825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13265692067791549509763883 19898538101687324264645825)
            ·
              refine ⟨14923903576265493198484369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19898538101687324264645825 14923903576265493198484369)
              ·
                refine ⟨11192927682199119898863277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14923903576265493198484369 11192927682199119898863277)
                ·
                  refine ⟨4197347880824669962073729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11192927682199119898863277 4197347880824669962073729)
                  ·
                    refine ⟨3148010910618502471555297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4197347880824669962073729 3148010910618502471555297)
                    ·
                      refine ⟨2361008182963876853666473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148010910618502471555297 2361008182963876853666473)
                      ·
                        rfl

theorem cell23_4598047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_4598047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598047 prefixEnd_4598047 := by exact prefixLift 4598047
  have htrace : WordTrace (prefixWord ++ tailWord_4598047) baseStart_4598047 baseEnd_4598047 := by
    simpa [prefixWord, tailWord_4598047, baseEnd_4598047] using wordTrace_append hprefix tailTrace_4598047
  have hstable : (prefixWord ++ tailWord_4598047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598047).length < 2 ^ (prefixWord ++ tailWord_4598047).sum := by decide
  have hdescent : baseEnd_4598047 < baseStart_4598047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598053 : List Nat := [1, 3, 1, 2, 5, 1, 1, 9]
def baseStart_4598053 : Nat := 118140960795 + 4598053 * 2 ^ 59
def prefixEnd_4598053 : Nat := 4983230072969 + 3 ^ 40 * 4598053 * 2
def baseEnd_4598053 : Nat := 87444861623992734451535

theorem tailTrace_4598053 : CollatzResearch.WordTrace tailWord_4598053 prefixEnd_4598053 87444861623992734451535 := by
  unfold tailWord_4598053
  simp only [CollatzResearch.WordTrace]
  refine ⟨167704770411046740777782813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111803180274031160518521875 167704770411046740777782813)
  ·
    refine ⟨62889288904142527791668555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167704770411046740777782813 62889288904142527791668555)
    ·
      refine ⟨94333933356213791687502833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62889288904142527791668555 94333933356213791687502833)
      ·
        refine ⟨70750450017160343765627125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94333933356213791687502833 70750450017160343765627125)
        ·
          refine ⟨6632854689108782228027543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70750450017160343765627125 6632854689108782228027543)
          ·
            refine ⟨9949282033663173342041315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6632854689108782228027543 9949282033663173342041315)
            ·
              refine ⟨14923923050494760013061973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949282033663173342041315 14923923050494760013061973)
              ·
                refine ⟨87444861623992734451535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14923923050494760013061973 87444861623992734451535)
                ·
                  rfl

theorem cell23_4598053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 9].length) (baseStart_4598053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598053 prefixEnd_4598053 := by exact prefixLift 4598053
  have htrace : WordTrace (prefixWord ++ tailWord_4598053) baseStart_4598053 baseEnd_4598053 := by
    simpa [prefixWord, tailWord_4598053, baseEnd_4598053] using wordTrace_append hprefix tailTrace_4598053
  have hstable : (prefixWord ++ tailWord_4598053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598053).length < 2 ^ (prefixWord ++ tailWord_4598053).sum := by decide
  have hdescent : baseEnd_4598053 < baseStart_4598053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598058 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4598058 : Nat := 118140960795 + 4598058 * 2 ^ 59
def prefixEnd_4598058 : Nat := 4983230072969 + 3 ^ 40 * 4598058 * 2
def baseEnd_4598058 : Nat := 2361013831251076310628923

theorem tailTrace_4598058 : CollatzResearch.WordTrace tailWord_4598058 prefixEnd_4598058 2361013831251076310628923 := by
  unfold tailWord_4598058
  simp only [CollatzResearch.WordTrace]
  refine ⟨41926238194007156657928707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111803301850685751087809885 41926238194007156657928707)
  ·
    refine ⟨62889357291010734986893061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41926238194007156657928707 62889357291010734986893061)
    ·
      refine ⟨11791754492064512810042449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62889357291010734986893061 11791754492064512810042449)
      ·
        refine ⟨8843815869048384607531837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11791754492064512810042449 8843815869048384607531837)
        ·
          refine ⟨3316430950893144227824439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8843815869048384607531837 3316430950893144227824439)
          ·
            refine ⟨4974646426339716341736659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316430950893144227824439 4974646426339716341736659)
            ·
              refine ⟨7461969639509574512604989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974646426339716341736659 7461969639509574512604989)
              ·
                refine ⟨2798238614816090442226871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7461969639509574512604989 2798238614816090442226871)
                ·
                  refine ⟨4197357922224135663340307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798238614816090442226871 4197357922224135663340307)
                  ·
                    refine ⟨6296036883336203495010461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4197357922224135663340307 6296036883336203495010461)
                    ·
                      refine ⟨2361013831251076310628923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296036883336203495010461 2361013831251076310628923)
                      ·
                        rfl

theorem cell23_4598058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4598058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598058 prefixEnd_4598058 := by exact prefixLift 4598058
  have htrace : WordTrace (prefixWord ++ tailWord_4598058) baseStart_4598058 baseEnd_4598058 := by
    simpa [prefixWord, tailWord_4598058, baseEnd_4598058] using wordTrace_append hprefix tailTrace_4598058
  have hstable : (prefixWord ++ tailWord_4598058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598058).length < 2 ^ (prefixWord ++ tailWord_4598058).sum := by decide
  have hdescent : baseEnd_4598058 < baseStart_4598058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598063 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3]
def baseStart_4598063 : Nat := 118140960795 + 4598063 * 2 ^ 59
def prefixEnd_4598063 : Nat := 4983230072969 + 3 ^ 40 * 4598063 * 2
def baseEnd_4598063 : Nat := 2361016398654348791066399

theorem tailTrace_4598063 : CollatzResearch.WordTrace tailWord_4598063 prefixEnd_4598063 2361016398654348791066399 := by
  unfold tailWord_4598063
  simp only [CollatzResearch.WordTrace]
  refine ⟨167705135141010512485646843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111803423427340341657097895 167705135141010512485646843)
  ·
    refine ⟨251557702711515768728470265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167705135141010512485646843 251557702711515768728470265)
    ·
      refine ⟨188668277033636826546352699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251557702711515768728470265 188668277033636826546352699)
      ·
        refine ⟨283002415550455239819529049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188668277033636826546352699 283002415550455239819529049)
        ·
          refine ⟨212251811662841429864646787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283002415550455239819529049 212251811662841429864646787)
          ·
            refine ⟨318377717494262144796970181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212251811662841429864646787 318377717494262144796970181)
            ·
              refine ⟨59695822030174152149431909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 318377717494262144796970181 59695822030174152149431909)
              ·
                refine ⟨11192966630657653528018483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59695822030174152149431909 11192966630657653528018483)
                ·
                  refine ⟨16789449945986480292027725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11192966630657653528018483 16789449945986480292027725)
                  ·
                    refine ⟨6296043729744930109510397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16789449945986480292027725 6296043729744930109510397)
                    ·
                      refine ⟨2361016398654348791066399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296043729744930109510397 2361016398654348791066399)
                      ·
                        rfl

theorem cell23_4598063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_4598063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598063 prefixEnd_4598063 := by exact prefixLift 4598063
  have htrace : WordTrace (prefixWord ++ tailWord_4598063) baseStart_4598063 baseEnd_4598063 := by
    simpa [prefixWord, tailWord_4598063, baseEnd_4598063] using wordTrace_append hprefix tailTrace_4598063
  have hstable : (prefixWord ++ tailWord_4598063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598063).length < 2 ^ (prefixWord ++ tailWord_4598063).sum := by decide
  have hdescent : baseEnd_4598063 < baseStart_4598063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598081 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4598081 : Nat := 118140960795 + 4598081 * 2 ^ 59
def prefixEnd_4598081 : Nat := 4983230072969 + 3 ^ 40 * 4598081 * 2
def baseEnd_4598081 : Nat := 2361025641306129720641317

theorem tailTrace_4598081 : CollatzResearch.WordTrace tailWord_4598081 prefixEnd_4598081 2361025641306129720641317 := by
  unfold tailWord_4598081
  simp only [CollatzResearch.WordTrace]
  refine ⟨167705791654945301559802097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111803861103296867706534731 167705791654945301559802097)
  ·
    refine ⟨125779343741208976169851573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167705791654945301559802097 125779343741208976169851573)
    ·
      refine ⟨11791813475738341515923585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125779343741208976169851573 11791813475738341515923585)
      ·
        refine ⟨8843860106803756136942689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11791813475738341515923585 8843860106803756136942689)
        ·
          refine ⟨6632895080102817102707017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8843860106803756136942689 6632895080102817102707017)
          ·
            refine ⟨4974671310077112827030263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6632895080102817102707017 4974671310077112827030263)
            ·
              refine ⟨7462006965115669240545395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974671310077112827030263 7462006965115669240545395)
              ·
                refine ⟨11193010447673503860818093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7462006965115669240545395 11193010447673503860818093)
                ·
                  refine ⟨4197378917877563947806785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11193010447673503860818093 4197378917877563947806785)
                  ·
                    refine ⟨3148034188408172960855089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4197378917877563947806785 3148034188408172960855089)
                    ·
                      refine ⟨2361025641306129720641317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148034188408172960855089 2361025641306129720641317)
                      ·
                        rfl

theorem cell23_4598081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4598081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598081 prefixEnd_4598081 := by exact prefixLift 4598081
  have htrace : WordTrace (prefixWord ++ tailWord_4598081) baseStart_4598081 baseEnd_4598081 := by
    simpa [prefixWord, tailWord_4598081, baseEnd_4598081] using wordTrace_append hprefix tailTrace_4598081
  have hstable : (prefixWord ++ tailWord_4598081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598081).length < 2 ^ (prefixWord ++ tailWord_4598081).sum := by decide
  have hdescent : baseEnd_4598081 < baseStart_4598081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598097 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_4598097 : Nat := 118140960795 + 4598097 * 2 ^ 59
def prefixEnd_4598097 : Nat := 4983230072969 + 3 ^ 40 * 4598097 * 2
def baseEnd_4598097 : Nat := 2361033856996601658041243

theorem tailTrace_4598097 : CollatzResearch.WordTrace tailWord_4598097 prefixEnd_4598097 2361033856996601658041243 := by
  unfold tailWord_4598097
  simp only [CollatzResearch.WordTrace]
  refine ⟨167706375222887336292384545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111804250148591557528256363 167706375222887336292384545)
  ·
    refine ⟨125779781417165502219288409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167706375222887336292384545 125779781417165502219288409)
    ·
      refine ⟨94334836062874126664466307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125779781417165502219288409 94334836062874126664466307)
      ·
        refine ⟨141502254094311189996699461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94334836062874126664466307 141502254094311189996699461)
        ·
          refine ⟨26531672642683348124381149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141502254094311189996699461 26531672642683348124381149)
          ·
            refine ⟨9949377241006255546642931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26531672642683348124381149 9949377241006255546642931)
            ·
              refine ⟨14924065861509383319964397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949377241006255546642931 14924065861509383319964397)
              ·
                refine ⟨5596524698066018744986649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14924065861509383319964397 5596524698066018744986649)
                ·
                  refine ⟨4197393523549514058739987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596524698066018744986649 4197393523549514058739987)
                  ·
                    refine ⟨6296090285324271088109981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4197393523549514058739987 6296090285324271088109981)
                    ·
                      refine ⟨2361033856996601658041243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296090285324271088109981 2361033856996601658041243)
                      ·
                        rfl

theorem cell23_4598097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_4598097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598097 prefixEnd_4598097 := by exact prefixLift 4598097
  have htrace : WordTrace (prefixWord ++ tailWord_4598097) baseStart_4598097 baseEnd_4598097 := by
    simpa [prefixWord, tailWord_4598097, baseEnd_4598097] using wordTrace_append hprefix tailTrace_4598097
  have hstable : (prefixWord ++ tailWord_4598097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598097).length < 2 ^ (prefixWord ++ tailWord_4598097).sum := by decide
  have hdescent : baseEnd_4598097 < baseStart_4598097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598223 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4]
def baseStart_4598223 : Nat := 118140960795 + 4598223 * 2 ^ 59
def prefixEnd_4598223 : Nat := 4983230072969 + 3 ^ 40 * 4598223 * 2
def baseEnd_4598223 : Nat := 2361098555559068165065663

theorem tailTrace_4598223 : CollatzResearch.WordTrace tailWord_4598223 prefixEnd_4598223 2361098555559068165065663 := by
  unfold tailWord_4598223
  simp only [CollatzResearch.WordTrace]
  refine ⟨167710970820430859811471323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111807313880287239874314215 167710970820430859811471323)
  ·
    refine ⟨251566456230646289717206985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167710970820430859811471323 251566456230646289717206985)
    ·
      refine ⟨188674842172984717287905239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251566456230646289717206985 188674842172984717287905239)
      ·
        refine ⟨283012263259477075931857859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188674842172984717287905239 283012263259477075931857859)
        ·
          refine ⟨424518394889215613897786789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283012263259477075931857859 424518394889215613897786789)
          ·
            refine ⟨79597199041727927605835023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 424518394889215613897786789 79597199041727927605835023)
            ·
              refine ⟨119395798562591891408752535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79597199041727927605835023 119395798562591891408752535)
              ·
                refine ⟨179093697843887837113128803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119395798562591891408752535 179093697843887837113128803)
                ·
                  refine ⟨268640546765831755669693205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179093697843887837113128803 268640546765831755669693205)
                  ·
                    refine ⟨12592525629648363547016869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 268640546765831755669693205 12592525629648363547016869)
                    ·
                      refine ⟨2361098555559068165065663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12592525629648363547016869 2361098555559068165065663)
                      ·
                        rfl

theorem cell23_4598223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_4598223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598223 prefixEnd_4598223 := by exact prefixLift 4598223
  have htrace : WordTrace (prefixWord ++ tailWord_4598223) baseStart_4598223 baseEnd_4598223 := by
    simpa [prefixWord, tailWord_4598223, baseEnd_4598223] using wordTrace_append hprefix tailTrace_4598223
  have hstable : (prefixWord ++ tailWord_4598223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598223).length < 2 ^ (prefixWord ++ tailWord_4598223).sum := by decide
  have hdescent : baseEnd_4598223 < baseStart_4598223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598233 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 10]
def baseStart_4598233 : Nat := 118140960795 + 4598233 * 2 ^ 59
def prefixEnd_4598233 : Nat := 4983230072969 + 3 ^ 40 * 4598233 * 2
def baseEnd_4598233 : Nat := 262344854485068125104513

theorem tailTrace_4598233 : CollatzResearch.WordTrace tailWord_4598233 prefixEnd_4598233 262344854485068125104513 := by
  unfold tailWord_4598233
  simp only [CollatzResearch.WordTrace]
  refine ⟨167711335550394631519335353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111807557033596421012890235 167711335550394631519335353)
  ·
    refine ⟨125783501662795973639501515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167711335550394631519335353 125783501662795973639501515)
    ·
      refine ⟨188675252494193960459252273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125783501662795973639501515 188675252494193960459252273)
      ·
        refine ⟨141506439370645470344439205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188675252494193960459252273 141506439370645470344439205)
        ·
          refine ⟨26532457381996025689582351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141506439370645470344439205 26532457381996025689582351)
          ·
            refine ⟨39798686072994038534373527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26532457381996025689582351 39798686072994038534373527)
            ·
              refine ⟨59698029109491057801560291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39798686072994038534373527 59698029109491057801560291)
              ·
                refine ⟨89547043664236586702340437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59698029109491057801560291 89547043664236586702340437)
                ·
                  refine ⟨262344854485068125104513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89547043664236586702340437 262344854485068125104513)
                  ·
                    rfl

theorem cell23_4598233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_4598233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598233 prefixEnd_4598233 := by exact prefixLift 4598233
  have htrace : WordTrace (prefixWord ++ tailWord_4598233) baseStart_4598233 baseEnd_4598233 := by
    simpa [prefixWord, tailWord_4598233, baseEnd_4598233] using wordTrace_append hprefix tailTrace_4598233
  have hstable : (prefixWord ++ tailWord_4598233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598233).length < 2 ^ (prefixWord ++ tailWord_4598233).sum := by decide
  have hdescent : baseEnd_4598233 < baseStart_4598233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598247 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4598247 : Nat := 118140960795 + 4598247 * 2 ^ 59
def prefixEnd_4598247 : Nat := 4983230072969 + 3 ^ 40 * 4598247 * 2
def baseEnd_4598247 : Nat := 2361110879094776071165553

theorem tailTrace_4598247 : CollatzResearch.WordTrace tailWord_4598247 prefixEnd_4598247 2361110879094776071165553 := by
  unfold tailWord_4598247
  simp only [CollatzResearch.WordTrace]
  refine ⟨167711846172343911910344995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111807897448229274606896663 167711846172343911910344995)
  ·
    refine ⟨251567769258515867865517493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167711846172343911910344995 251567769258515867865517493)
    ·
      refine ⟨23584478367985862612392265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251567769258515867865517493 23584478367985862612392265)
      ·
        refine ⟨17688358775989396959294199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23584478367985862612392265 17688358775989396959294199)
        ·
          refine ⟨26532538163984095438941299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17688358775989396959294199 26532538163984095438941299)
          ·
            refine ⟨39798807245976143158411949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26532538163984095438941299 39798807245976143158411949)
            ·
              refine ⟨14924552717241053684404481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39798807245976143158411949 14924552717241053684404481)
              ·
                refine ⟨11193414537930790263303361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14924552717241053684404481 11193414537930790263303361)
                ·
                  refine ⟨8395060903448092697477521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11193414537930790263303361 8395060903448092697477521)
                  ·
                    refine ⟨6296295677586069523108141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8395060903448092697477521 6296295677586069523108141)
                    ·
                      refine ⟨2361110879094776071165553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296295677586069523108141 2361110879094776071165553)
                      ·
                        rfl

theorem cell23_4598247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4598247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598247 prefixEnd_4598247 := by exact prefixLift 4598247
  have htrace : WordTrace (prefixWord ++ tailWord_4598247) baseStart_4598247 baseEnd_4598247 := by
    simpa [prefixWord, tailWord_4598247, baseEnd_4598247] using wordTrace_append hprefix tailTrace_4598247
  have hstable : (prefixWord ++ tailWord_4598247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598247).length < 2 ^ (prefixWord ++ tailWord_4598247).sum := by decide
  have hdescent : baseEnd_4598247 < baseStart_4598247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598250 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_4598250 : Nat := 118140960795 + 4598250 * 2 ^ 59
def prefixEnd_4598250 : Nat := 4983230072969 + 3 ^ 40 * 4598250 * 2
def baseEnd_4598250 : Nat := 262345824392971062158671

theorem tailTrace_4598250 : CollatzResearch.WordTrace tailWord_4598250 prefixEnd_4598250 262345824392971062158671 := by
  unfold tailWord_4598250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41927988897833260855676051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111807970394222028948469469 41927988897833260855676051)
  ·
    refine ⟨62891983346749891283514077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41927988897833260855676051 62891983346749891283514077)
    ·
      refine ⟨23584493755031209231317779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62891983346749891283514077 23584493755031209231317779)
      ·
        refine ⟨35376740632546813846976669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23584493755031209231317779 35376740632546813846976669)
        ·
          refine ⟨13266277737205055192616251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35376740632546813846976669 13266277737205055192616251)
          ·
            refine ⟨19899416605807582788924377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13266277737205055192616251 19899416605807582788924377)
            ·
              refine ⟨14924562454355687091693283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19899416605807582788924377 14924562454355687091693283)
              ·
                refine ⟨22386843681533530637539925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14924562454355687091693283 22386843681533530637539925)
                ·
                  refine ⟨262345824392971062158671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22386843681533530637539925 262345824392971062158671)
                  ·
                    rfl

theorem cell23_4598250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_4598250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598250 prefixEnd_4598250 := by exact prefixLift 4598250
  have htrace : WordTrace (prefixWord ++ tailWord_4598250) baseStart_4598250 baseEnd_4598250 := by
    simpa [prefixWord, tailWord_4598250, baseEnd_4598250] using wordTrace_append hprefix tailTrace_4598250
  have hstable : (prefixWord ++ tailWord_4598250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598250).length < 2 ^ (prefixWord ++ tailWord_4598250).sum := by decide
  have hdescent : baseEnd_4598250 < baseStart_4598250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598254 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_4598254 : Nat := 118140960795 + 4598254 * 2 ^ 59
def prefixEnd_4598254 : Nat := 4983230072969 + 3 ^ 40 * 4598254 * 2
def baseEnd_4598254 : Nat := 787038157819785847926007

theorem tailTrace_4598254 : CollatzResearch.WordTrace tailWord_4598254 prefixEnd_4598254 787038157819785847926007 := by
  unfold tailWord_4598254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964012685414819013231227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111808067655545701403899877 20964012685414819013231227)
  ·
    refine ⟨31446019028122228519846841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20964012685414819013231227 31446019028122228519846841)
    ·
      refine ⟨23584514271091671389885131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31446019028122228519846841 23584514271091671389885131)
      ·
        refine ⟨35376771406637507084827697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23584514271091671389885131 35376771406637507084827697)
        ·
          refine ⟨26532578554978130313620773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35376771406637507084827697 26532578554978130313620773)
          ·
            refine ⟨4974858479058399433803895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26532578554978130313620773 4974858479058399433803895)
            ·
              refine ⟨7462287718587599150705843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4974858479058399433803895 7462287718587599150705843)
              ·
                refine ⟨11193431577881398726058765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7462287718587599150705843 11193431577881398726058765)
                ·
                  refine ⟨4197536841705524522272037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11193431577881398726058765 4197536841705524522272037)
                  ·
                    refine ⟨787038157819785847926007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197536841705524522272037 787038157819785847926007)
                    ·
                      rfl

theorem cell23_4598254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_4598254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598254 prefixEnd_4598254 := by exact prefixLift 4598254
  have htrace : WordTrace (prefixWord ++ tailWord_4598254) baseStart_4598254 baseEnd_4598254 := by
    simpa [prefixWord, tailWord_4598254, baseEnd_4598254] using wordTrace_append hprefix tailTrace_4598254
  have hstable : (prefixWord ++ tailWord_4598254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598254).length < 2 ^ (prefixWord ++ tailWord_4598254).sum := by decide
  have hdescent : baseEnd_4598254 < baseStart_4598254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598277 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_4598277 : Nat := 118140960795 + 4598277 * 2 ^ 59
def prefixEnd_4598277 : Nat := 4983230072969 + 3 ^ 40 * 4598277 * 2
def baseEnd_4598277 : Nat := 2361126283514410953790415

theorem tailTrace_4598277 : CollatzResearch.WordTrace tailWord_4598277 prefixEnd_4598277 2361126283514410953790415 := by
  unfold tailWord_4598277
  simp only [CollatzResearch.WordTrace]
  refine ⟨167712940362235227033937085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111808626908156818022624723 167712940362235227033937085)
  ·
    refine ⟨62892352635838210137726407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167712940362235227033937085 62892352635838210137726407)
    ·
      refine ⟨94338528953757315206589611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62892352635838210137726407 94338528953757315206589611)
      ·
        refine ⟨141507793430635972809884417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94338528953757315206589611 141507793430635972809884417)
        ·
          refine ⟨106130845072976979607413313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141507793430635972809884417 106130845072976979607413313)
          ·
            refine ⟨79598133804732734705559985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106130845072976979607413313 79598133804732734705559985)
            ·
              refine ⟨59698600353549551029169989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79598133804732734705559985 59698600353549551029169989)
              ·
                refine ⟨11193487566290540817969373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59698600353549551029169989 11193487566290540817969373)
                ·
                  refine ⟨4197557837358952806738515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11193487566290540817969373 4197557837358952806738515)
                  ·
                    refine ⟨6296336756038429210107773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4197557837358952806738515 6296336756038429210107773)
                    ·
                      refine ⟨2361126283514410953790415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296336756038429210107773 2361126283514410953790415)
                      ·
                        rfl

theorem cell23_4598277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_4598277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598277 prefixEnd_4598277 := by exact prefixLift 4598277
  have htrace : WordTrace (prefixWord ++ tailWord_4598277) baseStart_4598277 baseEnd_4598277 := by
    simpa [prefixWord, tailWord_4598277, baseEnd_4598277] using wordTrace_append hprefix tailTrace_4598277
  have hstable : (prefixWord ++ tailWord_4598277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598277).length < 2 ^ (prefixWord ++ tailWord_4598277).sum := by decide
  have hdescent : baseEnd_4598277 < baseStart_4598277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598278 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4598278 : Nat := 118140960795 + 4598278 * 2 ^ 59
def prefixEnd_4598278 : Nat := 4983230072969 + 3 ^ 40 * 4598278 * 2
def baseEnd_4598278 : Nat := 2361126796995065449877911

theorem tailTrace_4598278 : CollatzResearch.WordTrace tailWord_4598278 prefixEnd_4598278 2361126796995065449877911 := by
  unfold tailWord_4598278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5241030526100987631397609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111808651223487736136482325 5241030526100987631397609)
  ·
    refine ⟨3930772894575740723548207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5241030526100987631397609 3930772894575740723548207)
    ·
      refine ⟨5896159341863611085322311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3930772894575740723548207 5896159341863611085322311)
      ·
        refine ⟨8844239012795416627983467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5896159341863611085322311 8844239012795416627983467)
        ·
          refine ⟨13266358519193124941975201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8844239012795416627983467 13266358519193124941975201)
          ·
            refine ⟨9949768889394843706481401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13266358519193124941975201 9949768889394843706481401)
            ·
              refine ⟨7462326667046132779861051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9949768889394843706481401 7462326667046132779861051)
              ·
                refine ⟨11193490000569199169791577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7462326667046132779861051 11193490000569199169791577)
                ·
                  refine ⟨8395117500426899377343683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11193490000569199169791577 8395117500426899377343683)
                  ·
                    refine ⟨12592676250640349066015525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8395117500426899377343683 12592676250640349066015525)
                    ·
                      refine ⟨2361126796995065449877911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12592676250640349066015525 2361126796995065449877911)
                      ·
                        rfl

theorem cell23_4598278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4598278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598278 prefixEnd_4598278 := by exact prefixLift 4598278
  have htrace : WordTrace (prefixWord ++ tailWord_4598278) baseStart_4598278 baseEnd_4598278 := by
    simpa [prefixWord, tailWord_4598278, baseEnd_4598278] using wordTrace_append hprefix tailTrace_4598278
  have hstable : (prefixWord ++ tailWord_4598278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598278).length < 2 ^ (prefixWord ++ tailWord_4598278).sum := by decide
  have hdescent : baseEnd_4598278 < baseStart_4598278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598287 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 2, 3, 2]
def baseStart_4598287 : Nat := 118140960795 + 4598287 * 2 ^ 59
def prefixEnd_4598287 : Nat := 4983230072969 + 3 ^ 40 * 4598287 * 2
def baseEnd_4598287 : Nat := 2361131418320955914665369

theorem tailTrace_4598287 : CollatzResearch.WordTrace tailWord_4598287 prefixEnd_4598287 2361131418320955914665369 := by
  unfold tailWord_4598287
  simp only [CollatzResearch.WordTrace]
  refine ⟨167713305092198998741801115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111808870061465999161200743 167713305092198998741801115)
  ·
    refine ⟨251569957638298498112701673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167713305092198998741801115 251569957638298498112701673)
    ·
      refine ⟨188677468228723873584526255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251569957638298498112701673 188677468228723873584526255)
      ·
        refine ⟨283016202343085810376789383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188677468228723873584526255 283016202343085810376789383)
        ·
          refine ⟨424524303514628715565184075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283016202343085810376789383 424524303514628715565184075)
          ·
            refine ⟨636786455271943073347776113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424524303514628715565184075 636786455271943073347776113)
            ·
              refine ⟨477589841453957305010832085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636786455271943073347776113 477589841453957305010832085)
              ·
                refine ⟨11193511909077124336191377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 477589841453957305010832085 11193511909077124336191377)
                ·
                  refine ⟨8395133931807843252143533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11193511909077124336191377 8395133931807843252143533)
                  ·
                    refine ⟨3148175224427941219553825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8395133931807843252143533 3148175224427941219553825)
                    ·
                      refine ⟨2361131418320955914665369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148175224427941219553825 2361131418320955914665369)
                      ·
                        rfl

theorem cell23_4598287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3, 2].length) (baseStart_4598287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598287 prefixEnd_4598287 := by exact prefixLift 4598287
  have htrace : WordTrace (prefixWord ++ tailWord_4598287) baseStart_4598287 baseEnd_4598287 := by
    simpa [prefixWord, tailWord_4598287, baseEnd_4598287] using wordTrace_append hprefix tailTrace_4598287
  have hstable : (prefixWord ++ tailWord_4598287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598287).length < 2 ^ (prefixWord ++ tailWord_4598287).sum := by decide
  have hdescent : baseEnd_4598287 < baseStart_4598287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598320 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_4598320 : Nat := 118140960795 + 4598320 * 2 ^ 59
def prefixEnd_4598320 : Nat := 4983230072969 + 3 ^ 40 * 4598320 * 2
def baseEnd_4598320 : Nat := 2361148363182554285552717

theorem tailTrace_4598320 : CollatzResearch.WordTrace tailWord_4598320 prefixEnd_4598320 2361148363182554285552717 := by
  unfold tailWord_4598320
  simp only [CollatzResearch.WordTrace]
  refine ⟨83857254350539722688876207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111809672467386296918501609 83857254350539722688876207)
  ·
    refine ⟨125785881525809584033314311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83857254350539722688876207 125785881525809584033314311)
    ·
      refine ⟨188678822288714376049971467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125785881525809584033314311 188678822288714376049971467)
      ·
        refine ⟨283018233433071564074957201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188678822288714376049971467 283018233433071564074957201)
        ·
          refine ⟨212263675074803673056217901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283018233433071564074957201 212263675074803673056217901)
          ·
            refine ⟨79598878153051377396081713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212263675074803673056217901 79598878153051377396081713)
            ·
              refine ⟨59699158614788533047061285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79598878153051377396081713 59699158614788533047061285)
              ·
                refine ⟨11193592240272849946323991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59699158614788533047061285 11193592240272849946323991)
                ·
                  refine ⟨16790388360409274919485987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11193592240272849946323991 16790388360409274919485987)
                  ·
                    refine ⟨25185582540613912379228981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16790388360409274919485987 25185582540613912379228981)
                    ·
                      refine ⟨2361148363182554285552717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25185582540613912379228981 2361148363182554285552717)
                      ·
                        rfl

theorem cell23_4598320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_4598320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598320 prefixEnd_4598320 := by exact prefixLift 4598320
  have htrace : WordTrace (prefixWord ++ tailWord_4598320) baseStart_4598320 baseEnd_4598320 := by
    simpa [prefixWord, tailWord_4598320, baseEnd_4598320] using wordTrace_append hprefix tailTrace_4598320
  have hstable : (prefixWord ++ tailWord_4598320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598320).length < 2 ^ (prefixWord ++ tailWord_4598320).sum := by decide
  have hdescent : baseEnd_4598320 < baseStart_4598320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598327 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 2, 4]
def baseStart_4598327 : Nat := 118140960795 + 4598327 * 2 ^ 59
def prefixEnd_4598327 : Nat := 4983230072969 + 3 ^ 40 * 4598327 * 2
def baseEnd_4598327 : Nat := 787050652515711919388395

theorem tailTrace_4598327 : CollatzResearch.WordTrace tailWord_4598327 prefixEnd_4598327 787050652515711919388395 := by
  unfold tailWord_4598327
  simp only [CollatzResearch.WordTrace]
  refine ⟨167714764012054085573257235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111809842674702723715504823 167714764012054085573257235)
  ·
    refine ⟨251572146018081128359885853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167714764012054085573257235 251572146018081128359885853)
    ·
      refine ⟨94339554756780423134957195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251572146018081128359885853 94339554756780423134957195)
      ·
        refine ⟨141509332135170634702435793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94339554756780423134957195 141509332135170634702435793)
        ·
          refine ⟨106131999101377976026826845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141509332135170634702435793 106131999101377976026826845)
          ·
            refine ⟨39799499663016741010060067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106131999101377976026826845 39799499663016741010060067)
            ·
              refine ⟨59699249494525111515090101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39799499663016741010060067 59699249494525111515090101)
              ·
                refine ⟨5596804640111729204539697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59699249494525111515090101 5596804640111729204539697)
                ·
                  refine ⟨4197603480083796903404773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596804640111729204539697 4197603480083796903404773)
                  ·
                    refine ⟨787050652515711919388395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4197603480083796903404773 787050652515711919388395)
                    ·
                      rfl

theorem cell23_4598327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_4598327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598327 prefixEnd_4598327 := by exact prefixLift 4598327
  have htrace : WordTrace (prefixWord ++ tailWord_4598327) baseStart_4598327 baseEnd_4598327 := by
    simpa [prefixWord, tailWord_4598327, baseEnd_4598327] using wordTrace_append hprefix tailTrace_4598327
  have hstable : (prefixWord ++ tailWord_4598327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598327).length < 2 ^ (prefixWord ++ tailWord_4598327).sum := by decide
  have hdescent : baseEnd_4598327 < baseStart_4598327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598351 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 1, 2, 2]
def baseStart_4598351 : Nat := 118140960795 + 4598351 * 2 ^ 59
def prefixEnd_4598351 : Nat := 4983230072969 + 3 ^ 40 * 4598351 * 2
def baseEnd_4598351 : Nat := 2361164281082843664265075

theorem tailTrace_4598351 : CollatzResearch.WordTrace tailWord_4598351 prefixEnd_4598351 2361164281082843664265075 := by
  unfold tailWord_4598351
  simp only [CollatzResearch.WordTrace]
  refine ⟨167715639363967137672130907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111810426242644758448087271 167715639363967137672130907)
  ·
    refine ⟨251573459045950706508196361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167715639363967137672130907 251573459045950706508196361)
    ·
      refine ⟨188680094284463029881147271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251573459045950706508196361 188680094284463029881147271)
      ·
        refine ⟨283020141426694544821720907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188680094284463029881147271 283020141426694544821720907)
        ·
          refine ⟨424530212140041817232581361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283020141426694544821720907 424530212140041817232581361)
          ·
            refine ⟨318397659105031362924436021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424530212140041817232581361 318397659105031362924436021)
            ·
              refine ⟨29849780541096690274165877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 318397659105031362924436021 29849780541096690274165877)
              ·
                refine ⟨2798416925727814713203051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29849780541096690274165877 2798416925727814713203051)
                ·
                  refine ⟨4197625388591722069804577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798416925727814713203051 4197625388591722069804577)
                  ·
                    refine ⟨3148219041443791552353433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4197625388591722069804577 3148219041443791552353433)
                    ·
                      refine ⟨2361164281082843664265075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148219041443791552353433 2361164281082843664265075)
                      ·
                        rfl

theorem cell23_4598351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 2, 2].length) (baseStart_4598351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598351 prefixEnd_4598351 := by exact prefixLift 4598351
  have htrace : WordTrace (prefixWord ++ tailWord_4598351) baseStart_4598351 baseEnd_4598351 := by
    simpa [prefixWord, tailWord_4598351, baseEnd_4598351] using wordTrace_append hprefix tailTrace_4598351
  have hstable : (prefixWord ++ tailWord_4598351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598351).length < 2 ^ (prefixWord ++ tailWord_4598351).sum := by decide
  have hdescent : baseEnd_4598351 < baseStart_4598351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598354 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_4598354 : Nat := 118140960795 + 4598354 * 2 ^ 59
def prefixEnd_4598354 : Nat := 4983230072969 + 3 ^ 40 * 4598354 * 2
def baseEnd_4598354 : Nat := 2361165821524807152527561

theorem tailTrace_4598354 : CollatzResearch.WordTrace tailWord_4598354 prefixEnd_4598354 2361165821524807152527561 := by
  unfold tailWord_4598354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41928937195739067296122529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111810499188637512789660077 41928937195739067296122529)
  ·
    refine ⟨31446702896804300472091897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41928937195739067296122529 31446702896804300472091897)
    ·
      refine ⟨23585027172603225354068923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31446702896804300472091897 23585027172603225354068923)
      ·
        refine ⟨35377540758904838031103385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23585027172603225354068923 35377540758904838031103385)
        ·
          refine ⟨26533155569178628523327539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35377540758904838031103385 26533155569178628523327539)
          ·
            refine ⟨39799733353767942784991309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26533155569178628523327539 39799733353767942784991309)
            ·
              refine ⟨14924900007662978544371741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39799733353767942784991309 14924900007662978544371741)
              ·
                refine ⟨5596837502873616954139403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14924900007662978544371741 5596837502873616954139403)
                ·
                  refine ⟨8395256254310425431209105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5596837502873616954139403 8395256254310425431209105)
                  ·
                    refine ⟨6296442190732819073406829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8395256254310425431209105 6296442190732819073406829)
                    ·
                      refine ⟨2361165821524807152527561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296442190732819073406829 2361165821524807152527561)
                      ·
                        rfl

theorem cell23_4598354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_4598354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598354 prefixEnd_4598354 := by exact prefixLift 4598354
  have htrace : WordTrace (prefixWord ++ tailWord_4598354) baseStart_4598354 baseEnd_4598354 := by
    simpa [prefixWord, tailWord_4598354, baseEnd_4598354] using wordTrace_append hprefix tailTrace_4598354
  have hstable : (prefixWord ++ tailWord_4598354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598354).length < 2 ^ (prefixWord ++ tailWord_4598354).sum := by decide
  have hdescent : baseEnd_4598354 < baseStart_4598354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598457 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4598457 : Nat := 118140960795 + 4598457 * 2 ^ 59
def prefixEnd_4598457 : Nat := 4983230072969 + 3 ^ 40 * 4598457 * 2
def baseEnd_4598457 : Nat := 2361218710032220249539587

theorem tailTrace_4598457 : CollatzResearch.WordTrace tailWord_4598457 prefixEnd_4598457 2361218710032220249539587 := by
  unfold tailWord_4598457
  simp only [CollatzResearch.WordTrace]
  refine ⟨167719505501583117775489625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111813003667722078516993083 167719505501583117775489625)
  ·
    refine ⟨125789629126187338331617219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167719505501583117775489625 125789629126187338331617219)
    ·
      refine ⟨188684443689281007497425829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125789629126187338331617219 188684443689281007497425829)
      ·
        refine ⟨35378333191740188905767343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188684443689281007497425829 35378333191740188905767343)
        ·
          refine ⟨53067499787610283358651015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35378333191740188905767343 53067499787610283358651015)
          ·
            refine ⟨79601249681415425037976523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53067499787610283358651015 79601249681415425037976523)
            ·
              refine ⟨119401874522123137556964785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79601249681415425037976523 119401874522123137556964785)
              ·
                refine ⟨89551405891592353167723589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119401874522123137556964785 89551405891592353167723589)
                ·
                  refine ⟨16790888604673566218948173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89551405891592353167723589 16790888604673566218948173)
                  ·
                    refine ⟨6296583226752587332105565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16790888604673566218948173 6296583226752587332105565)
                    ·
                      refine ⟨2361218710032220249539587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296583226752587332105565 2361218710032220249539587)
                      ·
                        rfl

theorem cell23_4598457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4598457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598457 prefixEnd_4598457 := by exact prefixLift 4598457
  have htrace : WordTrace (prefixWord ++ tailWord_4598457) baseStart_4598457 baseEnd_4598457 := by
    simpa [prefixWord, tailWord_4598457, baseEnd_4598457] using wordTrace_append hprefix tailTrace_4598457
  have hstable : (prefixWord ++ tailWord_4598457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598457).length < 2 ^ (prefixWord ++ tailWord_4598457).sum := by decide
  have hdescent : baseEnd_4598457 < baseStart_4598457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598487 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_4598487 : Nat := 118140960795 + 4598487 * 2 ^ 59
def prefixEnd_4598487 : Nat := 4983230072969 + 3 ^ 40 * 4598487 * 2
def baseEnd_4598487 : Nat := 2361234114451855132164449

theorem tailTrace_4598487 : CollatzResearch.WordTrace tailWord_4598487 prefixEnd_4598487 2361234114451855132164449 := by
  unfold tailWord_4598487
  simp only [CollatzResearch.WordTrace]
  refine ⟨167720599691474432899081715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111813733127649621932721143 167720599691474432899081715)
  ·
    refine ⟨251580899537211649348622573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167720599691474432899081715 251580899537211649348622573)
    ·
      refine ⟨94342837326454368505733465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251580899537211649348622573 94342837326454368505733465)
      ·
        refine ⟨70757127994840776379300099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94342837326454368505733465 70757127994840776379300099)
        ·
          refine ⟨106135691992261164568950149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70757127994840776379300099 106135691992261164568950149)
          ·
            refine ⟨19900442248548968356678153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106135691992261164568950149 19900442248548968356678153)
            ·
              refine ⟨14925331686411726267508615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19900442248548968356678153 14925331686411726267508615)
              ·
                refine ⟨22387997529617589401262923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14925331686411726267508615 22387997529617589401262923)
                ·
                  refine ⟨33581996294426384101894385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22387997529617589401262923 33581996294426384101894385)
                  ·
                    refine ⟨25186497220819788076420789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33581996294426384101894385 25186497220819788076420789)
                    ·
                      refine ⟨2361234114451855132164449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25186497220819788076420789 2361234114451855132164449)
                      ·
                        rfl

theorem cell23_4598487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_4598487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598487 prefixEnd_4598487 := by exact prefixLift 4598487
  have htrace : WordTrace (prefixWord ++ tailWord_4598487) baseStart_4598487 baseEnd_4598487 := by
    simpa [prefixWord, tailWord_4598487, baseEnd_4598487] using wordTrace_append hprefix tailTrace_4598487
  have hstable : (prefixWord ++ tailWord_4598487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598487).length < 2 ^ (prefixWord ++ tailWord_4598487).sum := by decide
  have hdescent : baseEnd_4598487 < baseStart_4598487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598514 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4598514 : Nat := 118140960795 + 4598514 * 2 ^ 59
def prefixEnd_4598514 : Nat := 4983230072969 + 3 ^ 40 * 4598514 * 2
def baseEnd_4598514 : Nat := 2361247978429526526526825

theorem tailTrace_4598514 : CollatzResearch.WordTrace tailWord_4598514 prefixEnd_4598514 2361247978429526526526825 := by
  unfold tailWord_4598514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41930396115594154127578649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111814389641584411006876397 41930396115594154127578649)
  ·
    refine ⟨31447797086695615595683987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41930396115594154127578649 31447797086695615595683987)
    ·
      refine ⟨47171695630043423393525981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31447797086695615595683987 47171695630043423393525981)
      ·
        refine ⟨17689385861266283772572243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47171695630043423393525981 17689385861266283772572243)
        ·
          refine ⟨26534078791899425658858365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17689385861266283772572243 26534078791899425658858365)
          ·
            refine ⟨9950279546962284622071887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26534078791899425658858365 9950279546962284622071887)
            ·
              refine ⟨14925419320443426933107831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9950279546962284622071887 14925419320443426933107831)
              ·
                refine ⟨22388128980665140399661747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14925419320443426933107831 22388128980665140399661747)
                ·
                  refine ⟨33582193470997710599492621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22388128980665140399661747 33582193470997710599492621)
                  ·
                    refine ⟨12593322551624141474809733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33582193470997710599492621 12593322551624141474809733)
                    ·
                      refine ⟨2361247978429526526526825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12593322551624141474809733 2361247978429526526526825)
                      ·
                        rfl

theorem cell23_4598514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4598514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598514 prefixEnd_4598514 := by exact prefixLift 4598514
  have htrace : WordTrace (prefixWord ++ tailWord_4598514) baseStart_4598514 baseEnd_4598514 := by
    simpa [prefixWord, tailWord_4598514, baseEnd_4598514] using wordTrace_append hprefix tailTrace_4598514
  have hstable : (prefixWord ++ tailWord_4598514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598514).length < 2 ^ (prefixWord ++ tailWord_4598514).sum := by decide
  have hdescent : baseEnd_4598514 < baseStart_4598514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598584 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_4598584 : Nat := 118140960795 + 4598584 * 2 ^ 59
def prefixEnd_4598584 : Nat := 4983230072969 + 3 ^ 40 * 4598584 * 2
def baseEnd_4598584 : Nat := 787094640691780417550501

theorem tailTrace_4598584 : CollatzResearch.WordTrace tailWord_4598584 prefixEnd_4598584 787094640691780417550501 := by
  unfold tailWord_4598584
  simp only [CollatzResearch.WordTrace]
  refine ⟨83862068786061509232681403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111816091714748678976908537 83862068786061509232681403)
  ·
    refine ⟨125793103179092263849022105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83862068786061509232681403 125793103179092263849022105)
    ·
      refine ⟨94344827384319197886766579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125793103179092263849022105 94344827384319197886766579)
      ·
        refine ⟨141517241076478796830149869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94344827384319197886766579 141517241076478796830149869)
        ·
          refine ⟨53068965403679548811306201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141517241076478796830149869 53068965403679548811306201)
          ·
            refine ⟨39801724052759661608479651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53068965403679548811306201 39801724052759661608479651)
            ·
              refine ⟨59702586079139492412719477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39801724052759661608479651 59702586079139492412719477)
              ·
                refine ⟨5597117444919327413692451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59702586079139492412719477 5597117444919327413692451)
                ·
                  refine ⟨8395676167378991120538677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597117444919327413692451 8395676167378991120538677)
                  ·
                    refine ⟨787094640691780417550501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8395676167378991120538677 787094640691780417550501)
                    ·
                      rfl

theorem cell23_4598584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_4598584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598584 prefixEnd_4598584 := by exact prefixLift 4598584
  have htrace : WordTrace (prefixWord ++ tailWord_4598584) baseStart_4598584 baseEnd_4598584 := by
    simpa [prefixWord, tailWord_4598584, baseEnd_4598584] using wordTrace_append hprefix tailTrace_4598584
  have hstable : (prefixWord ++ tailWord_4598584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598584).length < 2 ^ (prefixWord ++ tailWord_4598584).sum := by decide
  have hdescent : baseEnd_4598584 < baseStart_4598584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598591 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 4, 3, 2]
def baseStart_4598591 : Nat := 118140960795 + 4598591 * 2 ^ 59
def prefixEnd_4598591 : Nat := 4983230072969 + 3 ^ 40 * 4598591 * 2
def baseEnd_4598591 : Nat := 2361287516439922725263971

theorem tailTrace_4598591 : CollatzResearch.WordTrace tailWord_4598591 prefixEnd_4598591 2361287516439922725263971 := by
  unfold tailWord_4598591
  simp only [CollatzResearch.WordTrace]
  refine ⟨167724392883097658660867627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111816261922065105773911751 167724392883097658660867627)
  ·
    refine ⟨251586589324646487991301441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167724392883097658660867627 251586589324646487991301441)
    ·
      refine ⟨188689941993484865993476081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251586589324646487991301441 188689941993484865993476081)
      ·
        refine ⟨141517456495113649495107061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188689941993484865993476081 141517456495113649495107061)
        ·
          refine ⟨13267261546416904640166287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141517456495113649495107061 13267261546416904640166287)
          ·
            refine ⟨19900892319625356960249431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13267261546416904640166287 19900892319625356960249431)
            ·
              refine ⟨29851338479438035440374147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19900892319625356960249431 29851338479438035440374147)
              ·
                refine ⟨44777007719157053160561221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29851338479438035440374147 44777007719157053160561221)
                ·
                  refine ⟨8395688947341947467605229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44777007719157053160561221 8395688947341947467605229)
                  ·
                    refine ⟨3148383355253230300351961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8395688947341947467605229 3148383355253230300351961)
                    ·
                      refine ⟨2361287516439922725263971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148383355253230300351961 2361287516439922725263971)
                      ·
                        rfl

theorem cell23_4598591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_4598591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598591 prefixEnd_4598591 := by exact prefixLift 4598591
  have htrace : WordTrace (prefixWord ++ tailWord_4598591) baseStart_4598591 baseEnd_4598591 := by
    simpa [prefixWord, tailWord_4598591, baseEnd_4598591] using wordTrace_append hprefix tailTrace_4598591
  have hstable : (prefixWord ++ tailWord_4598591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598591).length < 2 ^ (prefixWord ++ tailWord_4598591).sum := by decide
  have hdescent : baseEnd_4598591 < baseStart_4598591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598597 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_4598597 : Nat := 118140960795 + 4598597 * 2 ^ 59
def prefixEnd_4598597 : Nat := 4983230072969 + 3 ^ 40 * 4598597 * 2
def baseEnd_4598597 : Nat := 787096865774616567262981

theorem tailTrace_4598597 : CollatzResearch.WordTrace tailWord_4598597 prefixEnd_4598597 787096865774616567262981 := by
  unfold tailWord_4598597
  simp only [CollatzResearch.WordTrace]
  refine ⟨167724611721075921685586045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111816407814050614457057363 167724611721075921685586045)
  ·
    refine ⟨62896729395403470632094767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167724611721075921685586045 62896729395403470632094767)
    ·
      refine ⟨94345094093105205948142151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62896729395403470632094767 94345094093105205948142151)
      ·
        refine ⟨141517641139657808922213227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94345094093105205948142151 141517641139657808922213227)
        ·
          refine ⟨212276461709486713383319841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141517641139657808922213227 212276461709486713383319841)
          ·
            refine ⟨159207346282115035037489881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212276461709486713383319841 159207346282115035037489881)
            ·
              refine ⟨119405509711586276278117411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159207346282115035037489881 119405509711586276278117411)
              ·
                refine ⟨179108264567379414417176117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119405509711586276278117411 179108264567379414417176117)
                ·
                  refine ⟨16791399803191820101610261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179108264567379414417176117 16791399803191820101610261)
                  ·
                    refine ⟨787096865774616567262981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16791399803191820101610261 787096865774616567262981)
                    ·
                      rfl

theorem cell23_4598597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_4598597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598597 prefixEnd_4598597 := by exact prefixLift 4598597
  have htrace : WordTrace (prefixWord ++ tailWord_4598597) baseStart_4598597 baseEnd_4598597 := by
    simpa [prefixWord, tailWord_4598597, baseEnd_4598597] using wordTrace_append hprefix tailTrace_4598597
  have hstable : (prefixWord ++ tailWord_4598597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598597).length < 2 ^ (prefixWord ++ tailWord_4598597).sum := by decide
  have hdescent : baseEnd_4598597 < baseStart_4598597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598605 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4598605 : Nat := 118140960795 + 4598605 * 2 ^ 59
def prefixEnd_4598605 : Nat := 4983230072969 + 3 ^ 40 * 4598605 * 2
def baseEnd_4598605 : Nat := 262366078352120630054323

theorem tailTrace_4598605 : CollatzResearch.WordTrace tailWord_4598605 prefixEnd_4598605 262366078352120630054323 := by
  unfold tailWord_4598605
  simp only [CollatzResearch.WordTrace]
  refine ⟨167724903505046939051877269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111816602336697959367918179 167724903505046939051877269)
  ·
    refine ⟨7862104851799075268056747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167724903505046939051877269 7862104851799075268056747)
    ·
      refine ⟨11793157277698612902085121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7862104851799075268056747 11793157277698612902085121)
      ·
        refine ⟨8844867958273959676563841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11793157277698612902085121 8844867958273959676563841)
        ·
          refine ⟨6633650968705469757422881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8844867958273959676563841 6633650968705469757422881)
          ·
            refine ⟨4975238226529102318067161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6633650968705469757422881 4975238226529102318067161)
            ·
              refine ⟨3731428669896826738550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975238226529102318067161 3731428669896826738550371)
              ·
                refine ⟨5597143004845240107825557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731428669896826738550371 5597143004845240107825557)
                ·
                  refine ⟨262366078352120630054323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5597143004845240107825557 262366078352120630054323)
                  ·
                    rfl

theorem cell23_4598605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4598605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598605 prefixEnd_4598605 := by exact prefixLift 4598605
  have htrace : WordTrace (prefixWord ++ tailWord_4598605) baseStart_4598605 baseEnd_4598605 := by
    simpa [prefixWord, tailWord_4598605, baseEnd_4598605] using wordTrace_append hprefix tailTrace_4598605
  have hstable : (prefixWord ++ tailWord_4598605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598605).length < 2 ^ (prefixWord ++ tailWord_4598605).sum := by decide
  have hdescent : baseEnd_4598605 < baseStart_4598605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598641 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_4598641 : Nat := 118140960795 + 4598641 * 2 ^ 59
def prefixEnd_4598641 : Nat := 4983230072969 + 3 ^ 40 * 4598641 * 2
def baseEnd_4598641 : Nat := 2361313190472647529638741

theorem tailTrace_4598641 : CollatzResearch.WordTrace tailWord_4598641 prefixEnd_4598641 2361313190472647529638741 := by
  unfold tailWord_4598641
  simp only [CollatzResearch.WordTrace]
  refine ⟨167726216532916517200187777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111817477688611011466791851 167726216532916517200187777)
  ·
    refine ⟨125794662399687387900140833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167726216532916517200187777 125794662399687387900140833)
    ·
      refine ⟨94345996799765540925105625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125794662399687387900140833 94345996799765540925105625)
      ·
        refine ⟨70759497599824155693829219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94345996799765540925105625 70759497599824155693829219)
        ·
          refine ⟨106139246399736233540743829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70759497599824155693829219 106139246399736233540743829)
          ·
            refine ⟨4975277174987635947222367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106139246399736233540743829 4975277174987635947222367)
            ·
              refine ⟨7462915762481453920833551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975277174987635947222367 7462915762481453920833551)
              ·
                refine ⟨11194373643722180881250327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7462915762481453920833551 11194373643722180881250327)
                ·
                  refine ⟨16791560465583271321875491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11194373643722180881250327 16791560465583271321875491)
                  ·
                    refine ⟨25187340698374906982813237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16791560465583271321875491 25187340698374906982813237)
                    ·
                      refine ⟨2361313190472647529638741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25187340698374906982813237 2361313190472647529638741)
                      ·
                        rfl

theorem cell23_4598641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_4598641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598641 prefixEnd_4598641 := by exact prefixLift 4598641
  have htrace : WordTrace (prefixWord ++ tailWord_4598641) baseStart_4598641 baseEnd_4598641 := by
    simpa [prefixWord, tailWord_4598641, baseEnd_4598641] using wordTrace_append hprefix tailTrace_4598641
  have hstable : (prefixWord ++ tailWord_4598641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598641).length < 2 ^ (prefixWord ++ tailWord_4598641).sum := by decide
  have hdescent : baseEnd_4598641 < baseStart_4598641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598711 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_4598711 : Nat := 118140960795 + 4598711 * 2 ^ 59
def prefixEnd_4598711 : Nat := 4983230072969 + 3 ^ 40 * 4598711 * 2
def baseEnd_4598711 : Nat := 2361349134118462255763419

theorem tailTrace_4598711 : CollatzResearch.WordTrace tailWord_4598711 prefixEnd_4598711 2361349134118462255763419 := by
  unfold tailWord_4598711
  simp only [CollatzResearch.WordTrace]
  refine ⟨167728769642662919155235987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111819179761775279436823991 167728769642662919155235987)
  ·
    refine ⟨251593154463994378732853981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167728769642662919155235987 251593154463994378732853981)
    ·
      refine ⟨94347432923997892024820243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251593154463994378732853981 94347432923997892024820243)
      ·
        refine ⟨141521149385996838037230365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94347432923997892024820243 141521149385996838037230365)
        ·
          refine ⟨53070431019748814263961387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141521149385996838037230365 53070431019748814263961387)
          ·
            refine ⟨79605646529623221395942081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53070431019748814263961387 79605646529623221395942081)
            ·
              refine ⟨59704234897217416046956561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79605646529623221395942081 59704234897217416046956561)
              ·
                refine ⟨44778176172913062035217421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59704234897217416046956561 44778176172913062035217421)
                ·
                  refine ⟨16791816064842398263206533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44778176172913062035217421 16791816064842398263206533)
                  ·
                    refine ⟨3148465512157949674351225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16791816064842398263206533 3148465512157949674351225)
                    ·
                      refine ⟨2361349134118462255763419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148465512157949674351225 2361349134118462255763419)
                      ·
                        rfl

theorem cell23_4598711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_4598711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598711 prefixEnd_4598711 := by exact prefixLift 4598711
  have htrace : WordTrace (prefixWord ++ tailWord_4598711) baseStart_4598711 baseEnd_4598711 := by
    simpa [prefixWord, tailWord_4598711, baseEnd_4598711] using wordTrace_append hprefix tailTrace_4598711
  have hstable : (prefixWord ++ tailWord_4598711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598711).length < 2 ^ (prefixWord ++ tailWord_4598711).sum := by decide
  have hdescent : baseEnd_4598711 < baseStart_4598711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598726 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4598726 : Nat := 118140960795 + 4598726 * 2 ^ 59
def prefixEnd_4598726 : Nat := 4983230072969 + 3 ^ 40 * 4598726 * 2
def baseEnd_4598726 : Nat := 2361356836328279697075851

theorem tailTrace_4598726 : CollatzResearch.WordTrace tailWord_4598726 prefixEnd_4598726 2361356836328279697075851 := by
  unfold tailWord_4598726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5241541148050268022407251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111819544491739051144688021 5241541148050268022407251)
  ·
    refine ⟨7862311722075402033610877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5241541148050268022407251 7862311722075402033610877)
    ·
      refine ⟨2948366895778275762604079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7862311722075402033610877 2948366895778275762604079)
      ·
        refine ⟨4422550343667413643906119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948366895778275762604079 4422550343667413643906119)
        ·
          refine ⟨6633825515501120465859179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422550343667413643906119 6633825515501120465859179)
          ·
            refine ⟨9950738273251680698788769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633825515501120465859179 9950738273251680698788769)
            ·
              refine ⟨7463053704938760524091577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9950738273251680698788769 7463053704938760524091577)
              ·
                refine ⟨5597290278704070393068683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463053704938760524091577 5597290278704070393068683)
                ·
                  refine ⟨8395935418056105589603025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597290278704070393068683 8395935418056105589603025)
                  ·
                    refine ⟨6296951563542079192202269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8395935418056105589603025 6296951563542079192202269)
                    ·
                      refine ⟨2361356836328279697075851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6296951563542079192202269 2361356836328279697075851)
                      ·
                        rfl

theorem cell23_4598726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4598726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598726 prefixEnd_4598726 := by exact prefixLift 4598726
  have htrace : WordTrace (prefixWord ++ tailWord_4598726) baseStart_4598726 baseEnd_4598726 := by
    simpa [prefixWord, tailWord_4598726, baseEnd_4598726] using wordTrace_append hprefix tailTrace_4598726
  have hstable : (prefixWord ++ tailWord_4598726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598726).length < 2 ^ (prefixWord ++ tailWord_4598726).sum := by decide
  have hdescent : baseEnd_4598726 < baseStart_4598726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598798 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_4598798 : Nat := 118140960795 + 4598798 * 2 ^ 59
def prefixEnd_4598798 : Nat := 4983230072969 + 3 ^ 40 * 4598798 * 2
def baseEnd_4598798 : Nat := 787131268978467805125173

theorem tailTrace_4598798 : CollatzResearch.WordTrace tailWord_4598798 prefixEnd_4598798 787131268978467805125173 := by
  unfold tailWord_4598798
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966492849168466626706631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111821295195565155342435365 20966492849168466626706631)
  ·
    refine ⟨31449739273752699940059947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20966492849168466626706631 31449739273752699940059947)
    ·
      refine ⟨47174608910629049910089921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31449739273752699940059947 47174608910629049910089921)
      ·
        refine ⟨35380956682971787432567441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47174608910629049910089921 35380956682971787432567441)
        ·
          refine ⟨26535717512228840574425581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35380956682971787432567441 26535717512228840574425581)
          ·
            refine ⟨9950894067085815215409593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26535717512228840574425581 9950894067085815215409593)
            ·
              refine ⟨7463170550314361411557195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9950894067085815215409593 7463170550314361411557195)
              ·
                refine ⟨11194755825471542117335793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463170550314361411557195 11194755825471542117335793)
                ·
                  refine ⟨8396066869103656588001845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11194755825471542117335793 8396066869103656588001845)
                  ·
                    refine ⟨787131268978467805125173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8396066869103656588001845 787131268978467805125173)
                    ·
                      rfl

theorem cell23_4598798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_4598798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598798 prefixEnd_4598798 := by exact prefixLift 4598798
  have htrace : WordTrace (prefixWord ++ tailWord_4598798) baseStart_4598798 baseEnd_4598798 := by
    simpa [prefixWord, tailWord_4598798, baseEnd_4598798] using wordTrace_append hprefix tailTrace_4598798
  have hstable : (prefixWord ++ tailWord_4598798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598798).length < 2 ^ (prefixWord ++ tailWord_4598798).sum := by decide
  have hdescent : baseEnd_4598798 < baseStart_4598798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598818 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4598818 : Nat := 118140960795 + 4598818 * 2 ^ 59
def prefixEnd_4598818 : Nat := 4983230072969 + 3 ^ 40 * 4598818 * 2
def baseEnd_4598818 : Nat := 2361404076548493337125427

theorem tailTrace_4598818 : CollatzResearch.WordTrace tailWord_4598818 prefixEnd_4598818 2361404076548493337125427 := by
  unfold tailWord_4598818
  simp only [CollatzResearch.WordTrace]
  refine ⟨41933168063318819107345277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111821781502183517619587405 41933168063318819107345277)
  ·
    refine ⟨15724938023744557165254479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41933168063318819107345277 15724938023744557165254479)
    ·
      refine ⟨23587407035616835747881719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15724938023744557165254479 23587407035616835747881719)
      ·
        refine ⟨35381110553425253621822579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23587407035616835747881719 35381110553425253621822579)
        ·
          refine ⟨53071665830137880432733869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35381110553425253621822579 53071665830137880432733869)
          ·
            refine ⟨19901874686301705162275201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53071665830137880432733869 19901874686301705162275201)
            ·
              refine ⟨14926406014726278871706401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19901874686301705162275201 14926406014726278871706401)
              ·
                refine ⟨11194804511044709153779801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14926406014726278871706401 11194804511044709153779801)
                ·
                  refine ⟨8396103383283531865334851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11194804511044709153779801 8396103383283531865334851)
                  ·
                    refine ⟨12594155074925297798002277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8396103383283531865334851 12594155074925297798002277)
                    ·
                      refine ⟨2361404076548493337125427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12594155074925297798002277 2361404076548493337125427)
                      ·
                        rfl

theorem cell23_4598818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4598818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598818 prefixEnd_4598818 := by exact prefixLift 4598818
  have htrace : WordTrace (prefixWord ++ tailWord_4598818) baseStart_4598818 baseEnd_4598818 := by
    simpa [prefixWord, tailWord_4598818, baseEnd_4598818] using wordTrace_append hprefix tailTrace_4598818
  have hstable : (prefixWord ++ tailWord_4598818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598818).length < 2 ^ (prefixWord ++ tailWord_4598818).sum := by decide
  have hdescent : baseEnd_4598818 < baseStart_4598818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598855 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_4598855 : Nat := 118140960795 + 4598855 * 2 ^ 59
def prefixEnd_4598855 : Nat := 4983230072969 + 3 ^ 40 * 4598855 * 2
def baseEnd_4598855 : Nat := 2361423075332709692362757

theorem tailTrace_4598855 : CollatzResearch.WordTrace tailWord_4598855 prefixEnd_4598855 2361423075332709692362757 := by
  unfold tailWord_4598855
  simp only [CollatzResearch.WordTrace]
  refine ⟨167734021754141231748478019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111822681169427487832318679 167734021754141231748478019)
  ·
    refine ⟨251601032631211847622717029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167734021754141231748478019 251601032631211847622717029)
    ·
      refine ⟨47175193618352221429259443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251601032631211847622717029 47175193618352221429259443)
      ·
        refine ⟨70762790427528332143889165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47175193618352221429259443 70762790427528332143889165)
        ·
          refine ⟨26536046410323124553958437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70762790427528332143889165 26536046410323124553958437)
          ·
            refine ⟨4975508701935585853867207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26536046410323124553958437 4975508701935585853867207)
            ·
              refine ⟨7463263052903378780800811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975508701935585853867207 7463263052903378780800811)
              ·
                refine ⟨11194894579355068171201217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463263052903378780800811 11194894579355068171201217)
                ·
                  refine ⟨8396170934516301128400913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11194894579355068171201217 8396170934516301128400913)
                  ·
                    refine ⟨6297128200887225846300685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8396170934516301128400913 6297128200887225846300685)
                    ·
                      refine ⟨2361423075332709692362757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6297128200887225846300685 2361423075332709692362757)
                      ·
                        rfl

theorem cell23_4598855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_4598855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598855 prefixEnd_4598855 := by exact prefixLift 4598855
  have htrace : WordTrace (prefixWord ++ tailWord_4598855) baseStart_4598855 baseEnd_4598855 := by
    simpa [prefixWord, tailWord_4598855, baseEnd_4598855] using wordTrace_append hprefix tailTrace_4598855
  have hstable : (prefixWord ++ tailWord_4598855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598855).length < 2 ^ (prefixWord ++ tailWord_4598855).sum := by decide
  have hdescent : baseEnd_4598855 < baseStart_4598855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598885 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_4598885 : Nat := 118140960795 + 4598885 * 2 ^ 59
def prefixEnd_4598885 : Nat := 4983230072969 + 3 ^ 40 * 4598885 * 2
def baseEnd_4598885 : Nat := 2361438479752344574987619

theorem tailTrace_4598885 : CollatzResearch.WordTrace tailWord_4598885 prefixEnd_4598885 2361438479752344574987619 := by
  unfold tailWord_4598885
  simp only [CollatzResearch.WordTrace]
  refine ⟨167735115944032546872070109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111823410629355031248046739 167735115944032546872070109)
  ·
    refine ⟨62900668479012205077026291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167735115944032546872070109 62900668479012205077026291)
    ·
      refine ⟨94351002718518307615539437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62900668479012205077026291 94351002718518307615539437)
      ·
        refine ⟨35381626019444365355827289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94351002718518307615539437 35381626019444365355827289)
        ·
          refine ⟨26536219514583274016870467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35381626019444365355827289 26536219514583274016870467)
          ·
            refine ⟨39804329271874911025305701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26536219514583274016870467 39804329271874911025305701)
            ·
              refine ⟨7463311738476545817244819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39804329271874911025305701 7463311738476545817244819)
              ·
                refine ⟨11194967607714818725867229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463311738476545817244819 11194967607714818725867229)
                ·
                  refine ⟨4198112852893057022200211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11194967607714818725867229 4198112852893057022200211)
                  ·
                    refine ⟨6297169279339585533300317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4198112852893057022200211 6297169279339585533300317)
                    ·
                      refine ⟨2361438479752344574987619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6297169279339585533300317 2361438479752344574987619)
                      ·
                        rfl

theorem cell23_4598885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_4598885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598885 prefixEnd_4598885 := by exact prefixLift 4598885
  have htrace : WordTrace (prefixWord ++ tailWord_4598885) baseStart_4598885 baseEnd_4598885 := by
    simpa [prefixWord, tailWord_4598885, baseEnd_4598885] using wordTrace_append hprefix tailTrace_4598885
  have hstable : (prefixWord ++ tailWord_4598885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598885).length < 2 ^ (prefixWord ++ tailWord_4598885).sum := by decide
  have hdescent : baseEnd_4598885 < baseStart_4598885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598905 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_4598905 : Nat := 118140960795 + 4598905 * 2 ^ 59
def prefixEnd_4598905 : Nat := 4983230072969 + 3 ^ 40 * 4598905 * 2
def baseEnd_4598905 : Nat := 787149583121811498912509

theorem tailTrace_4598905 : CollatzResearch.WordTrace tailWord_4598905 prefixEnd_4598905 787149583121811498912509 := by
  unfold tailWord_4598905
  simp only [CollatzResearch.WordTrace]
  refine ⟨167735845403960090287798169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111823896935973393525198779 167735845403960090287798169)
  ·
    refine ⟨125801884052970067715848627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167735845403960090287798169 125801884052970067715848627)
    ·
      refine ⟨188702826079455101573772941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125801884052970067715848627 188702826079455101573772941)
      ·
        refine ⟨70763559779795663090164853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188702826079455101573772941 70763559779795663090164853)
        ·
          refine ⟨6634083729355843414702955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70763559779795663090164853 6634083729355843414702955)
          ·
            refine ⟨9951125594033765122054433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6634083729355843414702955 9951125594033765122054433)
            ·
              refine ⟨7463344195525323841540825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9951125594033765122054433 7463344195525323841540825)
              ·
                refine ⟨5597508146643992881155619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463344195525323841540825 5597508146643992881155619)
                ·
                  refine ⟨8396262219965989321733429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597508146643992881155619 8396262219965989321733429)
                  ·
                    refine ⟨787149583121811498912509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8396262219965989321733429 787149583121811498912509)
                    ·
                      rfl

theorem cell23_4598905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_4598905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598905 prefixEnd_4598905 := by exact prefixLift 4598905
  have htrace : WordTrace (prefixWord ++ tailWord_4598905) baseStart_4598905 baseEnd_4598905 := by
    simpa [prefixWord, tailWord_4598905, baseEnd_4598905] using wordTrace_append hprefix tailTrace_4598905
  have hstable : (prefixWord ++ tailWord_4598905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598905).length < 2 ^ (prefixWord ++ tailWord_4598905).sum := by decide
  have hdescent : baseEnd_4598905 < baseStart_4598905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598908 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_4598908 : Nat := 118140960795 + 4598908 * 2 ^ 59
def prefixEnd_4598908 : Nat := 4983230072969 + 3 ^ 40 * 4598908 * 2
def baseEnd_4598908 : Nat := 2361450289807397985000013

theorem tailTrace_4598908 : CollatzResearch.WordTrace tailWord_4598908 prefixEnd_4598908 2361450289807397985000013 := by
  unfold tailWord_4598908
  simp only [CollatzResearch.WordTrace]
  refine ⟨83867977411474610900078689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111823969881966147866771585 83867977411474610900078689)
  ·
    refine ⟨62900983058605958175059017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83867977411474610900078689 62900983058605958175059017)
    ·
      refine ⟨47175737293954468631294263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62900983058605958175059017 47175737293954468631294263)
      ·
        refine ⟨70763605940931702946941395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47175737293954468631294263 70763605940931702946941395)
        ·
          refine ⟨106145408911397554420412093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70763605940931702946941395 106145408911397554420412093)
          ·
            refine ⟨39804528341774082907654535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106145408911397554420412093 39804528341774082907654535)
            ·
              refine ⟨59706792512661124361481803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39804528341774082907654535 59706792512661124361481803)
              ·
                refine ⟨89560188768991686542222705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59706792512661124361481803 89560188768991686542222705)
                ·
                  refine ⟨67170141576743764906667029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89560188768991686542222705 67170141576743764906667029)
                  ·
                    refine ⟨3148600386409863980000017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67170141576743764906667029 3148600386409863980000017)
                    ·
                      refine ⟨2361450289807397985000013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148600386409863980000017 2361450289807397985000013)
                      ·
                        rfl

theorem cell23_4598908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_4598908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598908 prefixEnd_4598908 := by exact prefixLift 4598908
  have htrace : WordTrace (prefixWord ++ tailWord_4598908) baseStart_4598908 baseEnd_4598908 := by
    simpa [prefixWord, tailWord_4598908, baseEnd_4598908] using wordTrace_append hprefix tailTrace_4598908
  have hstable : (prefixWord ++ tailWord_4598908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598908).length < 2 ^ (prefixWord ++ tailWord_4598908).sum := by decide
  have hdescent : baseEnd_4598908 < baseStart_4598908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3]
def baseStart_4598911 : Nat := 118140960795 + 4598911 * 2 ^ 59
def prefixEnd_4598911 : Nat := 4983230072969 + 3 ^ 40 * 4598911 * 2
def baseEnd_4598911 : Nat := 2361451830249361473262499

theorem tailTrace_4598911 : CollatzResearch.WordTrace tailWord_4598911 prefixEnd_4598911 2361451830249361473262499 := by
  unfold tailWord_4598911
  simp only [CollatzResearch.WordTrace]
  refine ⟨167736064241938353312516587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111824042827958902208344391 167736064241938353312516587)
  ·
    refine ⟨251604096362907529968774881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167736064241938353312516587 251604096362907529968774881)
    ·
      refine ⟨188703072272180647476581161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251604096362907529968774881 188703072272180647476581161)
      ·
        refine ⟨141527304204135485607435871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188703072272180647476581161 141527304204135485607435871)
        ·
          refine ⟨212290956306203228411153807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141527304204135485607435871 212290956306203228411153807)
          ·
            refine ⟨318436434459304842616730711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212290956306203228411153807 318436434459304842616730711)
            ·
              refine ⟨477654651688957263925096067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318436434459304842616730711 477654651688957263925096067)
              ·
                refine ⟨716481977533435895887644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477654651688957263925096067 716481977533435895887644101)
                ·
                  refine ⟨134340370787519230478933269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716481977533435895887644101 134340370787519230478933269)
                  ·
                    refine ⟨6297204880664963928699997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 134340370787519230478933269 6297204880664963928699997)
                    ·
                      refine ⟨2361451830249361473262499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6297204880664963928699997 2361451830249361473262499)
                      ·
                        rfl

theorem cell23_4598911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_4598911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598911 prefixEnd_4598911 := by exact prefixLift 4598911
  have htrace : WordTrace (prefixWord ++ tailWord_4598911) baseStart_4598911 baseEnd_4598911 := by
    simpa [prefixWord, tailWord_4598911, baseEnd_4598911] using wordTrace_append hprefix tailTrace_4598911
  have hstable : (prefixWord ++ tailWord_4598911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598911).length < 2 ^ (prefixWord ++ tailWord_4598911).sum := by decide
  have hdescent : baseEnd_4598911 < baseStart_4598911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598938 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4598938 : Nat := 118140960795 + 4598938 * 2 ^ 59
def prefixEnd_4598938 : Nat := 4983230072969 + 3 ^ 40 * 4598938 * 2
def baseEnd_4598938 : Nat := 2361465694227032867624875

theorem tailTrace_4598938 : CollatzResearch.WordTrace tailWord_4598938 prefixEnd_4598938 2361465694227032867624875 := by
  unfold tailWord_4598938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41934262253210134230937367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111824699341893691282499645 41934262253210134230937367)
  ·
    refine ⟨62901393379815201346406051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41934262253210134230937367 62901393379815201346406051)
    ·
      refine ⟨94352090069722802019609077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62901393379815201346406051 94352090069722802019609077)
      ·
        refine ⟨8845508444036512689338351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94352090069722802019609077 8845508444036512689338351)
        ·
          refine ⟨13268262666054769034007527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8845508444036512689338351 13268262666054769034007527)
          ·
            refine ⟨19902393999082153551011291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13268262666054769034007527 19902393999082153551011291)
            ·
              refine ⟨29853590998623230326516937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19902393999082153551011291 29853590998623230326516937)
              ·
                refine ⟨22390193248967422744887703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29853590998623230326516937 22390193248967422744887703)
                ·
                  refine ⟨33585289873451134117331555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22390193248967422744887703 33585289873451134117331555)
                  ·
                    refine ⟨50377934810176701175997333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33585289873451134117331555 50377934810176701175997333)
                    ·
                      refine ⟨2361465694227032867624875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50377934810176701175997333 2361465694227032867624875)
                      ·
                        rfl

theorem cell23_4598938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4598938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598938 prefixEnd_4598938 := by exact prefixLift 4598938
  have htrace : WordTrace (prefixWord ++ tailWord_4598938) baseStart_4598938 baseEnd_4598938 := by
    simpa [prefixWord, tailWord_4598938, baseEnd_4598938] using wordTrace_append hprefix tailTrace_4598938
  have hstable : (prefixWord ++ tailWord_4598938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598938).length < 2 ^ (prefixWord ++ tailWord_4598938).sum := by decide
  have hdescent : baseEnd_4598938 < baseStart_4598938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598948 : List Nat := [2, 3, 1, 2, 3, 2, 2, 8]
def baseStart_4598948 : Nat := 118140960795 + 4598948 * 2 ^ 59
def prefixEnd_4598948 : Nat := 4983230072969 + 3 ^ 40 * 4598948 * 2
def baseEnd_4598948 : Nat := 87461882556799178833327

theorem tailTrace_4598948 : CollatzResearch.WordTrace tailWord_4598948 prefixEnd_4598948 87461882556799178833327 := by
  unfold tailWord_4598948
  simp only [CollatzResearch.WordTrace]
  refine ⟨83868706871402154315806749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111824942495202872421075665 83868706871402154315806749)
  ·
    refine ⟨31450765076775807868427531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83868706871402154315806749 31450765076775807868427531)
    ·
      refine ⟨47176147615163711802641297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31450765076775807868427531 47176147615163711802641297)
      ·
        refine ⟨35382110711372783851980973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47176147615163711802641297 35382110711372783851980973)
        ·
          refine ⟨13268291516764793944492865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35382110711372783851980973 13268291516764793944492865)
          ·
            refine ⟨9951218637573595458369649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13268291516764793944492865 9951218637573595458369649)
            ·
              refine ⟨7463413978180196593777237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9951218637573595458369649 7463413978180196593777237)
              ·
                refine ⟨87461882556799178833327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7463413978180196593777237 87461882556799178833327)
                ·
                  rfl

theorem cell23_4598948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 8].length) (baseStart_4598948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598948 prefixEnd_4598948 := by exact prefixLift 4598948
  have htrace : WordTrace (prefixWord ++ tailWord_4598948) baseStart_4598948 baseEnd_4598948 := by
    simpa [prefixWord, tailWord_4598948, baseEnd_4598948] using wordTrace_append hprefix tailTrace_4598948
  have hstable : (prefixWord ++ tailWord_4598948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598948).length < 2 ^ (prefixWord ++ tailWord_4598948).sum := by decide
  have hdescent : baseEnd_4598948 < baseStart_4598948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598962 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_4598962 : Nat := 118140960795 + 4598962 * 2 ^ 59
def prefixEnd_4598962 : Nat := 4983230072969 + 3 ^ 40 * 4598962 * 2
def baseEnd_4598962 : Nat := 2361478017762740773724765

theorem tailTrace_4598962 : CollatzResearch.WordTrace tailWord_4598962 prefixEnd_4598962 2361478017762740773724765 := by
  unfold tailWord_4598962
  simp only [CollatzResearch.WordTrace]
  refine ⟨41934481091188397255655785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111825282909835726015082093 41934481091188397255655785)
  ·
    refine ⟨31450860818391297941741839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41934481091188397255655785 31450860818391297941741839)
    ·
      refine ⟨47176291227586946912612759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31450860818391297941741839 47176291227586946912612759)
      ·
        refine ⟨70764436841380420368919139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47176291227586946912612759 70764436841380420368919139)
        ·
          refine ⟨106146655262070630553378709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70764436841380420368919139 106146655262070630553378709)
          ·
            refine ⟨4975624465409560807189627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106146655262070630553378709 4975624465409560807189627)
            ·
              refine ⟨7463436698114341210784441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4975624465409560807189627 7463436698114341210784441)
              ·
                refine ⟨5597577523585755908088331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463436698114341210784441 5597577523585755908088331)
                ·
                  refine ⟨8396366285378633862132497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597577523585755908088331 8396366285378633862132497)
                  ·
                    refine ⟨6297274714033975396599373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8396366285378633862132497 6297274714033975396599373)
                    ·
                      refine ⟨2361478017762740773724765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6297274714033975396599373 2361478017762740773724765)
                      ·
                        rfl

theorem cell23_4598962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_4598962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598962 prefixEnd_4598962 := by exact prefixLift 4598962
  have htrace : WordTrace (prefixWord ++ tailWord_4598962) baseStart_4598962 baseEnd_4598962 := by
    simpa [prefixWord, tailWord_4598962, baseEnd_4598962] using wordTrace_append hprefix tailTrace_4598962
  have hstable : (prefixWord ++ tailWord_4598962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598962).length < 2 ^ (prefixWord ++ tailWord_4598962).sum := by decide
  have hdescent : baseEnd_4598962 < baseStart_4598962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598971 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_4598971 : Nat := 118140960795 + 4598971 * 2 ^ 59
def prefixEnd_4598971 : Nat := 4983230072969 + 3 ^ 40 * 4598971 * 2
def baseEnd_4598971 : Nat := 2361482639088631238512223

theorem tailTrace_4598971 : CollatzResearch.WordTrace tailWord_4598971 prefixEnd_4598971 2361482639088631238512223 := by
  unfold tailWord_4598971
  simp only [CollatzResearch.WordTrace]
  refine ⟨167738252621720983559700767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111825501747813989039800511 167738252621720983559700767)
  ·
    refine ⟨251607378932581475339551151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167738252621720983559700767 251607378932581475339551151)
    ·
      refine ⟨377411068398872213009326727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251607378932581475339551151 377411068398872213009326727)
      ·
        refine ⟨566116602598308319513990091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377411068398872213009326727 566116602598308319513990091)
        ·
          refine ⟨849174903897462479270985137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566116602598308319513990091 849174903897462479270985137)
          ·
            refine ⟨636881177923096859453238853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849174903897462479270985137 636881177923096859453238853)
            ·
              refine ⟨119415220860580661147482285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 636881177923096859453238853 119415220860580661147482285)
              ·
                refine ⟨44780707822717747930305857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119415220860580661147482285 44780707822717747930305857)
                ·
                  refine ⟨33585530867038310947729393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44780707822717747930305857 33585530867038310947729393)
                  ·
                    refine ⟨25189148150278733210797045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33585530867038310947729393 25189148150278733210797045)
                    ·
                      refine ⟨2361482639088631238512223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25189148150278733210797045 2361482639088631238512223)
                      ·
                        rfl

theorem cell23_4598971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_4598971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598971 prefixEnd_4598971 := by exact prefixLift 4598971
  have htrace : WordTrace (prefixWord ++ tailWord_4598971) baseStart_4598971 baseEnd_4598971 := by
    simpa [prefixWord, tailWord_4598971, baseEnd_4598971] using wordTrace_append hprefix tailTrace_4598971
  have hstable : (prefixWord ++ tailWord_4598971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598971).length < 2 ^ (prefixWord ++ tailWord_4598971).sum := by decide
  have hdescent : baseEnd_4598971 < baseStart_4598971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4598982 : List Nat := [6, 1, 2, 2, 1, 11]
def baseStart_4598982 : Nat := 118140960795 + 4598982 * 2 ^ 59
def prefixEnd_4598982 : Nat := 4983230072969 + 3 ^ 40 * 4598982 * 2
def baseEnd_4598982 : Nat := 9718058795785311504011

theorem tailTrace_4598982 : CollatzResearch.WordTrace tailWord_4598982 prefixEnd_4598982 9718058795785311504011 := by
  unfold tailWord_4598982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5241832932021285388698475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111825769216454088292234133 5241832932021285388698475)
  ·
    refine ⟨7862749398031928083047713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5241832932021285388698475 7862749398031928083047713)
    ·
      refine ⟨5897062048523946062285785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7862749398031928083047713 5897062048523946062285785)
      ·
        refine ⟨4422796536392959546714339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5897062048523946062285785 4422796536392959546714339)
        ·
          refine ⟨6634194804589439320071509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422796536392959546714339 6634194804589439320071509)
          ·
            refine ⟨9718058795785311504011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6634194804589439320071509 9718058795785311504011)
            ·
              rfl

theorem cell23_4598982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 11].length) (baseStart_4598982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4598982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4598982 prefixEnd_4598982 := by exact prefixLift 4598982
  have htrace : WordTrace (prefixWord ++ tailWord_4598982) baseStart_4598982 baseEnd_4598982 := by
    simpa [prefixWord, tailWord_4598982, baseEnd_4598982] using wordTrace_append hprefix tailTrace_4598982
  have hstable : (prefixWord ++ tailWord_4598982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4598982).length < 2 ^ (prefixWord ++ tailWord_4598982).sum := by decide
  have hdescent : baseEnd_4598982 < baseStart_4598982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4598982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599008 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_4599008 : Nat := 118140960795 + 4599008 * 2 ^ 59
def prefixEnd_4599008 : Nat := 4983230072969 + 3 ^ 40 * 4599008 * 2
def baseEnd_4599008 : Nat := 787167212624282531249851

theorem tailTrace_4599008 : CollatzResearch.WordTrace tailWord_4599008 prefixEnd_4599008 787167212624282531249851 := by
  unfold tailWord_4599008
  simp only [CollatzResearch.WordTrace]
  refine ⟨83869801061293469439398839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111826401415057959252531785 83869801061293469439398839)
  ·
    refine ⟨125804701591940204159098259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83869801061293469439398839 125804701591940204159098259)
    ·
      refine ⟨188707052387910306238647389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125804701591940204159098259 188707052387910306238647389)
      ·
        refine ⟨70765144645466364839492771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188707052387910306238647389 70765144645466364839492771)
        ·
          refine ⟨106147716968199547259239157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70765144645466364839492771 106147716968199547259239157)
          ·
            refine ⟨9951348465768707555553671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106147716968199547259239157 9951348465768707555553671)
            ·
              refine ⟨14927022698653061333330507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9951348465768707555553671 14927022698653061333330507)
              ·
                refine ⟨22390534047979591999995761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14927022698653061333330507 22390534047979591999995761)
                ·
                  refine ⟨16792900535984693999996821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22390534047979591999995761 16792900535984693999996821)
                  ·
                    refine ⟨787167212624282531249851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16792900535984693999996821 787167212624282531249851)
                    ·
                      rfl

theorem cell23_4599008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_4599008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599008 prefixEnd_4599008 := by exact prefixLift 4599008
  have htrace : WordTrace (prefixWord ++ tailWord_4599008) baseStart_4599008 baseEnd_4599008 := by
    simpa [prefixWord, tailWord_4599008, baseEnd_4599008] using wordTrace_append hprefix tailTrace_4599008
  have hstable : (prefixWord ++ tailWord_4599008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599008).length < 2 ^ (prefixWord ++ tailWord_4599008).sum := by decide
  have hdescent : baseEnd_4599008 < baseStart_4599008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599036 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_4599036 : Nat := 118140960795 + 4599036 * 2 ^ 59
def prefixEnd_4599036 : Nat := 4983230072969 + 3 ^ 40 * 4599036 * 2
def baseEnd_4599036 : Nat := 2361516015331173484199425

theorem tailTrace_4599036 : CollatzResearch.WordTrace tailWord_4599036 prefixEnd_4599036 2361516015331173484199425 := by
  unfold tailWord_4599036
  simp only [CollatzResearch.WordTrace]
  refine ⟨83870311683242749830408481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111827082244323666440544641 83870311683242749830408481)
  ·
    refine ⟨62902733762432062372806361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83870311683242749830408481 62902733762432062372806361)
    ·
      refine ⟨47177050321824046779604771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62902733762432062372806361 47177050321824046779604771)
      ·
        refine ⟨70765575482736070169407157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47177050321824046779604771 70765575482736070169407157)
        ·
          refine ⟨6634272701506506578381921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70765575482736070169407157 6634272701506506578381921)
          ·
            refine ⟨4975704526129879933786441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6634272701506506578381921 4975704526129879933786441)
            ·
              refine ⟨3731778394597409950339831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975704526129879933786441 3731778394597409950339831)
              ·
                refine ⟨5597667591896114925509747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731778394597409950339831 5597667591896114925509747)
                ·
                  refine ⟨8396501387844172388264621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597667591896114925509747 8396501387844172388264621)
                  ·
                    refine ⟨3148688020441564645599233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8396501387844172388264621 3148688020441564645599233)
                    ·
                      refine ⟨2361516015331173484199425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148688020441564645599233 2361516015331173484199425)
                      ·
                        rfl

theorem cell23_4599036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_4599036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599036 prefixEnd_4599036 := by exact prefixLift 4599036
  have htrace : WordTrace (prefixWord ++ tailWord_4599036) baseStart_4599036 baseEnd_4599036 := by
    simpa [prefixWord, tailWord_4599036, baseEnd_4599036] using wordTrace_append hprefix tailTrace_4599036
  have hstable : (prefixWord ++ tailWord_4599036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599036).length < 2 ^ (prefixWord ++ tailWord_4599036).sum := by decide
  have hdescent : baseEnd_4599036 < baseStart_4599036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599066 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_4599066 : Nat := 118140960795 + 4599066 * 2 ^ 59
def prefixEnd_4599066 : Nat := 4983230072969 + 3 ^ 40 * 4599066 * 2
def baseEnd_4599066 : Nat := 2361531419750808366824287

theorem tailTrace_4599066 : CollatzResearch.WordTrace tailWord_4599066 prefixEnd_4599066 2361531419750808366824287 := by
  unfold tailWord_4599066
  simp only [CollatzResearch.WordTrace]
  refine ⟨41935429389094203696102263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111827811704251209856272701 41935429389094203696102263)
  ·
    refine ⟨62903144083641305544153395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41935429389094203696102263 62903144083641305544153395)
    ·
      refine ⟨94354716125461958316230093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62903144083641305544153395 94354716125461958316230093)
      ·
        refine ⟨35383018547048234368586285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94354716125461958316230093 35383018547048234368586285)
        ·
          refine ⟨13268631955143087888219857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35383018547048234368586285 13268631955143087888219857)
          ·
            refine ⟨9951473966357315916164893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13268631955143087888219857 9951473966357315916164893)
            ·
              refine ⟨3731802737383993468561835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9951473966357315916164893 3731802737383993468561835)
              ·
                refine ⟨5597704106075990202842753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731802737383993468561835 5597704106075990202842753)
                ·
                  refine ⟨4198278079556992652132065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5597704106075990202842753 4198278079556992652132065)
                  ·
                    refine ⟨3148708559667744489099049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198278079556992652132065 3148708559667744489099049)
                    ·
                      refine ⟨2361531419750808366824287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148708559667744489099049 2361531419750808366824287)
                      ·
                        rfl

theorem cell23_4599066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_4599066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599066 prefixEnd_4599066 := by exact prefixLift 4599066
  have htrace : WordTrace (prefixWord ++ tailWord_4599066) baseStart_4599066 baseEnd_4599066 := by
    simpa [prefixWord, tailWord_4599066, baseEnd_4599066] using wordTrace_append hprefix tailTrace_4599066
  have hstable : (prefixWord ++ tailWord_4599066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599066).length < 2 ^ (prefixWord ++ tailWord_4599066).sum := by decide
  have hdescent : baseEnd_4599066 < baseStart_4599066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599068 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_4599068 : Nat := 118140960795 + 4599068 * 2 ^ 59
def prefixEnd_4599068 : Nat := 4983230072969 + 3 ^ 40 * 4599068 * 2
def baseEnd_4599068 : Nat := 787177482237372452999759

theorem tailTrace_4599068 : CollatzResearch.WordTrace tailWord_4599068 prefixEnd_4599068 787177482237372452999759 := by
  unfold tailWord_4599068
  simp only [CollatzResearch.WordTrace]
  refine ⟨83870895251184784562990929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111827860334913046083987905 83870895251184784562990929)
  ·
    refine ⟨62903171438388588422243197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83870895251184784562990929 62903171438388588422243197)
    ·
      refine ⟨23588689289395720658341199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62903171438388588422243197 23588689289395720658341199)
      ·
        refine ⟨35383033934093580987511799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23588689289395720658341199 35383033934093580987511799)
        ·
          refine ⟨53074550901140371481267699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35383033934093580987511799 53074550901140371481267699)
          ·
            refine ⟨79611826351710557221901549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53074550901140371481267699 79611826351710557221901549)
            ·
              refine ⟨29854434881891458958213081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79611826351710557221901549 29854434881891458958213081)
              ·
                refine ⟨22390826161418594218659811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29854434881891458958213081 22390826161418594218659811)
                ·
                  refine ⟨33586239242127891327989717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22390826161418594218659811 33586239242127891327989717)
                  ·
                    refine ⟨787177482237372452999759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33586239242127891327989717 787177482237372452999759)
                    ·
                      rfl

theorem cell23_4599068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_4599068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599068 prefixEnd_4599068 := by exact prefixLift 4599068
  have htrace : WordTrace (prefixWord ++ tailWord_4599068) baseStart_4599068 baseEnd_4599068 := by
    simpa [prefixWord, tailWord_4599068, baseEnd_4599068] using wordTrace_append hprefix tailTrace_4599068
  have hstable : (prefixWord ++ tailWord_4599068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599068).length < 2 ^ (prefixWord ++ tailWord_4599068).sum := by decide
  have hdescent : baseEnd_4599068 < baseStart_4599068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599088 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_4599088 : Nat := 118140960795 + 4599088 * 2 ^ 59
def prefixEnd_4599088 : Nat := 4983230072969 + 3 ^ 40 * 4599088 * 2
def baseEnd_4599088 : Nat := 2361542716325207280749185

theorem tailTrace_4599088 : CollatzResearch.WordTrace tailWord_4599088 prefixEnd_4599088 2361542716325207280749185 := by
  unfold tailWord_4599088
  simp only [CollatzResearch.WordTrace]
  refine ⟨83871259981148556270854959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111828346641531408361139945 83871259981148556270854959)
  ·
    refine ⟨125806889971722834406282439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83871259981148556270854959 125806889971722834406282439)
    ·
      refine ⟨188710334957584251609423659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125806889971722834406282439 188710334957584251609423659)
      ·
        refine ⟨283065502436376377414135489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188710334957584251609423659 283065502436376377414135489)
        ·
          refine ⟨212299126827282283060601617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283065502436376377414135489 212299126827282283060601617)
          ·
            refine ⟨159224345120461712295451213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212299126827282283060601617 159224345120461712295451213)
            ·
              refine ⟨59709129420173142110794205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159224345120461712295451213 59709129420173142110794205)
              ·
                refine ⟨22390923532564928291547827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59709129420173142110794205 22390923532564928291547827)
                ·
                  refine ⟨33586385298847392437321741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22390923532564928291547827 33586385298847392437321741)
                  ·
                    refine ⟨12594894487067772163995653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33586385298847392437321741 12594894487067772163995653)
                    ·
                      refine ⟨2361542716325207280749185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12594894487067772163995653 2361542716325207280749185)
                      ·
                        rfl

theorem cell23_4599088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_4599088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599088 prefixEnd_4599088 := by exact prefixLift 4599088
  have htrace : WordTrace (prefixWord ++ tailWord_4599088) baseStart_4599088 baseEnd_4599088 := by
    simpa [prefixWord, tailWord_4599088, baseEnd_4599088] using wordTrace_append hprefix tailTrace_4599088
  have hstable : (prefixWord ++ tailWord_4599088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599088).length < 2 ^ (prefixWord ++ tailWord_4599088).sum := by decide
  have hdescent : baseEnd_4599088 < baseStart_4599088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599117 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4599117 : Nat := 118140960795 + 4599117 * 2 ^ 59
def prefixEnd_4599117 : Nat := 4983230072969 + 3 ^ 40 * 4599117 * 2
def baseEnd_4599117 : Nat := 2361557607264187667286553

theorem tailTrace_4599117 : CollatzResearch.WordTrace tailWord_4599117 prefixEnd_4599117 2361557607264187667286553 := by
  unfold tailWord_4599117
  simp only [CollatzResearch.WordTrace]
  refine ⟨167743577679192050494515605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111829051786128033663010403 167743577679192050494515605)
  ·
    refine ⟨7862980203712127366930419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167743577679192050494515605 7862980203712127366930419)
    ·
      refine ⟨11794470305568191050395629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7862980203712127366930419 11794470305568191050395629)
      ·
        refine ⟨4422926364588071643898361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11794470305568191050395629 4422926364588071643898361)
        ·
          refine ⟨3317194773441053732923771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4422926364588071643898361 3317194773441053732923771)
          ·
            refine ⟨4975792160161580599385657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317194773441053732923771 4975792160161580599385657)
            ·
              refine ⟨3731844120121185449539243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975792160161580599385657 3731844120121185449539243)
              ·
                refine ⟨5597766180181778174308865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731844120121185449539243 5597766180181778174308865)
                ·
                  refine ⟨4198324635136333630731649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5597766180181778174308865 4198324635136333630731649)
                  ·
                    refine ⟨3148743476352250223048737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198324635136333630731649 3148743476352250223048737)
                    ·
                      refine ⟨2361557607264187667286553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148743476352250223048737 2361557607264187667286553)
                      ·
                        rfl

theorem cell23_4599117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4599117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599117 prefixEnd_4599117 := by exact prefixLift 4599117
  have htrace : WordTrace (prefixWord ++ tailWord_4599117) baseStart_4599117 baseEnd_4599117 := by
    simpa [prefixWord, tailWord_4599117, baseEnd_4599117] using wordTrace_append hprefix tailTrace_4599117
  have hstable : (prefixWord ++ tailWord_4599117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599117).length < 2 ^ (prefixWord ++ tailWord_4599117).sum := by decide
  have hdescent : baseEnd_4599117 < baseStart_4599117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599168 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_4599168 : Nat := 118140960795 + 4599168 * 2 ^ 59
def prefixEnd_4599168 : Nat := 4983230072969 + 3 ^ 40 * 4599168 * 2
def baseEnd_4599168 : Nat := 2361583794777566967748817

theorem tailTrace_4599168 : CollatzResearch.WordTrace tailWord_4599168 prefixEnd_4599168 2361583794777566967748817 := by
  unfold tailWord_4599168
  simp only [CollatzResearch.WordTrace]
  refine ⟨83872718901003643102311079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111830291868004857469748105 83872718901003643102311079)
  ·
    refine ⟨125809078351505464653466619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83872718901003643102311079 125809078351505464653466619)
    ·
      refine ⟨188713617527258196980199929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125809078351505464653466619 188713617527258196980199929)
      ·
        refine ⟨141535213145443647735149947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188713617527258196980199929 141535213145443647735149947)
        ·
          refine ⟨212302819718165471602724921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141535213145443647735149947 212302819718165471602724921)
          ·
            refine ⟨159227114788624103702043691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212302819718165471602724921 159227114788624103702043691)
            ·
              refine ⟨238840672182936155553065537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159227114788624103702043691 238840672182936155553065537)
              ·
                refine ⟨179130504137202116664799153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238840672182936155553065537 179130504137202116664799153)
                ·
                  refine ⟨134347878102901587498599365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179130504137202116664799153 134347878102901587498599365)
                  ·
                    refine ⟨25190227144294047655987381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134347878102901587498599365 25190227144294047655987381)
                    ·
                      refine ⟨2361583794777566967748817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25190227144294047655987381 2361583794777566967748817)
                      ·
                        rfl

theorem cell23_4599168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_4599168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599168 prefixEnd_4599168 := by exact prefixLift 4599168
  have htrace : WordTrace (prefixWord ++ tailWord_4599168) baseStart_4599168 baseEnd_4599168 := by
    simpa [prefixWord, tailWord_4599168, baseEnd_4599168] using wordTrace_append hprefix tailTrace_4599168
  have hstable : (prefixWord ++ tailWord_4599168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599168).length < 2 ^ (prefixWord ++ tailWord_4599168).sum := by decide
  have hdescent : baseEnd_4599168 < baseStart_4599168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599175 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 3, 5]
def baseStart_4599175 : Nat := 118140960795 + 4599175 * 2 ^ 59
def prefixEnd_4599175 : Nat := 4983230072969 + 3 ^ 40 * 4599175 * 2
def baseEnd_4599175 : Nat := 787195796380716146787095

theorem tailTrace_4599175 : CollatzResearch.WordTrace tailWord_4599175 prefixEnd_4599175 787195796380716146787095 := by
  unfold tailWord_4599175
  simp only [CollatzResearch.WordTrace]
  refine ⟨167745693112981926400126979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111830462075321284266751319 167745693112981926400126979)
  ·
    refine ⟨251618539669472889600190469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167745693112981926400126979 251618539669472889600190469)
    ·
      refine ⟨47178476188026166800035713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251618539669472889600190469 47178476188026166800035713)
      ·
        refine ⟨35383857141019625100026785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47178476188026166800035713 35383857141019625100026785)
        ·
          refine ⟨26537892855764718825020089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35383857141019625100026785 26537892855764718825020089)
          ·
            refine ⟨19903419641823539118765067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26537892855764718825020089 19903419641823539118765067)
            ·
              refine ⟨29855129462735308678147601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19903419641823539118765067 29855129462735308678147601)
              ·
                refine ⟨22391347097051481508610701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29855129462735308678147601 22391347097051481508610701)
                ·
                  refine ⟨8396755161394305565729013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22391347097051481508610701 8396755161394305565729013)
                  ·
                    refine ⟨787195796380716146787095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8396755161394305565729013 787195796380716146787095)
                    ·
                      rfl

theorem cell23_4599175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_4599175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599175 prefixEnd_4599175 := by exact prefixLift 4599175
  have htrace : WordTrace (prefixWord ++ tailWord_4599175) baseStart_4599175 baseEnd_4599175 := by
    simpa [prefixWord, tailWord_4599175, baseEnd_4599175] using wordTrace_append hprefix tailTrace_4599175
  have hstable : (prefixWord ++ tailWord_4599175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599175).length < 2 ^ (prefixWord ++ tailWord_4599175).sum := by decide
  have hdescent : baseEnd_4599175 < baseStart_4599175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599199 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 2, 3, 2]
def baseStart_4599199 : Nat := 118140960795 + 4599199 * 2 ^ 59
def prefixEnd_4599199 : Nat := 4983230072969 + 3 ^ 40 * 4599199 * 2
def baseEnd_4599199 : Nat := 2361599712677856346461175

theorem tailTrace_4599199 : CollatzResearch.WordTrace tailWord_4599199 prefixEnd_4599199 2361599712677856346461175 := by
  unfold tailWord_4599199
  simp only [CollatzResearch.WordTrace]
  refine ⟨167746568464894978499000651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111831045643263318999333767 167746568464894978499000651)
  ·
    refine ⟨251619852697342467748500977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167746568464894978499000651 251619852697342467748500977)
    ·
      refine ⟨188714889523006850811375733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251619852697342467748500977 188714889523006850811375733)
      ·
        refine ⟨17692020892781892263566475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188714889523006850811375733 17692020892781892263566475)
        ·
          refine ⟨26538031339172838395349713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17692020892781892263566475 26538031339172838395349713)
          ·
            refine ⟨19903523504379628796512285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26538031339172838395349713 19903523504379628796512285)
            ·
              refine ⟨7463821314142360798692107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19903523504379628796512285 7463821314142360798692107)
              ·
                refine ⟨11195731971213541198038161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463821314142360798692107 11195731971213541198038161)
                ·
                  refine ⟨8396798978410155898528621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11195731971213541198038161 8396798978410155898528621)
                  ·
                    refine ⟨3148799616903808461948233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8396798978410155898528621 3148799616903808461948233)
                    ·
                      refine ⟨2361599712677856346461175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148799616903808461948233 2361599712677856346461175)
                      ·
                        rfl

theorem cell23_4599199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_4599199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599199 prefixEnd_4599199 := by exact prefixLift 4599199
  have htrace : WordTrace (prefixWord ++ tailWord_4599199) baseStart_4599199 baseEnd_4599199 := by
    simpa [prefixWord, tailWord_4599199, baseEnd_4599199] using wordTrace_append hprefix tailTrace_4599199
  have hstable : (prefixWord ++ tailWord_4599199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599199).length < 2 ^ (prefixWord ++ tailWord_4599199).sum := by decide
  have hdescent : baseEnd_4599199 < baseStart_4599199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599239 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 2, 4]
def baseStart_4599239 : Nat := 118140960795 + 4599239 * 2 ^ 59
def prefixEnd_4599239 : Nat := 4983230072969 + 3 ^ 40 * 4599239 * 2
def baseEnd_4599239 : Nat := 787206750634678729986997

theorem tailTrace_4599239 : CollatzResearch.WordTrace tailWord_4599239 prefixEnd_4599239 787206750634678729986997 := by
  unfold tailWord_4599239
  simp only [CollatzResearch.WordTrace]
  refine ⟨167748027384750065330456771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111832018256500043553637847 167748027384750065330456771)
  ·
    refine ⟨251622041077125097995685157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167748027384750065330456771 251622041077125097995685157)
    ·
      refine ⟨47179132701960955874190967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251622041077125097995685157 47179132701960955874190967)
      ·
        refine ⟨70768699052941433811286451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47179132701960955874190967 70768699052941433811286451)
        ·
          refine ⟨106153048579412150716929677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70768699052941433811286451 106153048579412150716929677)
          ·
            refine ⟨39807393217279556518848629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106153048579412150716929677 39807393217279556518848629)
            ·
              refine ⟨3731943114119958423642059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39807393217279556518848629 3731943114119958423642059)
              ·
                refine ⟨5597914671179937635463089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731943114119958423642059 5597914671179937635463089)
                ·
                  refine ⟨4198436003384953226597317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5597914671179937635463089 4198436003384953226597317)
                  ·
                    refine ⟨787206750634678729986997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4198436003384953226597317 787206750634678729986997)
                    ·
                      rfl

theorem cell23_4599239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_4599239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599239 prefixEnd_4599239 := by exact prefixLift 4599239
  have htrace : WordTrace (prefixWord ++ tailWord_4599239) baseStart_4599239 baseEnd_4599239 := by
    simpa [prefixWord, tailWord_4599239, baseEnd_4599239] using wordTrace_append hprefix tailTrace_4599239
  have hstable : (prefixWord ++ tailWord_4599239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599239).length < 2 ^ (prefixWord ++ tailWord_4599239).sum := by decide
  have hdescent : baseEnd_4599239 < baseStart_4599239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599242 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_4599242 : Nat := 118140960795 + 4599242 * 2 ^ 59
def prefixEnd_4599242 : Nat := 4983230072969 + 3 ^ 40 * 4599242 * 2
def baseEnd_4599242 : Nat := 2361621792345999678223477

theorem tailTrace_4599242 : CollatzResearch.WordTrace tailWord_4599242 prefixEnd_4599242 2361621792345999678223477 := by
  unfold tailWord_4599242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41937034200934799210703995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111832091202492797895210653 41937034200934799210703995)
  ·
    refine ⟨62905551301402198816055993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41937034200934799210703995 62905551301402198816055993)
    ·
      refine ⟨47179163476051649112041995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62905551301402198816055993 47179163476051649112041995)
      ·
        refine ⟨70768745214077473668062993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47179163476051649112041995 70768745214077473668062993)
        ·
          refine ⟨53076558910558105251047245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70768745214077473668062993 53076558910558105251047245)
          ·
            refine ⟨19903709591459289469142717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53076558910558105251047245 19903709591459289469142717)
            ·
              refine ⟨7463891096797233550928519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19903709591459289469142717 7463891096797233550928519)
              ·
                refine ⟨11195836645195850326392779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463891096797233550928519 11195836645195850326392779)
                ·
                  refine ⟨16793754967793775489589169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11195836645195850326392779 16793754967793775489589169)
                  ·
                    refine ⟨12595316225845331617191877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16793754967793775489589169 12595316225845331617191877)
                    ·
                      refine ⟨2361621792345999678223477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12595316225845331617191877 2361621792345999678223477)
                      ·
                        rfl

theorem cell23_4599242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_4599242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599242 prefixEnd_4599242 := by exact prefixLift 4599242
  have htrace : WordTrace (prefixWord ++ tailWord_4599242) baseStart_4599242 baseEnd_4599242 := by
    simpa [prefixWord, tailWord_4599242, baseEnd_4599242] using wordTrace_append hprefix tailTrace_4599242
  have hstable : (prefixWord ++ tailWord_4599242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599242).length < 2 ^ (prefixWord ++ tailWord_4599242).sum := by decide
  have hdescent : baseEnd_4599242 < baseStart_4599242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599252 : List Nat := [2, 4, 1, 2, 3, 1, 1, 9]
def baseStart_4599252 : Nat := 118140960795 + 4599252 * 2 ^ 59
def prefixEnd_4599252 : Nat := 4983230072969 + 3 ^ 40 * 4599252 * 2
def baseEnd_4599252 : Nat := 87467663968612764411053

theorem tailTrace_4599252 : CollatzResearch.WordTrace tailWord_4599252 prefixEnd_4599252 87467663968612764411053 := by
  unfold tailWord_4599252
  simp only [CollatzResearch.WordTrace]
  refine ⟨83874250766851484275340005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111832334355801979033786673 83874250766851484275340005)
  ·
    refine ⟨15726422018784653301626251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83874250766851484275340005 15726422018784653301626251)
    ·
      refine ⟨23589633028176979952439377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15726422018784653301626251 23589633028176979952439377)
      ·
        refine ⟨17692224771132734964329533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23589633028176979952439377 17692224771132734964329533)
        ·
          refine ⟨6634584289174775611623575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17692224771132734964329533 6634584289174775611623575)
          ·
            refine ⟨9951876433762163417435363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6634584289174775611623575 9951876433762163417435363)
            ·
              refine ⟨14927814650643245126153045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9951876433762163417435363 14927814650643245126153045)
              ·
                refine ⟨87467663968612764411053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14927814650643245126153045 87467663968612764411053)
                ·
                  rfl

theorem cell23_4599252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 9].length) (baseStart_4599252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599252 prefixEnd_4599252 := by exact prefixLift 4599252
  have htrace : WordTrace (prefixWord ++ tailWord_4599252) baseStart_4599252 baseEnd_4599252 := by
    simpa [prefixWord, tailWord_4599252, baseEnd_4599252] using wordTrace_append hprefix tailTrace_4599252
  have hstable : (prefixWord ++ tailWord_4599252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599252).length < 2 ^ (prefixWord ++ tailWord_4599252).sum := by decide
  have hdescent : baseEnd_4599252 < baseStart_4599252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599305 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_4599305 : Nat := 118140960795 + 4599305 * 2 ^ 59
def prefixEnd_4599305 : Nat := 4983230072969 + 3 ^ 40 * 4599305 * 2
def baseEnd_4599305 : Nat := 2361654141627232931735687

theorem tailTrace_4599305 : CollatzResearch.WordTrace tailWord_4599305 prefixEnd_4599305 2361654141627232931735687 := by
  unfold tailWord_4599305
  simp only [CollatzResearch.WordTrace]
  refine ⟨167750434602510958602359369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111833623068340639068239579 167750434602510958602359369)
  ·
    refine ⟨125812825951883218951769527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167750434602510958602359369 125812825951883218951769527)
    ·
      refine ⟨188719238927824828427654291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125812825951883218951769527 188719238927824828427654291)
      ·
        refine ⟨283078858391737242641481437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188719238927824828427654291 283078858391737242641481437)
        ·
          refine ⟨106154571896901465990555539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283078858391737242641481437 106154571896901465990555539)
          ·
            refine ⟨159231857845352198985833309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106154571896901465990555539 159231857845352198985833309)
            ·
              refine ⟨59711946692007074619687491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159231857845352198985833309 59711946692007074619687491)
              ·
                refine ⟨89567920038010611929531237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59711946692007074619687491 89567920038010611929531237)
                ·
                  refine ⟨16793985007126989736787107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89567920038010611929531237 16793985007126989736787107)
                  ·
                    refine ⟨25190977510690484605180661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16793985007126989736787107 25190977510690484605180661)
                    ·
                      refine ⟨2361654141627232931735687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25190977510690484605180661 2361654141627232931735687)
                      ·
                        rfl

theorem cell23_4599305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_4599305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599305 prefixEnd_4599305 := by exact prefixLift 4599305
  have htrace : WordTrace (prefixWord ++ tailWord_4599305) baseStart_4599305 baseEnd_4599305 := by
    simpa [prefixWord, tailWord_4599305, baseEnd_4599305] using wordTrace_append hprefix tailTrace_4599305
  have hstable : (prefixWord ++ tailWord_4599305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599305).length < 2 ^ (prefixWord ++ tailWord_4599305).sum := by decide
  have hdescent : baseEnd_4599305 < baseStart_4599305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599306 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_4599306 : Nat := 118140960795 + 4599306 * 2 ^ 59
def prefixEnd_4599306 : Nat := 4983230072969 + 3 ^ 40 * 4599306 * 2
def baseEnd_4599306 : Nat := 2361654655107887427823183

theorem tailTrace_4599306 : CollatzResearch.WordTrace tailWord_4599306 prefixEnd_4599306 2361654655107887427823183 := by
  unfold tailWord_4599306
  simp only [CollatzResearch.WordTrace]
  refine ⟨41937617768876833943286443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111833647383671557182097181 41937617768876833943286443)
  ·
    refine ⟨62906426653315250914929665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41937617768876833943286443 62906426653315250914929665)
    ·
      refine ⟨47179819989986438186197249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62906426653315250914929665 47179819989986438186197249)
      ·
        refine ⟨35384864992489828639647937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47179819989986438186197249 35384864992489828639647937)
        ·
          refine ⟨26538648744367371479735953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35384864992489828639647937 26538648744367371479735953)
          ·
            refine ⟨19903986558275528609801965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26538648744367371479735953 19903986558275528609801965)
            ·
              refine ⟨7463994959353323228675737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19903986558275528609801965 7463994959353323228675737)
              ·
                refine ⟨5597996219514992421506803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7463994959353323228675737 5597996219514992421506803)
                ·
                  refine ⟨8396994329272488632260205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5597996219514992421506803 8396994329272488632260205)
                  ·
                    refine ⟨3148872873477183237097577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8396994329272488632260205 3148872873477183237097577)
                    ·
                      refine ⟨2361654655107887427823183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3148872873477183237097577 2361654655107887427823183)
                      ·
                        rfl

theorem cell23_4599306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_4599306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599306 prefixEnd_4599306 := by exact prefixLift 4599306
  have htrace : WordTrace (prefixWord ++ tailWord_4599306) baseStart_4599306 baseEnd_4599306 := by
    simpa [prefixWord, tailWord_4599306, baseEnd_4599306] using wordTrace_append hprefix tailTrace_4599306
  have hstable : (prefixWord ++ tailWord_4599306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599306).length < 2 ^ (prefixWord ++ tailWord_4599306).sum := by decide
  have hdescent : baseEnd_4599306 < baseStart_4599306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599345 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4599345 : Nat := 118140960795 + 4599345 * 2 ^ 59
def prefixEnd_4599345 : Nat := 4983230072969 + 3 ^ 40 * 4599345 * 2
def baseEnd_4599345 : Nat := 2361674680853412775235503

theorem tailTrace_4599345 : CollatzResearch.WordTrace tailWord_4599345 prefixEnd_4599345 2361674680853412775235503 := by
  unfold tailWord_4599345
  simp only [CollatzResearch.WordTrace]
  refine ⟨167751893522366045433815489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111834595681577363622543659 167751893522366045433815489)
  ·
    refine ⟨125813920141774534075361617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167751893522366045433815489 125813920141774534075361617)
    ·
      refine ⟨94360440106330900556521213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125813920141774534075361617 94360440106330900556521213)
      ·
        refine ⟨35385165039874087708695455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94360440106330900556521213 35385165039874087708695455)
        ·
          refine ⟨53077747559811131563043183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35385165039874087708695455 53077747559811131563043183)
          ·
            refine ⟨79616621339716697344564775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53077747559811131563043183 79616621339716697344564775)
            ·
              refine ⟨119424932009575046016847163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79616621339716697344564775 119424932009575046016847163)
              ·
                refine ⟨179137398014362569025270745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119424932009575046016847163 179137398014362569025270745)
                ·
                  refine ⟨134353048510771926768953059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179137398014362569025270745 134353048510771926768953059)
                  ·
                    refine ⟨201529572766157890153429589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134353048510771926768953059 201529572766157890153429589)
                    ·
                      refine ⟨2361674680853412775235503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 201529572766157890153429589 2361674680853412775235503)
                      ·
                        rfl

theorem cell23_4599345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4599345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599345 prefixEnd_4599345 := by exact prefixLift 4599345
  have htrace : WordTrace (prefixWord ++ tailWord_4599345) baseStart_4599345 baseEnd_4599345 := by
    simpa [prefixWord, tailWord_4599345, baseEnd_4599345] using wordTrace_append hprefix tailTrace_4599345
  have hstable : (prefixWord ++ tailWord_4599345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599345).length < 2 ^ (prefixWord ++ tailWord_4599345).sum := by decide
  have hdescent : baseEnd_4599345 < baseStart_4599345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599352 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_4599352 : Nat := 118140960795 + 4599352 * 2 ^ 59
def prefixEnd_4599352 : Nat := 4983230072969 + 3 ^ 40 * 4599352 * 2
def baseEnd_4599352 : Nat := 2361678275217994247847971

theorem tailTrace_4599352 : CollatzResearch.WordTrace tailWord_4599352 prefixEnd_4599352 2361678275217994247847971 := by
  unfold tailWord_4599352
  simp only [CollatzResearch.WordTrace]
  refine ⟨83876074416670342814660155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111834765888893790419546873 83876074416670342814660155)
  ·
    refine ⟨125814111625005514221990233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83876074416670342814660155 125814111625005514221990233)
    ·
      refine ⟨94360583718754135666492675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125814111625005514221990233 94360583718754135666492675)
      ·
        refine ⟨141540875578131203499739013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94360583718754135666492675 141540875578131203499739013)
        ·
          refine ⟨26538914170899600656201065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141540875578131203499739013 26538914170899600656201065)
          ·
            refine ⟨19904185628174700492150799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26538914170899600656201065 19904185628174700492150799)
            ·
              refine ⟨29856278442262050738226199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19904185628174700492150799 29856278442262050738226199)
              ·
                refine ⟨44784417663393076107339299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29856278442262050738226199 44784417663393076107339299)
                ·
                  refine ⟨67176626495089614161008949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44784417663393076107339299 67176626495089614161008949)
                  ·
                    refine ⟨6297808733914651327594589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67176626495089614161008949 6297808733914651327594589)
                    ·
                      refine ⟨2361678275217994247847971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6297808733914651327594589 2361678275217994247847971)
                      ·
                        rfl

theorem cell23_4599352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_4599352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599352 prefixEnd_4599352 := by exact prefixLift 4599352
  have htrace : WordTrace (prefixWord ++ tailWord_4599352) baseStart_4599352 baseEnd_4599352 := by
    simpa [prefixWord, tailWord_4599352, baseEnd_4599352] using wordTrace_append hprefix tailTrace_4599352
  have hstable : (prefixWord ++ tailWord_4599352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599352).length < 2 ^ (prefixWord ++ tailWord_4599352).sum := by decide
  have hdescent : baseEnd_4599352 < baseStart_4599352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599372 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_4599372 : Nat := 118140960795 + 4599372 * 2 ^ 59
def prefixEnd_4599372 : Nat := 4983230072969 + 3 ^ 40 * 4599372 * 2
def baseEnd_4599372 : Nat := 787229514943694723199293

theorem tailTrace_4599372 : CollatzResearch.WordTrace tailWord_4599372 prefixEnd_4599372 787229514943694723199293 := by
  unfold tailWord_4599372
  simp only [CollatzResearch.WordTrace]
  refine ⟨83876439146634114522524185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111835252195512152696698913 83876439146634114522524185)
  ·
    refine ⟨62907329359975585891893139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83876439146634114522524185 62907329359975585891893139)
    ·
      refine ⟨94360994039963378837839709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62907329359975585891893139 94360994039963378837839709)
      ·
        refine ⟨35385372764986267064189891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94360994039963378837839709 35385372764986267064189891)
        ·
          refine ⟨53078059147479400596284837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35385372764986267064189891 53078059147479400596284837)
          ·
            refine ⟨9952136090152387611803407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53078059147479400596284837 9952136090152387611803407)
            ·
              refine ⟨14928204135228581417705111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9952136090152387611803407 14928204135228581417705111)
              ·
                refine ⟨22392306202842872126557667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14928204135228581417705111 22392306202842872126557667)
                ·
                  refine ⟨33588459304264308189836501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22392306202842872126557667 33588459304264308189836501)
                  ·
                    refine ⟨787229514943694723199293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33588459304264308189836501 787229514943694723199293)
                    ·
                      rfl

theorem cell23_4599372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_4599372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599372 prefixEnd_4599372 := by exact prefixLift 4599372
  have htrace : WordTrace (prefixWord ++ tailWord_4599372) baseStart_4599372 baseEnd_4599372 := by
    simpa [prefixWord, tailWord_4599372, baseEnd_4599372] using wordTrace_append hprefix tailTrace_4599372
  have hstable : (prefixWord ++ tailWord_4599372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599372).length < 2 ^ (prefixWord ++ tailWord_4599372).sum := by decide
  have hdescent : baseEnd_4599372 < baseStart_4599372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599385 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_4599385 : Nat := 118140960795 + 4599385 * 2 ^ 59
def prefixEnd_4599385 : Nat := 4983230072969 + 3 ^ 40 * 4599385 * 2
def baseEnd_4599385 : Nat := 787231740026530872911773

theorem tailTrace_4599385 : CollatzResearch.WordTrace tailWord_4599385 prefixEnd_4599385 787231740026530872911773 := by
  unfold tailWord_4599385
  simp only [CollatzResearch.WordTrace]
  refine ⟨167753352442221132265271609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111835568294814088176847739 167753352442221132265271609)
  ·
    refine ⟨125815014331665849198953707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167753352442221132265271609 125815014331665849198953707)
    ·
      refine ⟨188722521497498773798430561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125815014331665849198953707 188722521497498773798430561)
      ·
        refine ⟨141541891123124080348822921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188722521497498773798430561 141541891123124080348822921)
        ·
          refine ⟨106156418342343060261617191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141541891123124080348822921 106156418342343060261617191)
          ·
            refine ⟨159234627513514590392425787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106156418342343060261617191 159234627513514590392425787)
            ·
              refine ⟨238851941270271885588638681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159234627513514590392425787 238851941270271885588638681)
              ·
                refine ⟨179138955952703914191479011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238851941270271885588638681 179138955952703914191479011)
                ·
                  refine ⟨268708433929055871287218517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179138955952703914191479011 268708433929055871287218517)
                  ·
                    refine ⟨787231740026530872911773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 268708433929055871287218517 787231740026530872911773)
                    ·
                      rfl

theorem cell23_4599385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_4599385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599385 prefixEnd_4599385 := by exact prefixLift 4599385
  have htrace : WordTrace (prefixWord ++ tailWord_4599385) baseStart_4599385 baseEnd_4599385 := by
    simpa [prefixWord, tailWord_4599385, baseEnd_4599385] using wordTrace_append hprefix tailTrace_4599385
  have hstable : (prefixWord ++ tailWord_4599385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599385).length < 2 ^ (prefixWord ++ tailWord_4599385).sum := by decide
  have hdescent : baseEnd_4599385 < baseStart_4599385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599392 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_4599392 : Nat := 118140960795 + 4599392 * 2 ^ 59
def prefixEnd_4599392 : Nat := 4983230072969 + 3 ^ 40 * 4599392 * 2
def baseEnd_4599392 : Nat := 2361698814444174091347787

theorem tailTrace_4599392 : CollatzResearch.WordTrace tailWord_4599392 prefixEnd_4599392 2361698814444174091347787 := by
  unfold tailWord_4599392
  simp only [CollatzResearch.WordTrace]
  refine ⟨83876803876597886230388215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111835738502130514973850953 83876803876597886230388215)
  ·
    refine ⟨125815205814896829345582323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83876803876597886230388215 125815205814896829345582323)
    ·
      refine ⟨188722808722345244018373485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125815205814896829345582323 188722808722345244018373485)
      ·
        refine ⟨70771053270879466506890057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188722808722345244018373485 70771053270879466506890057)
        ·
          refine ⟨53078289953159599880167543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70771053270879466506890057 53078289953159599880167543)
          ·
            refine ⟨79617434929739399820251315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53078289953159599880167543 79617434929739399820251315)
            ·
              refine ⟨119426152394609099730376973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79617434929739399820251315 119426152394609099730376973)
              ·
                refine ⟨44784807147978412398891365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119426152394609099730376973 44784807147978412398891365)
                ·
                  refine ⟨8397151340245952324792131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44784807147978412398891365 8397151340245952324792131)
                  ·
                    refine ⟨12595727010368928487188197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8397151340245952324792131 12595727010368928487188197)
                    ·
                      refine ⟨2361698814444174091347787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12595727010368928487188197 2361698814444174091347787)
                      ·
                        rfl

theorem cell23_4599392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_4599392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599392 prefixEnd_4599392 := by exact prefixLift 4599392
  have htrace : WordTrace (prefixWord ++ tailWord_4599392) baseStart_4599392 baseEnd_4599392 := by
    simpa [prefixWord, tailWord_4599392, baseEnd_4599392] using wordTrace_append hprefix tailTrace_4599392
  have hstable : (prefixWord ++ tailWord_4599392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599392).length < 2 ^ (prefixWord ++ tailWord_4599392).sum := by decide
  have hdescent : baseEnd_4599392 < baseStart_4599392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599429 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_4599429 : Nat := 118140960795 + 4599429 * 2 ^ 59
def prefixEnd_4599429 : Nat := 4983230072969 + 3 ^ 40 * 4599429 * 2
def baseEnd_4599429 : Nat := 2361717813228390446585117

theorem tailTrace_4599429 : CollatzResearch.WordTrace tailWord_4599429 prefixEnd_4599429 2361717813228390446585117 := by
  unfold tailWord_4599429
  simp only [CollatzResearch.WordTrace]
  refine ⟨167754957254061727779873341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111836638169374485186582227 167754957254061727779873341)
  ·
    refine ⟨62908108970273147917452503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167754957254061727779873341 62908108970273147917452503)
    ·
      refine ⟨94362163455409721876178755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62908108970273147917452503 94362163455409721876178755)
      ·
        refine ⟨141543245183114582814268133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94362163455409721876178755 141543245183114582814268133)
        ·
          refine ⟨26539358471833984277675275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141543245183114582814268133 26539358471833984277675275)
          ·
            refine ⟨39809037707750976416512913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26539358471833984277675275 39809037707750976416512913)
            ·
              refine ⟨29856778280813232312384685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39809037707750976416512913 29856778280813232312384685)
              ·
                refine ⟨11196291855304962117144257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29856778280813232312384685 11196291855304962117144257)
                ·
                  refine ⟨8397218891478721587858193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11196291855304962117144257 8397218891478721587858193)
                  ·
                    refine ⟨6297914168609041190893645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8397218891478721587858193 6297914168609041190893645)
                    ·
                      refine ⟨2361717813228390446585117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6297914168609041190893645 2361717813228390446585117)
                      ·
                        rfl

theorem cell23_4599429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_4599429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599429 prefixEnd_4599429 := by exact prefixLift 4599429
  have htrace : WordTrace (prefixWord ++ tailWord_4599429) baseStart_4599429 baseEnd_4599429 := by
    simpa [prefixWord, tailWord_4599429, baseEnd_4599429] using wordTrace_append hprefix tailTrace_4599429
  have hstable : (prefixWord ++ tailWord_4599429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599429).length < 2 ^ (prefixWord ++ tailWord_4599429).sum := by decide
  have hdescent : baseEnd_4599429 < baseStart_4599429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599479 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 3, 5]
def baseStart_4599479 : Nat := 118140960795 + 4599479 * 2 ^ 59
def prefixEnd_4599479 : Nat := 4983230072969 + 3 ^ 40 * 4599479 * 2
def baseEnd_4599479 : Nat := 787247829087038416986629

theorem tailTrace_4599479 : CollatzResearch.WordTrace tailWord_4599479 prefixEnd_4599479 787247829087038416986629 := by
  unfold tailWord_4599479
  simp only [CollatzResearch.WordTrace]
  refine ⟨167756780903880586319193491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111837853935920390879462327 167756780903880586319193491)
  ·
    refine ⟨251635171355820879478790237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167756780903880586319193491 251635171355820879478790237)
    ·
      refine ⟨94363189258432829804546339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251635171355820879478790237 94363189258432829804546339)
      ·
        refine ⟨141544783887649244706819509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94363189258432829804546339 141544783887649244706819509)
        ·
          refine ⟨13269823489467116691264329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141544783887649244706819509 13269823489467116691264329)
          ·
            refine ⟨9952367617100337518448247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13269823489467116691264329 9952367617100337518448247)
            ·
              refine ⟨14928551425650506277672371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9952367617100337518448247 14928551425650506277672371)
              ·
                refine ⟨22392827138475759416508557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14928551425650506277672371 22392827138475759416508557)
                ·
                  refine ⟨8397310176928409781190709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22392827138475759416508557 8397310176928409781190709)
                  ·
                    refine ⟨787247829087038416986629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8397310176928409781190709 787247829087038416986629)
                    ·
                      rfl

theorem cell23_4599479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_4599479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599479 prefixEnd_4599479 := by exact prefixLift 4599479
  have htrace : WordTrace (prefixWord ++ tailWord_4599479) baseStart_4599479 baseEnd_4599479 := by
    simpa [prefixWord, tailWord_4599479, baseEnd_4599479] using wordTrace_append hprefix tailTrace_4599479
  have hstable : (prefixWord ++ tailWord_4599479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599479).length < 2 ^ (prefixWord ++ tailWord_4599479).sum := by decide
  have hdescent : baseEnd_4599479 < baseStart_4599479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599496 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 1, 5]
def baseStart_4599496 : Nat := 118140960795 + 4599496 * 2 ^ 59
def prefixEnd_4599496 : Nat := 4983230072969 + 3 ^ 40 * 4599496 * 2
def baseEnd_4599496 : Nat := 787250738810747228149103

theorem tailTrace_4599496 : CollatzResearch.WordTrace tailWord_4599496 prefixEnd_4599496 787250738810747228149103 := by
  unfold tailWord_4599496
  simp only [CollatzResearch.WordTrace]
  refine ⟨83878700472409499111281171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111838267296545998815041561 83878700472409499111281171)
  ·
    refine ⟨125818050708614248666921757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83878700472409499111281171 125818050708614248666921757)
    ·
      refine ⟨47181769015730343250095659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125818050708614248666921757 47181769015730343250095659)
      ·
        refine ⟨70772653523595514875143489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47181769015730343250095659 70772653523595514875143489)
        ·
          refine ⟨53079490142696636156357617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70772653523595514875143489 53079490142696636156357617)
          ·
            refine ⟨39809617607022477117268213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53079490142696636156357617 39809617607022477117268213)
            ·
              refine ⟨3732151650658357229743895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39809617607022477117268213 3732151650658357229743895)
              ·
                refine ⟨5598227475987535844615843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732151650658357229743895 5598227475987535844615843)
                ·
                  refine ⟨8397341213981303766923765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598227475987535844615843 8397341213981303766923765)
                  ·
                    refine ⟨787250738810747228149103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8397341213981303766923765 787250738810747228149103)
                    ·
                      rfl

theorem cell23_4599496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_4599496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599496 prefixEnd_4599496 := by exact prefixLift 4599496
  have htrace : WordTrace (prefixWord ++ tailWord_4599496) baseStart_4599496 baseEnd_4599496 := by
    simpa [prefixWord, tailWord_4599496, baseEnd_4599496] using wordTrace_append hprefix tailTrace_4599496
  have hstable : (prefixWord ++ tailWord_4599496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599496).length < 2 ^ (prefixWord ++ tailWord_4599496).sum := by decide
  have hdescent : baseEnd_4599496 < baseStart_4599496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599499 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 4]
def baseStart_4599499 : Nat := 118140960795 + 4599499 * 2 ^ 59
def prefixEnd_4599499 : Nat := 4983230072969 + 3 ^ 40 * 4599499 * 2
def baseEnd_4599499 : Nat := 2361753756874205172709795

theorem tailTrace_4599499 : CollatzResearch.WordTrace tailWord_4599499 prefixEnd_4599499 2361753756874205172709795 := by
  unfold tailWord_4599499
  simp only [CollatzResearch.WordTrace]
  refine ⟨167757510363808129734921551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111838340242538753156614367 167757510363808129734921551)
  ·
    refine ⟨251636265545712194602382327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167757510363808129734921551 251636265545712194602382327)
    ·
      refine ⟨377454398318568291903573491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251636265545712194602382327 377454398318568291903573491)
      ·
        refine ⟨566181597477852437855360237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377454398318568291903573491 566181597477852437855360237)
        ·
          refine ⟨212318099054194664195760089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566181597477852437855360237 212318099054194664195760089)
          ·
            refine ⟨159238574290645998146820067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212318099054194664195760089 159238574290645998146820067)
            ·
              refine ⟨238857861435968997220230101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159238574290645998146820067 238857861435968997220230101)
              ·
                refine ⟨5598231127405523372349143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 238857861435968997220230101 5598231127405523372349143)
                ·
                  refine ⟨8397346691108285058523715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598231127405523372349143 8397346691108285058523715)
                  ·
                    refine ⟨12596020036662427587785573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8397346691108285058523715 12596020036662427587785573)
                    ·
                      refine ⟨2361753756874205172709795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12596020036662427587785573 2361753756874205172709795)
                      ·
                        rfl

theorem cell23_4599499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 4].length) (baseStart_4599499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599499 prefixEnd_4599499 := by exact prefixLift 4599499
  have htrace : WordTrace (prefixWord ++ tailWord_4599499) baseStart_4599499 baseEnd_4599499 := by
    simpa [prefixWord, tailWord_4599499, baseEnd_4599499] using wordTrace_append hprefix tailTrace_4599499
  have hstable : (prefixWord ++ tailWord_4599499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599499).length < 2 ^ (prefixWord ++ tailWord_4599499).sum := by decide
  have hdescent : baseEnd_4599499 < baseStart_4599499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599519 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3]
def baseStart_4599519 : Nat := 118140960795 + 4599519 * 2 ^ 59
def prefixEnd_4599519 : Nat := 4983230072969 + 3 ^ 40 * 4599519 * 2
def baseEnd_4599519 : Nat := 2361764026487295094459703

theorem tailTrace_4599519 : CollatzResearch.WordTrace tailWord_4599519 prefixEnd_4599519 2361764026487295094459703 := by
  unfold tailWord_4599519
  simp only [CollatzResearch.WordTrace]
  refine ⟨167758239823735673150649611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111838826549157115433766407 167758239823735673150649611)
  ·
    refine ⟨251637359735603509725974417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167758239823735673150649611 251637359735603509725974417)
    ·
      refine ⟨188728019801702632294480813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251637359735603509725974417 188728019801702632294480813)
      ·
        refine ⟨70773007425638487110430305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188728019801702632294480813 70773007425638487110430305)
        ·
          refine ⟨53079755569228865332822729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70773007425638487110430305 53079755569228865332822729)
          ·
            refine ⟨39809816676921648999617047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53079755569228865332822729 39809816676921648999617047)
            ·
              refine ⟨59714725015382473499425571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39809816676921648999617047 59714725015382473499425571)
              ·
                refine ⟨89572087523073710249138357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59714725015382473499425571 89572087523073710249138357)
                ·
                  refine ⟨8397383205288160335856721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89572087523073710249138357 8397383205288160335856721)
                  ·
                    refine ⟨6298037403966120251892541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8397383205288160335856721 6298037403966120251892541)
                    ·
                      refine ⟨2361764026487295094459703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298037403966120251892541 2361764026487295094459703)
                      ·
                        rfl

theorem cell23_4599519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_4599519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599519 prefixEnd_4599519 := by exact prefixLift 4599519
  have htrace : WordTrace (prefixWord ++ tailWord_4599519) baseStart_4599519 baseEnd_4599519 := by
    simpa [prefixWord, tailWord_4599519, baseEnd_4599519] using wordTrace_append hprefix tailTrace_4599519
  have hstable : (prefixWord ++ tailWord_4599519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599519).length < 2 ^ (prefixWord ++ tailWord_4599519).sum := by decide
  have hdescent : baseEnd_4599519 < baseStart_4599519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599533 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4599533 : Nat := 118140960795 + 4599533 * 2 ^ 59
def prefixEnd_4599533 : Nat := 4983230072969 + 3 ^ 40 * 4599533 * 2
def baseEnd_4599533 : Nat := 2361771215216458039684639

theorem tailTrace_4599533 : CollatzResearch.WordTrace tailWord_4599533 prefixEnd_4599533 2361771215216458039684639 := by
  unfold tailWord_4599533
  simp only [CollatzResearch.WordTrace]
  refine ⟨167758750445684953541659253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111839166963789969027772835 167758750445684953541659253)
  ·
    refine ⟨15727382854282964394530555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167758750445684953541659253 15727382854282964394530555)
    ·
      refine ⟨23591074281424446591795833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15727382854282964394530555 23591074281424446591795833)
      ·
        refine ⟨17693305711068334943846875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23591074281424446591795833 17693305711068334943846875)
        ·
          refine ⟨26539958566602502415770313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17693305711068334943846875 26539958566602502415770313)
          ·
            refine ⟨19904968924951876811827735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26539958566602502415770313 19904968924951876811827735)
            ·
              refine ⟨29857453387427815217741603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19904968924951876811827735 29857453387427815217741603)
              ·
                refine ⟨44786180081141722826612405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29857453387427815217741603 44786180081141722826612405)
                ·
                  refine ⟨4198704382607036514994913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44786180081141722826612405 4198704382607036514994913)
                  ·
                    refine ⟨3149028286955277386246185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198704382607036514994913 3149028286955277386246185)
                    ·
                      refine ⟨2361771215216458039684639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149028286955277386246185 2361771215216458039684639)
                      ·
                        rfl

theorem cell23_4599533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4599533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599533 prefixEnd_4599533 := by exact prefixLift 4599533
  have htrace : WordTrace (prefixWord ++ tailWord_4599533) baseStart_4599533 baseEnd_4599533 := by
    simpa [prefixWord, tailWord_4599533, baseEnd_4599533] using wordTrace_append hprefix tailTrace_4599533
  have hstable : (prefixWord ++ tailWord_4599533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599533).length < 2 ^ (prefixWord ++ tailWord_4599533).sum := by decide
  have hdescent : baseEnd_4599533 < baseStart_4599533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599549 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_4599549 : Nat := 118140960795 + 4599549 * 2 ^ 59
def prefixEnd_4599549 : Nat := 4983230072969 + 3 ^ 40 * 4599549 * 2
def baseEnd_4599549 : Nat := 2361779430906929977084565

theorem tailTrace_4599549 : CollatzResearch.WordTrace tailWord_4599549 prefixEnd_4599549 2361779430906929977084565 := by
  unfold tailWord_4599549
  simp only [CollatzResearch.WordTrace]
  refine ⟨167759334013626988274241701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111839556009084658849494467 167759334013626988274241701)
  ·
    refine ⟨31454875127555060301420319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167759334013626988274241701 31454875127555060301420319)
    ·
      refine ⟨47182312691332590452130479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31454875127555060301420319 47182312691332590452130479)
      ·
        refine ⟨70773469036998885678195719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47182312691332590452130479 70773469036998885678195719)
        ·
          refine ⟨106160203555498328517293579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70773469036998885678195719 106160203555498328517293579)
          ·
            refine ⟨159240305333247492775940369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106160203555498328517293579 159240305333247492775940369)
            ·
              refine ⟨119430228999935619581955277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159240305333247492775940369 119430228999935619581955277)
              ·
                refine ⟨44786335874975857343233229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119430228999935619581955277 44786335874975857343233229)
                ·
                  refine ⟨16794875953115946503712461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44786335874975857343233229 16794875953115946503712461)
                  ·
                    refine ⟨6298078482418479938892173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16794875953115946503712461 6298078482418479938892173)
                    ·
                      refine ⟨2361779430906929977084565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298078482418479938892173 2361779430906929977084565)
                      ·
                        rfl

theorem cell23_4599549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_4599549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599549 prefixEnd_4599549 := by exact prefixLift 4599549
  have htrace : WordTrace (prefixWord ++ tailWord_4599549) baseStart_4599549 baseEnd_4599549 := by
    simpa [prefixWord, tailWord_4599549, baseEnd_4599549] using wordTrace_append hprefix tailTrace_4599549
  have hstable : (prefixWord ++ tailWord_4599549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599549).length < 2 ^ (prefixWord ++ tailWord_4599549).sum := by decide
  have hdescent : baseEnd_4599549 < baseStart_4599549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599552 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_4599552 : Nat := 118140960795 + 4599552 * 2 ^ 59
def prefixEnd_4599552 : Nat := 4983230072969 + 3 ^ 40 * 4599552 * 2
def baseEnd_4599552 : Nat := 787260323782964488449017

theorem tailTrace_4599552 : CollatzResearch.WordTrace tailWord_4599552 prefixEnd_4599552 787260323782964488449017 := by
  unfold tailWord_4599552
  simp only [CollatzResearch.WordTrace]
  refine ⟨83879721716308059893300455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111839628955077413191067273 83879721716308059893300455)
  ·
    refine ⟨125819582574462089839950683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83879721716308059893300455 125819582574462089839950683)
    ·
      refine ⟨188729373861693134759926025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125819582574462089839950683 188729373861693134759926025)
      ·
        refine ⟨141547030396269851069944519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188729373861693134759926025 141547030396269851069944519)
        ·
          refine ⟨212320545594404776604916779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141547030396269851069944519 212320545594404776604916779)
          ·
            refine ⟨318480818391607164907375169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212320545594404776604916779 318480818391607164907375169)
            ·
              refine ⟨238860613793705373680531377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318480818391607164907375169 238860613793705373680531377)
              ·
                refine ⟨179145460345279030260398533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238860613793705373680531377 179145460345279030260398533)
                ·
                  refine ⟨33589773814739818173824725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179145460345279030260398533 33589773814739818173824725)
                  ·
                    refine ⟨787260323782964488449017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33589773814739818173824725 787260323782964488449017)
                    ·
                      rfl

theorem cell23_4599552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_4599552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599552 prefixEnd_4599552 := by exact prefixLift 4599552
  have htrace : WordTrace (prefixWord ++ tailWord_4599552) baseStart_4599552 baseEnd_4599552 := by
    simpa [prefixWord, tailWord_4599552, baseEnd_4599552] using wordTrace_append hprefix tailTrace_4599552
  have hstable : (prefixWord ++ tailWord_4599552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599552).length < 2 ^ (prefixWord ++ tailWord_4599552).sum := by decide
  have hdescent : baseEnd_4599552 < baseStart_4599552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599553 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_4599553 : Nat := 118140960795 + 4599553 * 2 ^ 59
def prefixEnd_4599553 : Nat := 4983230072969 + 3 ^ 40 * 4599553 * 2
def baseEnd_4599553 : Nat := 2361781484829547961434547

theorem tailTrace_4599553 : CollatzResearch.WordTrace tailWord_4599553 prefixEnd_4599553 2361781484829547961434547 := by
  unfold tailWord_4599553
  simp only [CollatzResearch.WordTrace]
  refine ⟨167759479905612496957387313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111839653270408331304924875 167759479905612496957387313)
  ·
    refine ⟨125819609929209372718040485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167759479905612496957387313 125819609929209372718040485)
    ·
      refine ⟨23591176861726757384632591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125819609929209372718040485 23591176861726757384632591)
      ·
        refine ⟨35386765292590136076948887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23591176861726757384632591 35386765292590136076948887)
        ·
          refine ⟨53080147938885204115423331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35386765292590136076948887 53080147938885204115423331)
          ·
            refine ⟨79620221908327806173134997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53080147938885204115423331 79620221908327806173134997)
            ·
              refine ⟨3732197901952865914365703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79620221908327806173134997 3732197901952865914365703)
              ·
                refine ⟨5598296852929298871548555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732197901952865914365703 5598296852929298871548555)
                ·
                  refine ⟨8397445279393948307322833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598296852929298871548555 8397445279393948307322833)
                  ·
                    refine ⟨6298083959545461230492125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8397445279393948307322833 6298083959545461230492125)
                    ·
                      refine ⟨2361781484829547961434547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298083959545461230492125 2361781484829547961434547)
                      ·
                        rfl

theorem cell23_4599553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_4599553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599553 prefixEnd_4599553 := by exact prefixLift 4599553
  have htrace : WordTrace (prefixWord ++ tailWord_4599553) baseStart_4599553 baseEnd_4599553 := by
    simpa [prefixWord, tailWord_4599553, baseEnd_4599553] using wordTrace_append hprefix tailTrace_4599553
  have hstable : (prefixWord ++ tailWord_4599553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599553).length < 2 ^ (prefixWord ++ tailWord_4599553).sum := by decide
  have hdescent : baseEnd_4599553 < baseStart_4599553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599576 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_4599576 : Nat := 118140960795 + 4599576 * 2 ^ 59
def prefixEnd_4599576 : Nat := 4983230072969 + 3 ^ 40 * 4599576 * 2
def baseEnd_4599576 : Nat := 2361793294884601371446941

theorem tailTrace_4599576 : CollatzResearch.WordTrace tailWord_4599576 prefixEnd_4599576 2361793294884601371446941 := by
  unfold tailWord_4599576
  simp only [CollatzResearch.WordTrace]
  refine ⟨83880159392264585942737291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111840212523019447923649721 83880159392264585942737291)
  ·
    refine ⟨125820239088396878914105937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83880159392264585942737291 125820239088396878914105937)
    ·
      refine ⟨94365179316297659185579453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125820239088396878914105937 94365179316297659185579453)
      ·
        refine ⟨35386942243611622194592295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94365179316297659185579453 35386942243611622194592295)
        ·
          refine ⟨53080413365417433291888443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35386942243611622194592295 53080413365417433291888443)
          ·
            refine ⟨79620620048126149937832665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53080413365417433291888443 79620620048126149937832665)
            ·
              refine ⟨59715465036094612453374499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79620620048126149937832665 59715465036094612453374499)
              ·
                refine ⟨89573197554141918680061749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59715465036094612453374499 89573197554141918680061749)
                ·
                  refine ⟨8397487270700804876255789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89573197554141918680061749 8397487270700804876255789)
                  ·
                    refine ⟨3149057726512801828595921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8397487270700804876255789 3149057726512801828595921)
                    ·
                      refine ⟨2361793294884601371446941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149057726512801828595921 2361793294884601371446941)
                      ·
                        rfl

theorem cell23_4599576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_4599576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599576 prefixEnd_4599576 := by exact prefixLift 4599576
  have htrace : WordTrace (prefixWord ++ tailWord_4599576) baseStart_4599576 baseEnd_4599576 := by
    simpa [prefixWord, tailWord_4599576, baseEnd_4599576] using wordTrace_append hprefix tailTrace_4599576
  have hstable : (prefixWord ++ tailWord_4599576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599576).length < 2 ^ (prefixWord ++ tailWord_4599576).sum := by decide
  have hdescent : baseEnd_4599576 < baseStart_4599576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599623 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_4599623 : Nat := 118140960795 + 4599623 * 2 ^ 59
def prefixEnd_4599623 : Nat := 4983230072969 + 3 ^ 40 * 4599623 * 2
def baseEnd_4599623 : Nat := 2361817428475362687559225

theorem tailTrace_4599623 : CollatzResearch.WordTrace tailWord_4599623 prefixEnd_4599623 2361817428475362687559225 := by
  unfold tailWord_4599623
  simp only [CollatzResearch.WordTrace]
  refine ⟨167762033015358898912435523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111841355343572599274957015 167762033015358898912435523)
  ·
    refine ⟨251643049523038348368653285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167762033015358898912435523 251643049523038348368653285)
    ·
      refine ⟨47183071785569690319122491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251643049523038348368653285 47183071785569690319122491)
      ·
        refine ⟨70774607678354535478683737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47183071785569690319122491 70774607678354535478683737)
        ·
          refine ⟨53080955758765901609012803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70774607678354535478683737 53080955758765901609012803)
          ·
            refine ⟨79621433638148852413519205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53080955758765901609012803 79621433638148852413519205)
            ·
              refine ⟨14929018807152909827534851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79621433638148852413519205 14929018807152909827534851)
              ·
                refine ⟨22393528210729364741302277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14929018807152909827534851 22393528210729364741302277)
                ·
                  refine ⟨4198786539511755888994177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22393528210729364741302277 4198786539511755888994177)
                  ·
                    refine ⟨3149089904633816916745633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198786539511755888994177 3149089904633816916745633)
                    ·
                      refine ⟨2361817428475362687559225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149089904633816916745633 2361817428475362687559225)
                      ·
                        rfl

theorem cell23_4599623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_4599623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599623 prefixEnd_4599623 := by exact prefixLift 4599623
  have htrace : WordTrace (prefixWord ++ tailWord_4599623) baseStart_4599623 baseEnd_4599623 := by
    simpa [prefixWord, tailWord_4599623, baseEnd_4599623] using wordTrace_append hprefix tailTrace_4599623
  have hstable : (prefixWord ++ tailWord_4599623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599623).length < 2 ^ (prefixWord ++ tailWord_4599623).sum := by decide
  have hdescent : baseEnd_4599623 < baseStart_4599623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599644 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4599644 : Nat := 118140960795 + 4599644 * 2 ^ 59
def prefixEnd_4599644 : Nat := 4983230072969 + 3 ^ 40 * 4599644 * 2
def baseEnd_4599644 : Nat := 2361828211569107105396629

theorem tailTrace_4599644 : CollatzResearch.WordTrace tailWord_4599644 prefixEnd_4599644 2361828211569107105396629 := by
  unfold tailWord_4599644
  simp only [CollatzResearch.WordTrace]
  refine ⟨83881399474141409749474993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111841865965521879665966657 83881399474141409749474993)
  ·
    refine ⟨62911049605606057312106245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83881399474141409749474993 62911049605606057312106245)
    ·
      refine ⟨11795821801051135746019921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62911049605606057312106245 11795821801051135746019921)
      ·
        refine ⟨8846866350788351809514941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11795821801051135746019921 8846866350788351809514941)
        ·
          refine ⟨3317574881545631928568103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8846866350788351809514941 3317574881545631928568103)
          ·
            refine ⟨4976362322318447892852155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317574881545631928568103 4976362322318447892852155)
            ·
              refine ⟨7464543483477671839278233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976362322318447892852155 7464543483477671839278233)
              ·
                refine ⟨5598407612608253879458675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7464543483477671839278233 5598407612608253879458675)
                ·
                  refine ⟨8397611418912380819188013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598407612608253879458675 8397611418912380819188013)
                  ·
                    refine ⟨3149104282092142807195505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8397611418912380819188013 3149104282092142807195505)
                    ·
                      refine ⟨2361828211569107105396629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149104282092142807195505 2361828211569107105396629)
                      ·
                        rfl

theorem cell23_4599644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4599644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599644 prefixEnd_4599644 := by exact prefixLift 4599644
  have htrace : WordTrace (prefixWord ++ tailWord_4599644) baseStart_4599644 baseEnd_4599644 := by
    simpa [prefixWord, tailWord_4599644, baseEnd_4599644] using wordTrace_append hprefix tailTrace_4599644
  have hstable : (prefixWord ++ tailWord_4599644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599644).length < 2 ^ (prefixWord ++ tailWord_4599644).sum := by decide
  have hdescent : baseEnd_4599644 < baseStart_4599644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599679 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_4599679 : Nat := 118140960795 + 4599679 * 2 ^ 59
def prefixEnd_4599679 : Nat := 4983230072969 + 3 ^ 40 * 4599679 * 2
def baseEnd_4599679 : Nat := 2361846183392014468458967

theorem tailTrace_4599679 : CollatzResearch.WordTrace tailWord_4599679 prefixEnd_4599679 2361846183392014468458967 := by
  unfold tailWord_4599679
  simp only [CollatzResearch.WordTrace]
  refine ⟨167764075503156020476474091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111842717002104013650982727 167764075503156020476474091)
  ·
    refine ⟨251646113254734030714711137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167764075503156020476474091 251646113254734030714711137)
    ·
      refine ⟨188734584941050523036033353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251646113254734030714711137 188734584941050523036033353)
      ·
        refine ⟨141550938705787892277025015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188734584941050523036033353 141550938705787892277025015)
        ·
          refine ⟨212326408058681838415537523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141550938705787892277025015 212326408058681838415537523)
          ·
            refine ⟨318489612088022757623306285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212326408058681838415537523 318489612088022757623306285)
            ·
              refine ⟨119433604533008534108739857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318489612088022757623306285 119433604533008534108739857)
              ·
                refine ⟨89575203399756400581554893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119433604533008534108739857 89575203399756400581554893)
                ·
                  refine ⟨33590701274908650218083085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89575203399756400581554893 33590701274908650218083085)
                  ·
                    refine ⟨12596512978090743831781157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33590701274908650218083085 12596512978090743831781157)
                    ·
                      refine ⟨2361846183392014468458967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12596512978090743831781157 2361846183392014468458967)
                      ·
                        rfl

theorem cell23_4599679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_4599679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599679 prefixEnd_4599679 := by exact prefixLift 4599679
  have htrace : WordTrace (prefixWord ++ tailWord_4599679) baseStart_4599679 baseEnd_4599679 := by
    simpa [prefixWord, tailWord_4599679, baseEnd_4599679] using wordTrace_append hprefix tailTrace_4599679
  have hstable : (prefixWord ++ tailWord_4599679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599679).length < 2 ^ (prefixWord ++ tailWord_4599679).sum := by decide
  have hdescent : baseEnd_4599679 < baseStart_4599679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599696 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2]
def baseStart_4599696 : Nat := 118140960795 + 4599696 * 2 ^ 59
def prefixEnd_4599696 : Nat := 4983230072969 + 3 ^ 40 * 4599696 * 2
def baseEnd_4599696 : Nat := 2361854912563140901946389

theorem tailTrace_4599696 : CollatzResearch.WordTrace tailWord_4599696 prefixEnd_4599696 2361854912563140901946389 := by
  unfold tailWord_4599696
  simp only [CollatzResearch.WordTrace]
  refine ⟨83882347772047216189921471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111843130362729621586561961 83882347772047216189921471)
  ·
    refine ⟨125823521658070824284882207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83882347772047216189921471 125823521658070824284882207)
    ·
      refine ⟨188735282487106236427323311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125823521658070824284882207 188735282487106236427323311)
      ·
        refine ⟨283102923730659354640984967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188735282487106236427323311 283102923730659354640984967)
        ·
          refine ⟨424654385595989031961477451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283102923730659354640984967 424654385595989031961477451)
          ·
            refine ⟨636981578393983547942216177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424654385595989031961477451 636981578393983547942216177)
            ·
              refine ⟨477736183795487660956662133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636981578393983547942216177 477736183795487660956662133)
              ·
                refine ⟨44787767230826968214687075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477736183795487660956662133 44787767230826968214687075)
                ·
                  refine ⟨67181650846240452322030613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44787767230826968214687075 67181650846240452322030613)
                  ·
                    refine ⟨3149139883417521202595185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67181650846240452322030613 3149139883417521202595185)
                    ·
                      refine ⟨2361854912563140901946389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149139883417521202595185 2361854912563140901946389)
                      ·
                        rfl

theorem cell23_4599696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2].length) (baseStart_4599696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599696 prefixEnd_4599696 := by exact prefixLift 4599696
  have htrace : WordTrace (prefixWord ++ tailWord_4599696) baseStart_4599696 baseEnd_4599696 := by
    simpa [prefixWord, tailWord_4599696, baseEnd_4599696] using wordTrace_append hprefix tailTrace_4599696
  have hstable : (prefixWord ++ tailWord_4599696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599696).length < 2 ^ (prefixWord ++ tailWord_4599696).sum := by decide
  have hdescent : baseEnd_4599696 < baseStart_4599696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599710 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4599710 : Nat := 118140960795 + 4599710 * 2 ^ 59
def prefixEnd_4599710 : Nat := 4983230072969 + 3 ^ 40 * 4599710 * 2
def baseEnd_4599710 : Nat := 787287367097434615723775

theorem tailTrace_4599710 : CollatzResearch.WordTrace tailWord_4599710 prefixEnd_4599710 787287367097434615723775 := by
  unfold tailWord_4599710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970650770755464096356573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111843470777362475180568389 20970650770755464096356573)
  ·
    refine ⟨7863994039033299036133715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20970650770755464096356573 7863994039033299036133715)
    ·
      refine ⟨11795991058549948554200573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863994039033299036133715 11795991058549948554200573)
      ·
        refine ⟨4423496646956230707825215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11795991058549948554200573 4423496646956230707825215)
        ·
          refine ⟨6635244970434346061737823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423496646956230707825215 6635244970434346061737823)
          ·
            refine ⟨9952867455651519092606735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635244970434346061737823 9952867455651519092606735)
            ·
              refine ⟨14929301183477278638910103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9952867455651519092606735 14929301183477278638910103)
              ·
                refine ⟨22393951775215917958365155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14929301183477278638910103 22393951775215917958365155)
                ·
                  refine ⟨33590927662823876937547733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22393951775215917958365155 33590927662823876937547733)
                  ·
                    refine ⟨787287367097434615723775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33590927662823876937547733 787287367097434615723775)
                    ·
                      rfl

theorem cell23_4599710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4599710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599710 prefixEnd_4599710 := by exact prefixLift 4599710
  have htrace : WordTrace (prefixWord ++ tailWord_4599710) baseStart_4599710 baseEnd_4599710 := by
    simpa [prefixWord, tailWord_4599710, baseEnd_4599710] using wordTrace_append hprefix tailTrace_4599710
  have hstable : (prefixWord ++ tailWord_4599710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599710).length < 2 ^ (prefixWord ++ tailWord_4599710).sum := by decide
  have hdescent : baseEnd_4599710 < baseStart_4599710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599713 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4599713 : Nat := 118140960795 + 4599713 * 2 ^ 59
def prefixEnd_4599713 : Nat := 4983230072969 + 3 ^ 40 * 4599713 * 2
def baseEnd_4599713 : Nat := 2361863641734267335433811

theorem tailTrace_4599713 : CollatzResearch.WordTrace tailWord_4599713 prefixEnd_4599713 2361863641734267335433811 := by
  unfold tailWord_4599713
  simp only [CollatzResearch.WordTrace]
  refine ⟨167765315585032844283211793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111843543723355229522141195 167765315585032844283211793)
  ·
    refine ⟨125823986688774633212408845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167765315585032844283211793 125823986688774633212408845)
    ·
      refine ⟨47183995008290487454653317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125823986688774633212408845 47183995008290487454653317)
      ·
        refine ⟨8846999064054466397747497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47183995008290487454653317 8846999064054466397747497)
        ·
          refine ⟨6635249298040849798310623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8846999064054466397747497 6635249298040849798310623)
          ·
            refine ⟨9952873947061274697465935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635249298040849798310623 9952873947061274697465935)
            ·
              refine ⟨14929310920591912046198903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9952873947061274697465935 14929310920591912046198903)
              ·
                refine ⟨22393966380887868069298355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14929310920591912046198903 22393966380887868069298355)
                ·
                  refine ⟨33590949571331802103947533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22393966380887868069298355 33590949571331802103947533)
                  ·
                    refine ⟨12596606089249425788980325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33590949571331802103947533 12596606089249425788980325)
                    ·
                      refine ⟨2361863641734267335433811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12596606089249425788980325 2361863641734267335433811)
                      ·
                        rfl

theorem cell23_4599713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4599713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599713 prefixEnd_4599713 := by exact prefixLift 4599713
  have htrace : WordTrace (prefixWord ++ tailWord_4599713) baseStart_4599713 baseEnd_4599713 := by
    simpa [prefixWord, tailWord_4599713, baseEnd_4599713] using wordTrace_append hprefix tailTrace_4599713
  have hstable : (prefixWord ++ tailWord_4599713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599713).length < 2 ^ (prefixWord ++ tailWord_4599713).sum := by decide
  have hdescent : baseEnd_4599713 < baseStart_4599713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599739 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_4599739 : Nat := 118140960795 + 4599739 * 2 ^ 59
def prefixEnd_4599739 : Nat := 4983230072969 + 3 ^ 40 * 4599739 * 2
def baseEnd_4599739 : Nat := 2361876992231284233708691

theorem tailTrace_4599739 : CollatzResearch.WordTrace tailWord_4599739 prefixEnd_4599739 2361876992231284233708691 := by
  unfold tailWord_4599739
  simp only [CollatzResearch.WordTrace]
  refine ⟨167766263882938650723658271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111844175921959100482438847 167766263882938650723658271)
  ·
    refine ⟨251649395824407976085487407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167766263882938650723658271 251649395824407976085487407)
    ·
      refine ⟨377474093736611964128231111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251649395824407976085487407 377474093736611964128231111)
      ·
        refine ⟨566211140604917946192346667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377474093736611964128231111 566211140604917946192346667)
        ·
          refine ⟨849316710907376919288520001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566211140604917946192346667 849316710907376919288520001)
          ·
            refine ⟨636987533180532689466390001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849316710907376919288520001 636987533180532689466390001)
            ·
              refine ⟨477740649885399517099792501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636987533180532689466390001 477740649885399517099792501)
              ·
                refine ⟨44788185926756204728105547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477740649885399517099792501 44788185926756204728105547)
                ·
                  refine ⟨67182278890134307092158321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44788185926756204728105547 67182278890134307092158321)
                  ·
                    refine ⟨50386709167600730319118741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67182278890134307092158321 50386709167600730319118741)
                    ·
                      refine ⟨2361876992231284233708691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50386709167600730319118741 2361876992231284233708691)
                      ·
                        rfl

theorem cell23_4599739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_4599739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599739 prefixEnd_4599739 := by exact prefixLift 4599739
  have htrace : WordTrace (prefixWord ++ tailWord_4599739) baseStart_4599739 baseEnd_4599739 := by
    simpa [prefixWord, tailWord_4599739, baseEnd_4599739] using wordTrace_append hprefix tailTrace_4599739
  have hstable : (prefixWord ++ tailWord_4599739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599739).length < 2 ^ (prefixWord ++ tailWord_4599739).sum := by decide
  have hdescent : baseEnd_4599739 < baseStart_4599739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599749 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_4599749 : Nat := 118140960795 + 4599749 * 2 ^ 59
def prefixEnd_4599749 : Nat := 4983230072969 + 3 ^ 40 * 4599749 * 2
def baseEnd_4599749 : Nat := 787294042345943064861215

theorem tailTrace_4599749 : CollatzResearch.WordTrace tailWord_4599749 prefixEnd_4599749 787294042345943064861215 := by
  unfold tailWord_4599749
  simp only [CollatzResearch.WordTrace]
  refine ⟨167766628612902422431522301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111844419075268281621014867 167766628612902422431522301)
  ·
    refine ⟨62912485729838408411820863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167766628612902422431522301 62912485729838408411820863)
    ·
      refine ⟨94368728594757612617731295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62912485729838408411820863 94368728594757612617731295)
      ·
        refine ⟨141553092892136418926596943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94368728594757612617731295 141553092892136418926596943)
        ·
          refine ⟨212329639338204628389895415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141553092892136418926596943 212329639338204628389895415)
          ·
            refine ⟨318494459007306942584843123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212329639338204628389895415 318494459007306942584843123)
            ·
              refine ⟨477741688510960413877264685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318494459007306942584843123 477741688510960413877264685)
              ·
                refine ⟨179153133191610155203974257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477741688510960413877264685 179153133191610155203974257)
                ·
                  refine ⟨134364849893707616402980693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179153133191610155203974257 134364849893707616402980693)
                  ·
                    refine ⟨787294042345943064861215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134364849893707616402980693 787294042345943064861215)
                    ·
                      rfl

theorem cell23_4599749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_4599749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599749 prefixEnd_4599749 := by exact prefixLift 4599749
  have htrace : WordTrace (prefixWord ++ tailWord_4599749) baseStart_4599749 baseEnd_4599749 := by
    simpa [prefixWord, tailWord_4599749, baseEnd_4599749] using wordTrace_append hprefix tailTrace_4599749
  have hstable : (prefixWord ++ tailWord_4599749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599749).length < 2 ^ (prefixWord ++ tailWord_4599749).sum := by decide
  have hdescent : baseEnd_4599749 < baseStart_4599749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599790 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_4599790 : Nat := 118140960795 + 4599790 * 2 ^ 59
def prefixEnd_4599790 : Nat := 4983230072969 + 3 ^ 40 * 4599790 * 2
def baseEnd_4599790 : Nat := 2361903179744663534170957

theorem tailTrace_4599790 : CollatzResearch.WordTrace tailWord_4599790 prefixEnd_4599790 2361903179744663534170957 := by
  unfold tailWord_4599790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20971015500719235804220603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111845416003835924289176549 20971015500719235804220603)
  ·
    refine ⟨31456523251078853706330905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20971015500719235804220603 31456523251078853706330905)
    ·
      refine ⟨23592392438309140279748179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31456523251078853706330905 23592392438309140279748179)
      ·
        refine ⟨35388588657463710419622269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23592392438309140279748179 35388588657463710419622269)
        ·
          refine ⟨13270720746548891407358351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35388588657463710419622269 13270720746548891407358351)
          ·
            refine ⟨19906081119823337111037527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13270720746548891407358351 19906081119823337111037527)
            ·
              refine ⟨29859121679735005666556291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19906081119823337111037527 29859121679735005666556291)
              ·
                refine ⟨44788682519602508499834437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29859121679735005666556291 44788682519602508499834437)
                ·
                  refine ⟨8397877972425470343718957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44788682519602508499834437 8397877972425470343718957)
                  ·
                    refine ⟨3149204239659551378894609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8397877972425470343718957 3149204239659551378894609)
                    ·
                      refine ⟨2361903179744663534170957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149204239659551378894609 2361903179744663534170957)
                      ·
                        rfl

theorem cell23_4599790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_4599790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599790 prefixEnd_4599790 := by exact prefixLift 4599790
  have htrace : WordTrace (prefixWord ++ tailWord_4599790) baseStart_4599790 baseEnd_4599790 := by
    simpa [prefixWord, tailWord_4599790, baseEnd_4599790] using wordTrace_append hprefix tailTrace_4599790
  have hstable : (prefixWord ++ tailWord_4599790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599790).length < 2 ^ (prefixWord ++ tailWord_4599790).sum := by decide
  have hdescent : baseEnd_4599790 < baseStart_4599790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599816 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4599816 : Nat := 118140960795 + 4599816 * 2 ^ 59
def prefixEnd_4599816 : Nat := 4983230072969 + 3 ^ 40 * 4599816 * 2
def baseEnd_4599816 : Nat := 2361916530241680432445837

theorem tailTrace_4599816 : CollatzResearch.WordTrace tailWord_4599816 prefixEnd_4599816 2361916530241680432445837 := by
  unfold tailWord_4599816
  simp only [CollatzResearch.WordTrace]
  refine ⟨83884536151829846437105651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111846048202439795249474201 83884536151829846437105651)
  ·
    refine ⟨125826804227744769655658477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83884536151829846437105651 125826804227744769655658477)
    ·
      refine ⟨47185051585404288620871929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125826804227744769655658477 47185051585404288620871929)
      ·
        refine ⟨35388788689053216465653947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47185051585404288620871929 35388788689053216465653947)
        ·
          refine ⟨53083183033579824698480921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35388788689053216465653947 53083183033579824698480921)
          ·
            refine ⟨39812387275184868523860691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53083183033579824698480921 39812387275184868523860691)
            ·
              refine ⟨59718580912777302785791037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39812387275184868523860691 59718580912777302785791037)
              ·
                refine ⟨22394467842291488544671639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59718580912777302785791037 22394467842291488544671639)
                ·
                  refine ⟨33591701763437232817007459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22394467842291488544671639 33591701763437232817007459)
                  ·
                    refine ⟨50387552645155849225511189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33591701763437232817007459 50387552645155849225511189)
                    ·
                      refine ⟨2361916530241680432445837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50387552645155849225511189 2361916530241680432445837)
                      ·
                        rfl

theorem cell23_4599816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4599816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599816 prefixEnd_4599816 := by exact prefixLift 4599816
  have htrace : WordTrace (prefixWord ++ tailWord_4599816) baseStart_4599816 baseEnd_4599816 := by
    simpa [prefixWord, tailWord_4599816, baseEnd_4599816] using wordTrace_append hprefix tailTrace_4599816
  have hstable : (prefixWord ++ tailWord_4599816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599816).length < 2 ^ (prefixWord ++ tailWord_4599816).sum := by decide
  have hdescent : baseEnd_4599816 < baseStart_4599816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599820 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_4599820 : Nat := 118140960795 + 4599820 * 2 ^ 59
def prefixEnd_4599820 : Nat := 4983230072969 + 3 ^ 40 * 4599820 * 2
def baseEnd_4599820 : Nat := 2361918584164298416795819

theorem tailTrace_4599820 : CollatzResearch.WordTrace tailWord_4599820 prefixEnd_4599820 2361918584164298416795819 := by
  unfold tailWord_4599820
  simp only [CollatzResearch.WordTrace]
  refine ⟨83884609097822600778678457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111846145463763467704904609 83884609097822600778678457)
  ·
    refine ⟨62913456823366950584008843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83884609097822600778678457 62913456823366950584008843)
    ·
      refine ⟨94370185235050425876013265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62913456823366950584008843 94370185235050425876013265)
      ·
        refine ⟨70777638926287819407009949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94370185235050425876013265 70777638926287819407009949)
        ·
          refine ⟨26541614597357932277628731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70777638926287819407009949 26541614597357932277628731)
          ·
            refine ⟨39812421896036898416443097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26541614597357932277628731 39812421896036898416443097)
            ·
              refine ⟨29859316422027673812332323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39812421896036898416443097 29859316422027673812332323)
              ·
                refine ⟨44788974633041510718498485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29859316422027673812332323 44788974633041510718498485)
                ·
                  refine ⟨4198966371847641629859233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44788974633041510718498485 4198966371847641629859233)
                  ·
                    refine ⟨3149224778885731222394425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198966371847641629859233 3149224778885731222394425)
                    ·
                      refine ⟨2361918584164298416795819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149224778885731222394425 2361918584164298416795819)
                      ·
                        rfl

theorem cell23_4599820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_4599820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599820 prefixEnd_4599820 := by exact prefixLift 4599820
  have htrace : WordTrace (prefixWord ++ tailWord_4599820) baseStart_4599820 baseEnd_4599820 := by
    simpa [prefixWord, tailWord_4599820, baseEnd_4599820] using wordTrace_append hprefix tailTrace_4599820
  have hstable : (prefixWord ++ tailWord_4599820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599820).length < 2 ^ (prefixWord ++ tailWord_4599820).sum := by decide
  have hdescent : baseEnd_4599820 < baseStart_4599820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599837 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_4599837 : Nat := 118140960795 + 4599837 * 2 ^ 59
def prefixEnd_4599837 : Nat := 4983230072969 + 3 ^ 40 * 4599837 * 2
def baseEnd_4599837 : Nat := 2361927313335424850283241

theorem tailTrace_4599837 : CollatzResearch.WordTrace tailWord_4599837 prefixEnd_4599837 2361927313335424850283241 := by
  unfold tailWord_4599837
  simp only [CollatzResearch.WordTrace]
  refine ⟨167769838236583613460725765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111846558824389075640483843 167769838236583613460725765)
  ·
    refine ⟨31456844669359427523886081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167769838236583613460725765 31456844669359427523886081)
    ·
      refine ⟨23592633502019570642914561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31456844669359427523886081 23592633502019570642914561)
      ·
        refine ⟨17694475126514677982185921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23592633502019570642914561 17694475126514677982185921)
        ·
          refine ⟨13270856344886008486639441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17694475126514677982185921 13270856344886008486639441)
          ·
            refine ⟨9953142258664506364979581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13270856344886008486639441 9953142258664506364979581)
            ·
              refine ⟨3732428346999189886867343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9953142258664506364979581 3732428346999189886867343)
              ·
                refine ⟨5598642520498784830301015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732428346999189886867343 5598642520498784830301015)
                ·
                  refine ⟨8397963780748177245451523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598642520498784830301015 8397963780748177245451523)
                  ·
                    refine ⟨12596945671122265868177285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8397963780748177245451523 12596945671122265868177285)
                    ·
                      refine ⟨2361927313335424850283241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12596945671122265868177285 2361927313335424850283241)
                      ·
                        rfl

theorem cell23_4599837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_4599837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599837 prefixEnd_4599837 := by exact prefixLift 4599837
  have htrace : WordTrace (prefixWord ++ tailWord_4599837) baseStart_4599837 baseEnd_4599837 := by
    simpa [prefixWord, tailWord_4599837, baseEnd_4599837] using wordTrace_append hprefix tailTrace_4599837
  have hstable : (prefixWord ++ tailWord_4599837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599837).length < 2 ^ (prefixWord ++ tailWord_4599837).sum := by decide
  have hdescent : baseEnd_4599837 < baseStart_4599837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599848 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4599848 : Nat := 118140960795 + 4599848 * 2 ^ 59
def prefixEnd_4599848 : Nat := 4983230072969 + 3 ^ 40 * 4599848 * 2
def baseEnd_4599848 : Nat := 2361932961622624307245691

theorem tailTrace_4599848 : CollatzResearch.WordTrace tailWord_4599848 prefixEnd_4599848 2361932961622624307245691 := by
  unfold tailWord_4599848
  simp only [CollatzResearch.WordTrace]
  refine ⟨83885119719771881169688099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111846826293029174892917465 83885119719771881169688099)
  ·
    refine ⟨125827679579657821754532149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83885119719771881169688099 125827679579657821754532149)
    ·
      refine ⟨11796344960592920789487389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125827679579657821754532149 11796344960592920789487389)
      ·
        refine ⟨4423629360222345296057771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11796344960592920789487389 4423629360222345296057771)
        ·
          refine ⟨6635444040333517944086657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423629360222345296057771 6635444040333517944086657)
          ·
            refine ⟨4976583030250138458064993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6635444040333517944086657 4976583030250138458064993)
            ·
              refine ⟨3732437272687603843548745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4976583030250138458064993 3732437272687603843548745)
              ·
                refine ⟨2799327954515702882661559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732437272687603843548745 2799327954515702882661559)
                ·
                  refine ⟨4198991931773554323992339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799327954515702882661559 4198991931773554323992339)
                  ·
                    refine ⟨6298487897660331485988509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4198991931773554323992339 6298487897660331485988509)
                    ·
                      refine ⟨2361932961622624307245691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298487897660331485988509 2361932961622624307245691)
                      ·
                        rfl

theorem cell23_4599848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4599848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599848 prefixEnd_4599848 := by exact prefixLift 4599848
  have htrace : WordTrace (prefixWord ++ tailWord_4599848) baseStart_4599848 baseEnd_4599848 := by
    simpa [prefixWord, tailWord_4599848, baseEnd_4599848] using wordTrace_append hprefix tailTrace_4599848
  have hstable : (prefixWord ++ tailWord_4599848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599848).length < 2 ^ (prefixWord ++ tailWord_4599848).sum := by decide
  have hdescent : baseEnd_4599848 < baseStart_4599848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599856 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_4599856 : Nat := 118140960795 + 4599856 * 2 ^ 59
def prefixEnd_4599856 : Nat := 4983230072969 + 3 ^ 40 * 4599856 * 2
def baseEnd_4599856 : Nat := 787312356489286758648551

theorem tailTrace_4599856 : CollatzResearch.WordTrace tailWord_4599856 prefixEnd_4599856 787312356489286758648551 := by
  unfold tailWord_4599856
  simp only [CollatzResearch.WordTrace]
  refine ⟨83885265611757389852833711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111847020815676519803778281 83885265611757389852833711)
  ·
    refine ⟨125827898417636084779250567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83885265611757389852833711 125827898417636084779250567)
    ·
      refine ⟨188741847626454127168875851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125827898417636084779250567 188741847626454127168875851)
      ·
        refine ⟨283112771439681190753313777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188741847626454127168875851 283112771439681190753313777)
        ·
          refine ⟨212334578579760893064985333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283112771439681190753313777 212334578579760893064985333)
          ·
            refine ⟨19906366741852583724842375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 212334578579760893064985333 19906366741852583724842375)
            ·
              refine ⟨29859550112778875587263563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19906366741852583724842375 29859550112778875587263563)
              ·
                refine ⟨44789325169168313380895345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29859550112778875587263563 44789325169168313380895345)
                ·
                  refine ⟨33591993876876235035671509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44789325169168313380895345 33591993876876235035671509)
                  ·
                    refine ⟨787312356489286758648551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33591993876876235035671509 787312356489286758648551)
                    ·
                      rfl

theorem cell23_4599856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_4599856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599856 prefixEnd_4599856 := by exact prefixLift 4599856
  have htrace : WordTrace (prefixWord ++ tailWord_4599856) baseStart_4599856 baseEnd_4599856 := by
    simpa [prefixWord, tailWord_4599856, baseEnd_4599856] using wordTrace_append hprefix tailTrace_4599856
  have hstable : (prefixWord ++ tailWord_4599856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599856).length < 2 ^ (prefixWord ++ tailWord_4599856).sum := by decide
  have hdescent : baseEnd_4599856 < baseStart_4599856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599866 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_4599866 : Nat := 118140960795 + 4599866 * 2 ^ 59
def prefixEnd_4599866 : Nat := 4983230072969 + 3 ^ 40 * 4599866 * 2
def baseEnd_4599866 : Nat := 2361942204274405236820607

theorem tailTrace_4599866 : CollatzResearch.WordTrace tailWord_4599866 prefixEnd_4599866 2361942204274405236820607 := by
  unfold tailWord_4599866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41942723988369637853382863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111847263968985700942354301 41942723988369637853382863)
  ·
    refine ⟨62914085982554456780074295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41942723988369637853382863 62914085982554456780074295)
    ·
      refine ⟨94371128973831685170111443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62914085982554456780074295 94371128973831685170111443)
      ·
        refine ⟨141556693460747527755167165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94371128973831685170111443 141556693460747527755167165)
        ·
          refine ⟨53083760047780322908187687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141556693460747527755167165 53083760047780322908187687)
          ·
            refine ⟨79625640071670484362281531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53083760047780322908187687 79625640071670484362281531)
            ·
              refine ⟨119438460107505726543422297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79625640071670484362281531 119438460107505726543422297)
              ·
                refine ⟨89578845080629294907566723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119438460107505726543422297 89578845080629294907566723)
                ·
                  refine ⟨134368267620943942361350085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89578845080629294907566723 134368267620943942361350085)
                  ·
                    refine ⟨25194050178926989192753141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134368267620943942361350085 25194050178926989192753141)
                    ·
                      refine ⟨2361942204274405236820607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25194050178926989192753141 2361942204274405236820607)
                      ·
                        rfl

theorem cell23_4599866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_4599866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599866 prefixEnd_4599866 := by exact prefixLift 4599866
  have htrace : WordTrace (prefixWord ++ tailWord_4599866) baseStart_4599866 baseEnd_4599866 := by
    simpa [prefixWord, tailWord_4599866, baseEnd_4599866] using wordTrace_append hprefix tailTrace_4599866
  have hstable : (prefixWord ++ tailWord_4599866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599866).length < 2 ^ (prefixWord ++ tailWord_4599866).sum := by decide
  have hdescent : baseEnd_4599866 < baseStart_4599866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599927 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_4599927 : Nat := 118140960795 + 4599927 * 2 ^ 59
def prefixEnd_4599927 : Nat := 4983230072969 + 3 ^ 40 * 4599927 * 2
def baseEnd_4599927 : Nat := 2361973526594329498157827

theorem tailTrace_4599927 : CollatzResearch.WordTrace tailWord_4599927 prefixEnd_4599927 2361973526594329498157827 := by
  unfold tailWord_4599927
  simp only [CollatzResearch.WordTrace]
  refine ⟨167773120806257558831502035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111848747204171705887668023 167773120806257558831502035)
  ·
    refine ⟨251659681209386338247253053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167773120806257558831502035 251659681209386338247253053)
    ·
      refine ⟨94372380453519876842719895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251659681209386338247253053 94372380453519876842719895)
      ·
        refine ⟨141558570680279815264079843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94372380453519876842719895 141558570680279815264079843)
        ·
          refine ⟨212337856020419722896119765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141558570680279815264079843 212337856020419722896119765)
          ·
            refine ⟨4976668500478587255377807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 212337856020419722896119765 4976668500478587255377807)
            ·
              refine ⟨7465002750717880883066711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976668500478587255377807 7465002750717880883066711)
              ·
                refine ⟨11197504126076821324600067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7465002750717880883066711 11197504126076821324600067)
                ·
                  refine ⟨16796256189115231986900101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11197504126076821324600067 16796256189115231986900101)
                  ·
                    refine ⟨3149298035459105997543769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16796256189115231986900101 3149298035459105997543769)
                    ·
                      refine ⟨2361973526594329498157827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149298035459105997543769 2361973526594329498157827)
                      ·
                        rfl

theorem cell23_4599927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_4599927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599927 prefixEnd_4599927 := by exact prefixLift 4599927
  have htrace : WordTrace (prefixWord ++ tailWord_4599927) baseStart_4599927 baseEnd_4599927 := by
    simpa [prefixWord, tailWord_4599927, baseEnd_4599927] using wordTrace_append hprefix tailTrace_4599927
  have hstable : (prefixWord ++ tailWord_4599927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599927).length < 2 ^ (prefixWord ++ tailWord_4599927).sum := by decide
  have hdescent : baseEnd_4599927 < baseStart_4599927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599933 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 7]
def baseStart_4599933 : Nat := 118140960795 + 4599933 * 2 ^ 59
def prefixEnd_4599933 : Nat := 4983230072969 + 3 ^ 40 * 4599933 * 2
def baseEnd_4599933 : Nat := 262441845275361830520311

theorem tailTrace_4599933 : CollatzResearch.WordTrace tailWord_4599933 prefixEnd_4599933 262441845275361830520311 := by
  unfold tailWord_4599933
  simp only [CollatzResearch.WordTrace]
  refine ⟨167773339644235821856220453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111848893096157214570813635 167773339644235821856220453)
  ·
    refine ⟨31457501183294216598041335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167773339644235821856220453 31457501183294216598041335)
    ·
      refine ⟨47186251774941324897062003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31457501183294216598041335 47186251774941324897062003)
      ·
        refine ⟨70779377662411987345593005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47186251774941324897062003 70779377662411987345593005)
        ·
          refine ⟨26542266623404495254597377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70779377662411987345593005 26542266623404495254597377)
          ·
            refine ⟨19906699967553371440948033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26542266623404495254597377 19906699967553371440948033)
            ·
              refine ⟨14930024975665028580711025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19906699967553371440948033 14930024975665028580711025)
              ·
                refine ⟨11197518731748771435533269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14930024975665028580711025 11197518731748771435533269)
                ·
                  refine ⟨262441845275361830520311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11197518731748771435533269 262441845275361830520311)
                  ·
                    rfl

theorem cell23_4599933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_4599933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599933 prefixEnd_4599933 := by exact prefixLift 4599933
  have htrace : WordTrace (prefixWord ++ tailWord_4599933) baseStart_4599933 baseEnd_4599933 := by
    simpa [prefixWord, tailWord_4599933, baseEnd_4599933] using wordTrace_append hprefix tailTrace_4599933
  have hstable : (prefixWord ++ tailWord_4599933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599933).length < 2 ^ (prefixWord ++ tailWord_4599933).sum := by decide
  have hdescent : baseEnd_4599933 < baseStart_4599933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599943 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_4599943 : Nat := 118140960795 + 4599943 * 2 ^ 59
def prefixEnd_4599943 : Nat := 4983230072969 + 3 ^ 40 * 4599943 * 2
def baseEnd_4599943 : Nat := 2361981742284801435557753

theorem tailTrace_4599943 : CollatzResearch.WordTrace tailWord_4599943 prefixEnd_4599943 2361981742284801435557753 := by
  unfold tailWord_4599943
  simp only [CollatzResearch.WordTrace]
  refine ⟨167773704374199593564084483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111849136249466395709389655 167773704374199593564084483)
  ·
    refine ⟨251660556561299390346126725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167773704374199593564084483 251660556561299390346126725)
    ·
      refine ⟨47186354355243635689898761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251660556561299390346126725 47186354355243635689898761)
      ·
        refine ⟨35389765766432726767424071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47186354355243635689898761 35389765766432726767424071)
        ·
          refine ⟨53084648649649090151136107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35389765766432726767424071 53084648649649090151136107)
          ·
            refine ⟨79626972974473635226704161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53084648649649090151136107 79626972974473635226704161)
            ·
              refine ⟨59720229730855226420028121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79626972974473635226704161 59720229730855226420028121)
              ·
                refine ⟨44790172298141419815021091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59720229730855226420028121 44790172298141419815021091)
                ·
                  refine ⟨67185258447212129722531637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44790172298141419815021091 67185258447212129722531637)
                  ·
                    refine ⟨6298617979426137161487341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67185258447212129722531637 6298617979426137161487341)
                    ·
                      refine ⟨2361981742284801435557753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298617979426137161487341 2361981742284801435557753)
                      ·
                        rfl

theorem cell23_4599943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_4599943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599943 prefixEnd_4599943 := by exact prefixLift 4599943
  have htrace : WordTrace (prefixWord ++ tailWord_4599943) baseStart_4599943 baseEnd_4599943 := by
    simpa [prefixWord, tailWord_4599943, baseEnd_4599943] using wordTrace_append hprefix tailTrace_4599943
  have hstable : (prefixWord ++ tailWord_4599943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599943).length < 2 ^ (prefixWord ++ tailWord_4599943).sum := by decide
  have hdescent : baseEnd_4599943 < baseStart_4599943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599973 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_4599973 : Nat := 118140960795 + 4599973 * 2 ^ 59
def prefixEnd_4599973 : Nat := 4983230072969 + 3 ^ 40 * 4599973 * 2
def baseEnd_4599973 : Nat := 2361997146704436318182615

theorem tailTrace_4599973 : CollatzResearch.WordTrace tailWord_4599973 prefixEnd_4599973 2361997146704436318182615 := by
  unfold tailWord_4599973
  simp only [CollatzResearch.WordTrace]
  refine ⟨167774798564090908687676573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111849865709393939125117715 167774798564090908687676573)
  ·
    refine ⟨62915549461534090757878715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167774798564090908687676573 62915549461534090757878715)
    ·
      refine ⟨94373324192301136136818073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62915549461534090757878715 94373324192301136136818073)
      ·
        refine ⟨70779993144225852102613555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94373324192301136136818073 70779993144225852102613555)
        ·
          refine ⟨106169989716338778153920333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70779993144225852102613555 106169989716338778153920333)
          ·
            refine ⟨39813746143627041807720125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106169989716338778153920333 39813746143627041807720125)
            ·
              refine ⟨14930154803860140677895047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39813746143627041807720125 14930154803860140677895047)
              ·
                refine ⟨22395232205790211016842571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14930154803860140677895047 22395232205790211016842571)
                ·
                  refine ⟨33592848308685316525263857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22395232205790211016842571 33592848308685316525263857)
                  ·
                    refine ⟨25194636231513987393947893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33592848308685316525263857 25194636231513987393947893)
                    ·
                      refine ⟨2361997146704436318182615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25194636231513987393947893 2361997146704436318182615)
                      ·
                        rfl

theorem cell23_4599973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_4599973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599973 prefixEnd_4599973 := by exact prefixLift 4599973
  have htrace : WordTrace (prefixWord ++ tailWord_4599973) baseStart_4599973 baseEnd_4599973 := by
    simpa [prefixWord, tailWord_4599973, baseEnd_4599973] using wordTrace_append hprefix tailTrace_4599973
  have hstable : (prefixWord ++ tailWord_4599973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599973).length < 2 ^ (prefixWord ++ tailWord_4599973).sum := by decide
  have hdescent : baseEnd_4599973 < baseStart_4599973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4599983 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_4599983 : Nat := 118140960795 + 4599983 * 2 ^ 59
def prefixEnd_4599983 : Nat := 4983230072969 + 3 ^ 40 * 4599983 * 2
def baseEnd_4599983 : Nat := 2362002281510981279057569

theorem tailTrace_4599983 : CollatzResearch.WordTrace tailWord_4599983 prefixEnd_4599983 2362002281510981279057569 := by
  unfold tailWord_4599983
  simp only [CollatzResearch.WordTrace]
  refine ⟨167775163294054680395540603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111850108862703120263693735 167775163294054680395540603)
  ·
    refine ⟨251662744941082020593310905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167775163294054680395540603 251662744941082020593310905)
    ·
      refine ⟨188747058705811515444983179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251662744941082020593310905 188747058705811515444983179)
      ·
        refine ⟨283120588058717273167474769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188747058705811515444983179 283120588058717273167474769)
        ·
          refine ⟨212340441044037954875606077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283120588058717273167474769 212340441044037954875606077)
          ·
            refine ⟨79627665391514233078352279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212340441044037954875606077 79627665391514233078352279)
            ·
              refine ⟨119441498087271349617528419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79627665391514233078352279 119441498087271349617528419)
              ·
                refine ⟨179162247130907024426292629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119441498087271349617528419 179162247130907024426292629)
                ·
                  refine ⟨8398230334261266769982467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179162247130907024426292629 8398230334261266769982467)
                  ·
                    refine ⟨12597345501391900154973701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8398230334261266769982467 12597345501391900154973701)
                    ·
                      refine ⟨2362002281510981279057569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12597345501391900154973701 2362002281510981279057569)
                      ·
                        rfl

theorem cell23_4599983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_4599983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4599983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4599983 prefixEnd_4599983 := by exact prefixLift 4599983
  have htrace : WordTrace (prefixWord ++ tailWord_4599983) baseStart_4599983 baseEnd_4599983 := by
    simpa [prefixWord, tailWord_4599983, baseEnd_4599983] using wordTrace_append hprefix tailTrace_4599983
  have hstable : (prefixWord ++ tailWord_4599983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4599983).length < 2 ^ (prefixWord ++ tailWord_4599983).sum := by decide
  have hdescent : baseEnd_4599983 < baseStart_4599983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4599983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600000 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_4600000 : Nat := 118140960795 + 4600000 * 2 ^ 59
def prefixEnd_4600000 : Nat := 4983230072969 + 3 ^ 40 * 4600000 * 2
def baseEnd_4600000 : Nat := 2362011010682107712544991

theorem tailTrace_4600000 : CollatzResearch.WordTrace tailWord_4600000 prefixEnd_4600000 2362011010682107712544991 := by
  unfold tailWord_4600000
  simp only [CollatzResearch.WordTrace]
  refine ⟨83887891667496546149454727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111850522223328728199272969 83887891667496546149454727)
  ·
    refine ⟨125831837501244819224182091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83887891667496546149454727 125831837501244819224182091)
    ·
      refine ⟨188747756251867228836273137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125831837501244819224182091 188747756251867228836273137)
      ·
        refine ⟨141560817188900421627204853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188747756251867228836273137 141560817188900421627204853)
        ·
          refine ⟨13271326611459414527550455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141560817188900421627204853 13271326611459414527550455)
          ·
            refine ⟨19906989917189121791325683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13271326611459414527550455 19906989917189121791325683)
            ·
              refine ⟨29860484875783682686988525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19906989917189121791325683 29860484875783682686988525)
              ·
                refine ⟨11197681828418881007620697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29860484875783682686988525 11197681828418881007620697)
                ·
                  refine ⟨8398261371314160755715523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11197681828418881007620697 8398261371314160755715523)
                  ·
                    refine ⟨12597392056971241133573285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8398261371314160755715523 12597392056971241133573285)
                    ·
                      refine ⟨2362011010682107712544991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12597392056971241133573285 2362011010682107712544991)
                      ·
                        rfl

theorem cell23_4600000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_4600000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600000 prefixEnd_4600000 := by exact prefixLift 4600000
  have htrace : WordTrace (prefixWord ++ tailWord_4600000) baseStart_4600000 baseEnd_4600000 := by
    simpa [prefixWord, tailWord_4600000, baseEnd_4600000] using wordTrace_append hprefix tailTrace_4600000
  have hstable : (prefixWord ++ tailWord_4600000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600000).length < 2 ^ (prefixWord ++ tailWord_4600000).sum := by decide
  have hdescent : baseEnd_4600000 < baseStart_4600000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600003 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3]
def baseStart_4600003 : Nat := 118140960795 + 4600003 * 2 ^ 59
def prefixEnd_4600003 : Nat := 4983230072969 + 3 ^ 40 * 4600003 * 2
def baseEnd_4600003 : Nat := 2362012551124071200807477

theorem tailTrace_4600003 : CollatzResearch.WordTrace tailWord_4600003 prefixEnd_4600003 2362012551124071200807477 := by
  unfold tailWord_4600003
  simp only [CollatzResearch.WordTrace]
  refine ⟨167775892753982223811268663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111850595169321482540845775 167775892753982223811268663)
  ·
    refine ⟨251663839130973335716902995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167775892753982223811268663 251663839130973335716902995)
    ·
      refine ⟨377495758696460003575354493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251663839130973335716902995 377495758696460003575354493)
      ·
        refine ⟨141560909511172501340757935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377495758696460003575354493 141560909511172501340757935)
        ·
          refine ⟨212341364266758752011136903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141560909511172501340757935 212341364266758752011136903)
          ·
            refine ⟨318512046400138128016705355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212341364266758752011136903 318512046400138128016705355)
            ·
              refine ⟨477768069600207192025058033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318512046400138128016705355 477768069600207192025058033)
              ·
                refine ⟨358326052200155394018793525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477768069600207192025058033 358326052200155394018793525)
                ·
                  refine ⟨33593067393764568189261893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358326052200155394018793525 33593067393764568189261893)
                  ·
                    refine ⟨6298700136330856535486605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33593067393764568189261893 6298700136330856535486605)
                    ·
                      refine ⟨2362012551124071200807477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298700136330856535486605 2362012551124071200807477)
                      ·
                        rfl

theorem cell23_4600003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_4600003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600003 prefixEnd_4600003 := by exact prefixLift 4600003
  have htrace : WordTrace (prefixWord ++ tailWord_4600003) baseStart_4600003 baseEnd_4600003 := by
    simpa [prefixWord, tailWord_4600003, baseEnd_4600003] using wordTrace_append hprefix tailTrace_4600003
  have hstable : (prefixWord ++ tailWord_4600003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600003).length < 2 ^ (prefixWord ++ tailWord_4600003).sum := by decide
  have hdescent : baseEnd_4600003 < baseStart_4600003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600040 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 6]
def baseStart_4600040 : Nat := 118140960795 + 4600040 * 2 ^ 59
def prefixEnd_4600040 : Nat := 4983230072969 + 3 ^ 40 * 4600040 * 2
def baseEnd_4600040 : Nat := 262447949989809728449423

theorem tailTrace_4600040 : CollatzResearch.WordTrace tailWord_4600040 prefixEnd_4600040 262447949989809728449423 := by
  unfold tailWord_4600040
  simp only [CollatzResearch.WordTrace]
  refine ⟨83888621127424089565182787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111851494836565452753577049 83888621127424089565182787)
  ·
    refine ⟨125832931691136134347774181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83888621127424089565182787 125832931691136134347774181)
    ·
      refine ⟨23593674692088025190207659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125832931691136134347774181 23593674692088025190207659)
      ·
        refine ⟨35390512038132037785311489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23593674692088025190207659 35390512038132037785311489)
        ·
          refine ⟨26542884028599028338983617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35390512038132037785311489 26542884028599028338983617)
          ·
            refine ⟨19907163021449271254237713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26542884028599028338983617 19907163021449271254237713)
            ·
              refine ⟨14930372266086953440678285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19907163021449271254237713 14930372266086953440678285)
              ·
                refine ⟨5598889599782607540254357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14930372266086953440678285 5598889599782607540254357)
                ·
                  refine ⟨262447949989809728449423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5598889599782607540254357 262447949989809728449423)
                  ·
                    rfl

theorem cell23_4600040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_4600040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600040 prefixEnd_4600040 := by exact prefixLift 4600040
  have htrace : WordTrace (prefixWord ++ tailWord_4600040) baseStart_4600040 baseEnd_4600040 := by
    simpa [prefixWord, tailWord_4600040, baseEnd_4600040] using wordTrace_append hprefix tailTrace_4600040
  have hstable : (prefixWord ++ tailWord_4600040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600040).length < 2 ^ (prefixWord ++ tailWord_4600040).sum := by decide
  have hdescent : baseEnd_4600040 < baseStart_4600040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600083 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 3, 6]
def baseStart_4600083 : Nat := 118140960795 + 4600083 * 2 ^ 59
def prefixEnd_4600083 : Nat := 4983230072969 + 3 ^ 40 * 4600083 * 2
def baseEnd_4600083 : Nat := 787351209858810295935703

theorem tailTrace_4600083 : CollatzResearch.WordTrace tailWord_4600083 prefixEnd_4600083 787351209858810295935703 := by
  unfold tailWord_4600083
  simp only [CollatzResearch.WordTrace]
  refine ⟨167778810593692397474180903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111852540395794931649453935 167778810593692397474180903)
  ·
    refine ⟨251668215890538596211271355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167778810593692397474180903 251668215890538596211271355)
    ·
      refine ⟨377502323835807894316907033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251668215890538596211271355 377502323835807894316907033)
      ·
        refine ⟨283126742876855920737680275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377502323835807894316907033 283126742876855920737680275)
        ·
          refine ⟨424690114315283881106520413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283126742876855920737680275 424690114315283881106520413)
          ·
            refine ⟨159258792868231455414945155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424690114315283881106520413 159258792868231455414945155)
            ·
              refine ⟨238888189302347183122417733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159258792868231455414945155 238888189302347183122417733)
              ·
                refine ⟨44791535494190096835453325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238888189302347183122417733 44791535494190096835453325)
                ·
                  refine ⟨16796825810321286313294997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44791535494190096835453325 16796825810321286313294997)
                  ·
                    refine ⟨787351209858810295935703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16796825810321286313294997 787351209858810295935703)
                    ·
                      rfl

theorem cell23_4600083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_4600083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600083 prefixEnd_4600083 := by exact prefixLift 4600083
  have htrace : WordTrace (prefixWord ++ tailWord_4600083) baseStart_4600083 baseEnd_4600083 := by
    simpa [prefixWord, tailWord_4600083, baseEnd_4600083] using wordTrace_append hprefix tailTrace_4600083
  have hstable : (prefixWord ++ tailWord_4600083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600083).length < 2 ^ (prefixWord ++ tailWord_4600083).sum := by decide
  have hdescent : baseEnd_4600083 < baseStart_4600083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600104 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4600104 : Nat := 118140960795 + 4600104 * 2 ^ 59
def prefixEnd_4600104 : Nat := 4983230072969 + 3 ^ 40 * 4600104 * 2
def baseEnd_4600104 : Nat := 787354804223391768548171

theorem tailTrace_4600104 : CollatzResearch.WordTrace tailWord_4600104 prefixEnd_4600104 787354804223391768548171 := by
  unfold tailWord_4600104
  simp only [CollatzResearch.WordTrace]
  refine ⟨83889788263308159030347683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111853051017744212040463577 83889788263308159030347683)
  ·
    refine ⟨125834682394962238545521525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83889788263308159030347683 125834682394962238545521525)
    ·
      refine ⟨11797001474527709863642643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125834682394962238545521525 11797001474527709863642643)
      ·
        refine ⟨17695502211791564795463965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11797001474527709863642643 17695502211791564795463965)
        ·
          refine ⟨6635813329421836798298987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17695502211791564795463965 6635813329421836798298987)
          ·
            refine ⟨9953719994132755197448481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635813329421836798298987 9953719994132755197448481)
            ·
              refine ⟨7465289995599566398086361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9953719994132755197448481 7465289995599566398086361)
              ·
                refine ⟨5598967496699674798564771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7465289995599566398086361 5598967496699674798564771)
                ·
                  refine ⟨8398451245049512197847157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598967496699674798564771 8398451245049512197847157)
                  ·
                    refine ⟨787354804223391768548171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8398451245049512197847157 787354804223391768548171)
                    ·
                      rfl

theorem cell23_4600104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4600104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600104 prefixEnd_4600104 := by exact prefixLift 4600104
  have htrace : WordTrace (prefixWord ++ tailWord_4600104) baseStart_4600104 baseEnd_4600104 := by
    simpa [prefixWord, tailWord_4600104, baseEnd_4600104] using wordTrace_append hprefix tailTrace_4600104
  have hstable : (prefixWord ++ tailWord_4600104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600104).length < 2 ^ (prefixWord ++ tailWord_4600104).sum := by decide
  have hdescent : baseEnd_4600104 < baseStart_4600104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600120 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_4600120 : Nat := 118140960795 + 4600120 * 2 ^ 59
def prefixEnd_4600120 : Nat := 4983230072969 + 3 ^ 40 * 4600120 * 2
def baseEnd_4600120 : Nat := 2362072628360647243044439

theorem tailTrace_4600120 : CollatzResearch.WordTrace tailWord_4600120 prefixEnd_4600120 2362072628360647243044439 := by
  unfold tailWord_4600120
  simp only [CollatzResearch.WordTrace]
  refine ⟨83890080047279176396638907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111853440063038901862185209 83890080047279176396638907)
  ·
    refine ⟨125835120070918764594958361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83890080047279176396638907 125835120070918764594958361)
    ·
      refine ⟨94376340053189073446218771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125835120070918764594958361 94376340053189073446218771)
      ·
        refine ⟨141564510079783610169328157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94376340053189073446218771 141564510079783610169328157)
        ·
          refine ⟨53086691279918853813498059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141564510079783610169328157 53086691279918853813498059)
          ·
            refine ⟨79630036919878280720247089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53086691279918853813498059 79630036919878280720247089)
            ·
              refine ⟨59722527689908710540185317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79630036919878280720247089 59722527689908710540185317)
              ·
                refine ⟨11197973941857883226284747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59722527689908710540185317 11197973941857883226284747)
                ·
                  refine ⟨16796960912786824839427121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11197973941857883226284747 16796960912786824839427121)
                  ·
                    refine ⟨12597720684590118629570341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16796960912786824839427121 12597720684590118629570341)
                    ·
                      refine ⟨2362072628360647243044439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12597720684590118629570341 2362072628360647243044439)
                      ·
                        rfl

theorem cell23_4600120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_4600120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600120 prefixEnd_4600120 := by exact prefixLift 4600120
  have htrace : WordTrace (prefixWord ++ tailWord_4600120) baseStart_4600120 baseEnd_4600120 := by
    simpa [prefixWord, tailWord_4600120, baseEnd_4600120] using wordTrace_append hprefix tailTrace_4600120
  have hstable : (prefixWord ++ tailWord_4600120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600120).length < 2 ^ (prefixWord ++ tailWord_4600120).sum := by decide
  have hdescent : baseEnd_4600120 < baseStart_4600120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600127 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_4600127 : Nat := 118140960795 + 4600127 * 2 ^ 59
def prefixEnd_4600127 : Nat := 4983230072969 + 3 ^ 40 * 4600127 * 2
def baseEnd_4600127 : Nat := 2362076222725228715656907

theorem tailTrace_4600127 : CollatzResearch.WordTrace tailWord_4600127 prefixEnd_4600127 2362076222725228715656907 := by
  unfold tailWord_4600127
  simp only [CollatzResearch.WordTrace]
  refine ⟨167780415405532992988782635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111853610270355328659188423 167780415405532992988782635)
  ·
    refine ⟨251670623108299489483173953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167780415405532992988782635 251670623108299489483173953)
    ·
      refine ⟨188752967331224617112380465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251670623108299489483173953 188752967331224617112380465)
      ·
        refine ⟨141564725498418462834285349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188752967331224617112380465 141564725498418462834285349)
        ·
          refine ⟨26543386030953461781428503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141564725498418462834285349 26543386030953461781428503)
          ·
            refine ⟨39815079046430192672142755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26543386030953461781428503 39815079046430192672142755)
            ·
              refine ⟨59722618569645289008214133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39815079046430192672142755 59722618569645289008214133)
              ·
                refine ⟨5598995490904245844520075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59722618569645289008214133 5598995490904245844520075)
                ·
                  refine ⟨8398493236356368766780113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598995490904245844520075 8398493236356368766780113)
                  ·
                    refine ⟨6298869927267276575085085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8398493236356368766780113 6298869927267276575085085)
                    ·
                      refine ⟨2362076222725228715656907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6298869927267276575085085 2362076222725228715656907)
                      ·
                        rfl

theorem cell23_4600127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_4600127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600127 prefixEnd_4600127 := by exact prefixLift 4600127
  have htrace : WordTrace (prefixWord ++ tailWord_4600127) baseStart_4600127 baseEnd_4600127 := by
    simpa [prefixWord, tailWord_4600127, baseEnd_4600127] using wordTrace_append hprefix tailTrace_4600127
  have hstable : (prefixWord ++ tailWord_4600127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600127).length < 2 ^ (prefixWord ++ tailWord_4600127).sum := by decide
  have hdescent : baseEnd_4600127 < baseStart_4600127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600197 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_4600197 : Nat := 118140960795 + 4600197 * 2 ^ 59
def prefixEnd_4600197 : Nat := 4983230072969 + 3 ^ 40 * 4600197 * 2
def baseEnd_4600197 : Nat := 2362112166371043441781585

theorem tailTrace_4600197 : CollatzResearch.WordTrace tailWord_4600197 prefixEnd_4600197 2362112166371043441781585 := by
  unfold tailWord_4600197
  simp only [CollatzResearch.WordTrace]
  refine ⟨167782968515279394943830845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111855312343519596629220563 167782968515279394943830845)
  ·
    refine ⟨62918613193229773103936567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167782968515279394943830845 62918613193229773103936567)
    ·
      refine ⟨94377919789844659655904851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62918613193229773103936567 94377919789844659655904851)
      ·
        refine ⟨141566879684766989483857277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94377919789844659655904851 141566879684766989483857277)
        ·
          refine ⟨53087579881787621056446479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141566879684766989483857277 53087579881787621056446479)
          ·
            refine ⟨79631369822681431584669719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53087579881787621056446479 79631369822681431584669719)
            ·
              refine ⟨119447054734022147377004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79631369822681431584669719 119447054734022147377004579)
              ·
                refine ⟨179170582101033221065506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119447054734022147377004579 179170582101033221065506869)
                ·
                  refine ⟨16797242071971864474891269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179170582101033221065506869 16797242071971864474891269)
                  ·
                    refine ⟨3149482888494724589042113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16797242071971864474891269 3149482888494724589042113)
                    ·
                      refine ⟨2362112166371043441781585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149482888494724589042113 2362112166371043441781585)
                      ·
                        rfl

theorem cell23_4600197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_4600197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600197 prefixEnd_4600197 := by exact prefixLift 4600197
  have htrace : WordTrace (prefixWord ++ tailWord_4600197) baseStart_4600197 baseEnd_4600197 := by
    simpa [prefixWord, tailWord_4600197, baseEnd_4600197] using wordTrace_append hprefix tailTrace_4600197
  have hstable : (prefixWord ++ tailWord_4600197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600197).length < 2 ^ (prefixWord ++ tailWord_4600197).sum := by decide
  have hdescent : baseEnd_4600197 < baseStart_4600197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600247 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_4600247 : Nat := 118140960795 + 4600247 * 2 ^ 59
def prefixEnd_4600247 : Nat := 4983230072969 + 3 ^ 40 * 4600247 * 2
def baseEnd_4600247 : Nat := 2362137840403768246156355

theorem tailTrace_4600247 : CollatzResearch.WordTrace tailWord_4600247 prefixEnd_4600247 2362137840403768246156355 := by
  unfold tailWord_4600247
  simp only [CollatzResearch.WordTrace]
  refine ⟨167784792165098253483150995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111856528110065502322100663 167784792165098253483150995)
  ·
    refine ⟨251677188247647380224726493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167784792165098253483150995 251677188247647380224726493)
    ·
      refine ⟨94378945592867767584272435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251677188247647380224726493 94378945592867767584272435)
      ·
        refine ⟨141568418389301651376408653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94378945592867767584272435 141568418389301651376408653)
        ·
          refine ⟨53088156895988119266153245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141568418389301651376408653 53088156895988119266153245)
          ·
            refine ⟨19908058835995544724807467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53088156895988119266153245 19908058835995544724807467)
            ·
              refine ⟨29862088253993317087211201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19908058835995544724807467 29862088253993317087211201)
              ·
                refine ⟨22396566190494987815408401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29862088253993317087211201 22396566190494987815408401)
                ·
                  refine ⟨16797424642871240861556301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22396566190494987815408401 16797424642871240861556301)
                  ·
                    refine ⟨6299034241076715323083613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16797424642871240861556301 6299034241076715323083613)
                    ·
                      refine ⟨2362137840403768246156355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6299034241076715323083613 2362137840403768246156355)
                      ·
                        rfl

theorem cell23_4600247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_4600247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600247 prefixEnd_4600247 := by exact prefixLift 4600247
  have htrace : WordTrace (prefixWord ++ tailWord_4600247) baseStart_4600247 baseEnd_4600247 := by
    simpa [prefixWord, tailWord_4600247, baseEnd_4600247] using wordTrace_append hprefix tailTrace_4600247
  have hstable : (prefixWord ++ tailWord_4600247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600247).length < 2 ^ (prefixWord ++ tailWord_4600247).sum := by decide
  have hdescent : baseEnd_4600247 < baseStart_4600247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600254 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_4600254 : Nat := 118140960795 + 4600254 * 2 ^ 59
def prefixEnd_4600254 : Nat := 4983230072969 + 3 ^ 40 * 4600254 * 2
def baseEnd_4600254 : Nat := 262460159418705524307647

theorem tailTrace_4600254 : CollatzResearch.WordTrace tailWord_4600254 prefixEnd_4600254 262460159418705524307647 := by
  unfold tailWord_4600254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20973130934509111709831977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111856698317381929119103877 20973130934509111709831977)
  ·
    refine ⟨15729848200881833782373983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20973130934509111709831977 15729848200881833782373983)
    ·
      refine ⟨23594772301322750673560975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15729848200881833782373983 23594772301322750673560975)
      ·
        refine ⟨35392158451984126010341463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23594772301322750673560975 35392158451984126010341463)
        ·
          refine ⟨53088237677976189015512195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35392158451984126010341463 53088237677976189015512195)
          ·
            refine ⟨79632356516964283523268293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53088237677976189015512195 79632356516964283523268293)
            ·
              refine ⟨14931066846930803160612805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79632356516964283523268293 14931066846930803160612805)
              ·
                refine ⟨2799575033799525592614901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14931066846930803160612805 2799575033799525592614901)
                ·
                  refine ⟨262460159418705524307647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799575033799525592614901 262460159418705524307647)
                  ·
                    rfl

theorem cell23_4600254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_4600254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600254 prefixEnd_4600254 := by exact prefixLift 4600254
  have htrace : WordTrace (prefixWord ++ tailWord_4600254) baseStart_4600254 baseEnd_4600254 := by
    simpa [prefixWord, tailWord_4600254, baseEnd_4600254] using wordTrace_append hprefix tailTrace_4600254
  have hstable : (prefixWord ++ tailWord_4600254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600254).length < 2 ^ (prefixWord ++ tailWord_4600254).sum := by decide
  have hdescent : baseEnd_4600254 < baseStart_4600254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600280 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_4600280 : Nat := 118140960795 + 4600280 * 2 ^ 59
def prefixEnd_4600280 : Nat := 4983230072969 + 3 ^ 40 * 4600280 * 2
def baseEnd_4600280 : Nat := 787384928421788872347901

theorem tailTrace_4600280 : CollatzResearch.WordTrace tailWord_4600280 prefixEnd_4600280 787384928421788872347901 := by
  unfold tailWord_4600280
  simp only [CollatzResearch.WordTrace]
  refine ⟨83892997886989350059551147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111857330515985800079401529 83892997886989350059551147)
  ·
    refine ⟨125839496830484025089326721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83892997886989350059551147 125839496830484025089326721)
    ·
      refine ⟨94379622622863018816995041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125839496830484025089326721 94379622622863018816995041)
      ·
        refine ⟨70784716967147264112746281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94379622622863018816995041 70784716967147264112746281)
        ·
          refine ⟨53088537725360448084559711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70784716967147264112746281 53088537725360448084559711)
          ·
            refine ⟨79632806588040672126839567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53088537725360448084559711 79632806588040672126839567)
            ·
              refine ⟨119449209882061008190259351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79632806588040672126839567 119449209882061008190259351)
              ·
                refine ⟨179173814823091512285389027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119449209882061008190259351 179173814823091512285389027)
                ·
                  refine ⟨268760722234637268428083541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179173814823091512285389027 268760722234637268428083541)
                  ·
                    refine ⟨787384928421788872347901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 268760722234637268428083541 787384928421788872347901)
                    ·
                      rfl

theorem cell23_4600280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_4600280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600280 prefixEnd_4600280 := by exact prefixLift 4600280
  have htrace : WordTrace (prefixWord ++ tailWord_4600280) baseStart_4600280 baseEnd_4600280 := by
    simpa [prefixWord, tailWord_4600280, baseEnd_4600280] using wordTrace_append hprefix tailTrace_4600280
  have hstable : (prefixWord ++ tailWord_4600280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600280).length < 2 ^ (prefixWord ++ tailWord_4600280).sum := by decide
  have hdescent : baseEnd_4600280 < baseStart_4600280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600287 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_4600287 : Nat := 118140960795 + 4600287 * 2 ^ 59
def prefixEnd_4600287 : Nat := 4983230072969 + 3 ^ 40 * 4600287 * 2
def baseEnd_4600287 : Nat := 2362158379629948089656171

theorem tailTrace_4600287 : CollatzResearch.WordTrace tailWord_4600287 prefixEnd_4600287 2362158379629948089656171 := by
  unfold tailWord_4600287
  simp only [CollatzResearch.WordTrace]
  refine ⟨167786251084953340314607115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111857500723302226876404743 167786251084953340314607115)
  ·
    refine ⟨251679376627430010471910673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167786251084953340314607115 251679376627430010471910673)
    ·
      refine ⟨188759532470572507853933005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251679376627430010471910673 188759532470572507853933005)
      ·
        refine ⟨70784824676464690445224877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188759532470572507853933005 70784824676464690445224877)
        ·
          refine ⟨26544309253674258916959329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70784824676464690445224877 26544309253674258916959329)
          ·
            refine ⟨19908231940255694187719497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26544309253674258916959329 19908231940255694187719497)
            ·
              refine ⟨14931173955191770640789623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19908231940255694187719497 14931173955191770640789623)
              ·
                refine ⟨22396760932787655961184435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14931173955191770640789623 22396760932787655961184435)
                ·
                  refine ⟨33595141399181483941776653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22396760932787655961184435 33595141399181483941776653)
                  ·
                    refine ⟨12598178024693056478166245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33595141399181483941776653 12598178024693056478166245)
                    ·
                      refine ⟨2362158379629948089656171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12598178024693056478166245 2362158379629948089656171)
                      ·
                        rfl

theorem cell23_4600287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_4600287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600287 prefixEnd_4600287 := by exact prefixLift 4600287
  have htrace : WordTrace (prefixWord ++ tailWord_4600287) baseStart_4600287 baseEnd_4600287 := by
    simpa [prefixWord, tailWord_4600287, baseEnd_4600287] using wordTrace_append hprefix tailTrace_4600287
  have hstable : (prefixWord ++ tailWord_4600287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600287).length < 2 ^ (prefixWord ++ tailWord_4600287).sum := by decide
  have hdescent : baseEnd_4600287 < baseStart_4600287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600394 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_4600394 : Nat := 118140960795 + 4600394 * 2 ^ 59
def prefixEnd_4600394 : Nat := 4983230072969 + 3 ^ 40 * 4600394 * 2
def baseEnd_4600394 : Nat := 2362213322059979171018179

theorem tailTrace_4600394 : CollatzResearch.WordTrace tailWord_4600394 prefixEnd_4600394 2362213322059979171018179 := by
  unfold tailWord_4600394
  simp only [CollatzResearch.WordTrace]
  refine ⟨41947538423891424397188059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111860102463710465059168157 41947538423891424397188059)
  ·
    refine ⟨62921307635837136595782089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41947538423891424397188059 62921307635837136595782089)
    ·
      refine ⟨47190980726877852446836567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62921307635837136595782089 47190980726877852446836567)
      ·
        refine ⟨70786471090316778670254851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47190980726877852446836567 70786471090316778670254851)
        ·
          refine ⟨106179706635475168005382277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70786471090316778670254851 106179706635475168005382277)
          ·
            refine ⟨19908694994151594001009177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106179706635475168005382277 19908694994151594001009177)
            ·
              refine ⟨14931521245613695500756883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19908694994151594001009177 14931521245613695500756883)
              ·
                refine ⟨22397281868420543251135325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14931521245613695500756883 22397281868420543251135325)
                ·
                  refine ⟨8398980700657703719175747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22397281868420543251135325 8398980700657703719175747)
                  ·
                    refine ⟨12598471050986555578763621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8398980700657703719175747 12598471050986555578763621)
                    ·
                      refine ⟨2362213322059979171018179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12598471050986555578763621 2362213322059979171018179)
                      ·
                        rfl

theorem cell23_4600394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_4600394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600394 prefixEnd_4600394 := by exact prefixLift 4600394
  have htrace : WordTrace (prefixWord ++ tailWord_4600394) baseStart_4600394 baseEnd_4600394 := by
    simpa [prefixWord, tailWord_4600394, baseEnd_4600394] using wordTrace_append hprefix tailTrace_4600394
  have hstable : (prefixWord ++ tailWord_4600394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600394).length < 2 ^ (prefixWord ++ tailWord_4600394).sum := by decide
  have hdescent : baseEnd_4600394 < baseStart_4600394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600404 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4600404 : Nat := 118140960795 + 4600404 * 2 ^ 59
def prefixEnd_4600404 : Nat := 4983230072969 + 3 ^ 40 * 4600404 * 2
def baseEnd_4600404 : Nat := 787406152288841377297711

theorem tailTrace_4600404 : CollatzResearch.WordTrace tailWord_4600404 prefixEnd_4600404 787406152288841377297711 := by
  unfold tailWord_4600404
  simp only [CollatzResearch.WordTrace]
  refine ⟨83895259212764734648308133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111860345617019646197744177 83895259212764734648308133)
  ·
    refine ⟨15730361102393387746557775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83895259212764734648308133 15730361102393387746557775)
    ·
      refine ⟨23595541653590081619836663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15730361102393387746557775 23595541653590081619836663)
      ·
        refine ⟨35393312480385122429754995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23595541653590081619836663 35393312480385122429754995)
        ·
          refine ⟨53089968720577683644632493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35393312480385122429754995 53089968720577683644632493)
          ·
            refine ⟨19908738270216631366737185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53089968720577683644632493 19908738270216631366737185)
            ·
              refine ⟨14931553702662473525052889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19908738270216631366737185 14931553702662473525052889)
              ·
                refine ⟨11198665276996855143789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14931553702662473525052889 11198665276996855143789667)
                ·
                  refine ⟨16797997915495282715684501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11198665276996855143789667 16797997915495282715684501)
                  ·
                    refine ⟨787406152288841377297711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16797997915495282715684501 787406152288841377297711)
                    ·
                      rfl

theorem cell23_4600404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4600404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600404 prefixEnd_4600404 := by exact prefixLift 4600404
  have htrace : WordTrace (prefixWord ++ tailWord_4600404) baseStart_4600404 baseEnd_4600404 := by
    simpa [prefixWord, tailWord_4600404, baseEnd_4600404] using wordTrace_append hprefix tailTrace_4600404
  have hstable : (prefixWord ++ tailWord_4600404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600404).length < 2 ^ (prefixWord ++ tailWord_4600404).sum := by decide
  have hdescent : baseEnd_4600404 < baseStart_4600404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600417 : List Nat := [1, 2, 3, 1, 1, 5, 10]
def baseStart_4600417 : Nat := 118140960795 + 4600417 * 2 ^ 59
def prefixEnd_4600417 : Nat := 4983230072969 + 3 ^ 40 * 4600417 * 2
def baseEnd_4600417 : Nat := 29163273235988056555933

theorem tailTrace_4600417 : CollatzResearch.WordTrace tailWord_4600417 prefixEnd_4600417 29163273235988056555933 := by
  unfold tailWord_4600417
  simp only [CollatzResearch.WordTrace]
  refine ⟨167790992574482372516839505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111860661716321581677893003 167790992574482372516839505)
  ·
    refine ⟨125843244430861779387629629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167790992574482372516839505 125843244430861779387629629)
    ·
      refine ⟨47191216661573167270361111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125843244430861779387629629 47191216661573167270361111)
      ·
        refine ⟨70786824992359750905541667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47191216661573167270361111 70786824992359750905541667)
        ·
          refine ⟨106180237488539626358312501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70786824992359750905541667 106180237488539626358312501)
          ·
            refine ⟨9954397264550589971091797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106180237488539626358312501 9954397264550589971091797)
            ·
              refine ⟨29163273235988056555933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9954397264550589971091797 29163273235988056555933)
              ·
                rfl

theorem cell23_4600417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 10].length) (baseStart_4600417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600417 prefixEnd_4600417 := by exact prefixLift 4600417
  have htrace : WordTrace (prefixWord ++ tailWord_4600417) baseStart_4600417 baseEnd_4600417 := by
    simpa [prefixWord, tailWord_4600417, baseEnd_4600417] using wordTrace_append hprefix tailTrace_4600417
  have hstable : (prefixWord ++ tailWord_4600417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600417).length < 2 ^ (prefixWord ++ tailWord_4600417).sum := by decide
  have hdescent : baseEnd_4600417 < baseStart_4600417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600421 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_4600421 : Nat := 118140960795 + 4600421 * 2 ^ 59
def prefixEnd_4600421 : Nat := 4983230072969 + 3 ^ 40 * 4600421 * 2
def baseEnd_4600421 : Nat := 787409062012550188460185

theorem tailTrace_4600421 : CollatzResearch.WordTrace tailWord_4600421 prefixEnd_4600421 787409062012550188460185 := by
  unfold tailWord_4600421
  simp only [CollatzResearch.WordTrace]
  refine ⟨167791138466467881199985117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111860758977645254133323411 167791138466467881199985117)
  ·
    refine ⟨62921676924925455449994419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167791138466467881199985117 62921676924925455449994419)
    ·
      refine ⟨94382515387388183174991629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62921676924925455449994419 94382515387388183174991629)
      ·
        refine ⟨35393443270270568690621861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94382515387388183174991629 35393443270270568690621861)
        ·
          refine ⟨6636270613175731629491599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35393443270270568690621861 6636270613175731629491599)
          ·
            refine ⟨9954405919763597444237399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6636270613175731629491599 9954405919763597444237399)
            ·
              refine ⟨14931608879645396166356099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9954405919763597444237399 14931608879645396166356099)
              ·
                refine ⟨22397413319468094249534149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14931608879645396166356099 22397413319468094249534149)
                ·
                  refine ⟨4199514997400267671787653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22397413319468094249534149 4199514997400267671787653)
                  ·
                    refine ⟨787409062012550188460185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199514997400267671787653 787409062012550188460185)
                    ·
                      rfl

theorem cell23_4600421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_4600421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600421 prefixEnd_4600421 := by exact prefixLift 4600421
  have htrace : WordTrace (prefixWord ++ tailWord_4600421) baseStart_4600421 baseEnd_4600421 := by
    simpa [prefixWord, tailWord_4600421, baseEnd_4600421] using wordTrace_append hprefix tailTrace_4600421
  have hstable : (prefixWord ++ tailWord_4600421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600421).length < 2 ^ (prefixWord ++ tailWord_4600421).sum := by decide
  have hdescent : baseEnd_4600421 < baseStart_4600421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600438 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_4600438 : Nat := 118140960795 + 4600438 * 2 ^ 59
def prefixEnd_4600438 : Nat := 4983230072969 + 3 ^ 40 * 4600438 * 2
def baseEnd_4600438 : Nat := 787411971736258999622659

theorem tailTrace_4600438 : CollatzResearch.WordTrace tailWord_4600438 prefixEnd_4600438 787411971736258999622659 := by
  unfold tailWord_4600438
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486984906712893318959623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111861172338270862068902645 10486984906712893318959623)
  ·
    refine ⟨15730477360069339978439435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10486984906712893318959623 15730477360069339978439435)
    ·
      refine ⟨23595716040104009967659153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15730477360069339978439435 23595716040104009967659153)
      ·
        refine ⟨17696787030078007475744365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23595716040104009967659153 17696787030078007475744365)
        ·
          refine ⟨6636295136279252803404137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17696787030078007475744365 6636295136279252803404137)
          ·
            refine ⟨4977221352209439602553103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6636295136279252803404137 4977221352209439602553103)
            ·
              refine ⟨7465832028314159403829655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4977221352209439602553103 7465832028314159403829655)
              ·
                refine ⟨11198748042471239105744483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7465832028314159403829655 11198748042471239105744483)
                ·
                  refine ⟨16798122063706858658616725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11198748042471239105744483 16798122063706858658616725)
                  ·
                    refine ⟨787411971736258999622659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16798122063706858658616725 787411971736258999622659)
                    ·
                      rfl

theorem cell23_4600438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_4600438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600438 prefixEnd_4600438 := by exact prefixLift 4600438
  have htrace : WordTrace (prefixWord ++ tailWord_4600438) baseStart_4600438 baseEnd_4600438 := by
    simpa [prefixWord, tailWord_4600438, baseEnd_4600438] using wordTrace_append hprefix tailTrace_4600438
  have hstable : (prefixWord ++ tailWord_4600438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600438).length < 2 ^ (prefixWord ++ tailWord_4600438).sum := by decide
  have hdescent : baseEnd_4600438 < baseStart_4600438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600441 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_4600441 : Nat := 118140960795 + 4600441 * 2 ^ 59
def prefixEnd_4600441 : Nat := 4983230072969 + 3 ^ 40 * 4600441 * 2
def baseEnd_4600441 : Nat := 2362237455650740487130463

theorem tailTrace_4600441 : CollatzResearch.WordTrace tailWord_4600441 prefixEnd_4600441 2362237455650740487130463 := by
  unfold tailWord_4600441
  simp only [CollatzResearch.WordTrace]
  refine ⟨167791867926395424615713177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111861245284263616410475451 167791867926395424615713177)
  ·
    refine ⟨125843900944796568461784883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167791867926395424615713177 125843900944796568461784883)
    ·
      refine ⟨188765851417194852692677325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125843900944796568461784883 188765851417194852692677325)
      ·
        refine ⟨70787194281448069759753997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188765851417194852692677325 70787194281448069759753997)
        ·
          refine ⟨26545197855543026159907749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70787194281448069759753997 26545197855543026159907749)
          ·
            refine ⟨4977224597914317404982703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26545197855543026159907749 4977224597914317404982703)
            ·
              refine ⟨7465836896871476107474055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4977224597914317404982703 7465836896871476107474055)
              ·
                refine ⟨11198755345307214161211083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7465836896871476107474055 11198755345307214161211083)
                ·
                  refine ⟨16798133017960821241816625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11198755345307214161211083 16798133017960821241816625)
                  ·
                    refine ⟨12598599763470615931362469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16798133017960821241816625 12598599763470615931362469)
                    ·
                      refine ⟨2362237455650740487130463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12598599763470615931362469 2362237455650740487130463)
                      ·
                        rfl

theorem cell23_4600441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_4600441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600441 prefixEnd_4600441 := by exact prefixLift 4600441
  have htrace : WordTrace (prefixWord ++ tailWord_4600441) baseStart_4600441 baseEnd_4600441 := by
    simpa [prefixWord, tailWord_4600441, baseEnd_4600441] using wordTrace_append hprefix tailTrace_4600441
  have hstable : (prefixWord ++ tailWord_4600441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600441).length < 2 ^ (prefixWord ++ tailWord_4600441).sum := by decide
  have hdescent : baseEnd_4600441 < baseStart_4600441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600478 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4600478 : Nat := 118140960795 + 4600478 * 2 ^ 59
def prefixEnd_4600478 : Nat := 4983230072969 + 3 ^ 40 * 4600478 * 2
def baseEnd_4600478 : Nat := 2362256454434956842367793

theorem tailTrace_4600478 : CollatzResearch.WordTrace tailWord_4600478 prefixEnd_4600478 2362256454434956842367793 := by
  unfold tailWord_4600478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20974152178407672491851261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111862144951507586623206725 20974152178407672491851261)
  ·
    refine ⟨7865307066902877184444223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20974152178407672491851261 7865307066902877184444223)
    ·
      refine ⟨11797960600354315776666335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7865307066902877184444223 11797960600354315776666335)
      ·
        refine ⟨17696940900531473664999503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11797960600354315776666335 17696940900531473664999503)
        ·
          refine ⟨26545411350797210497499255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17696940900531473664999503 26545411350797210497499255)
          ·
            refine ⟨39818117026195815746248883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26545411350797210497499255 39818117026195815746248883)
            ·
              refine ⟨59727175539293723619373325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39818117026195815746248883 59727175539293723619373325)
              ·
                refine ⟨22397690827235146357264997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59727175539293723619373325 22397690827235146357264997)
                ·
                  refine ⟨4199567030106589941987187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22397690827235146357264997 4199567030106589941987187)
                  ·
                    refine ⟨6299350545159884912980781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4199567030106589941987187 6299350545159884912980781)
                    ·
                      refine ⟨2362256454434956842367793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6299350545159884912980781 2362256454434956842367793)
                      ·
                        rfl

theorem cell23_4600478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4600478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600478 prefixEnd_4600478 := by exact prefixLift 4600478
  have htrace : WordTrace (prefixWord ++ tailWord_4600478) baseStart_4600478 baseEnd_4600478 := by
    simpa [prefixWord, tailWord_4600478, baseEnd_4600478] using wordTrace_append hprefix tailTrace_4600478
  have hstable : (prefixWord ++ tailWord_4600478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600478).length < 2 ^ (prefixWord ++ tailWord_4600478).sum := by decide
  have hdescent : baseEnd_4600478 < baseStart_4600478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600484 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_4600484 : Nat := 118140960795 + 4600484 * 2 ^ 59
def prefixEnd_4600484 : Nat := 4983230072969 + 3 ^ 40 * 4600484 * 2
def baseEnd_4600484 : Nat := 2362259535318883818892765

theorem tailTrace_4600484 : CollatzResearch.WordTrace tailWord_4600484 prefixEnd_4600484 2362259535318883818892765 := by
  unfold tailWord_4600484
  simp only [CollatzResearch.WordTrace]
  refine ⟨83896718132619821479764253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111862290843493095306352337 83896718132619821479764253)
  ·
    refine ⟨31461269299732433054911595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83896718132619821479764253 31461269299732433054911595)
    ·
      refine ⟨47191903949598649582367393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31461269299732433054911595 47191903949598649582367393)
      ·
        refine ⟨35393927962198987186775545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47191903949598649582367393 35393927962198987186775545)
        ·
          refine ⟨26545445971649240390081659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35393927962198987186775545 26545445971649240390081659)
          ·
            refine ⟨39818168957473860585122489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26545445971649240390081659 39818168957473860585122489)
            ·
              refine ⟨29863626718105395438841867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39818168957473860585122489 29863626718105395438841867)
              ·
                refine ⟨44795440077158093158262801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29863626718105395438841867 44795440077158093158262801)
                ·
                  refine ⟨33596580057868569868697101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44795440077158093158262801 33596580057868569868697101)
                  ·
                    refine ⟨12598717521700713700761413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33596580057868569868697101 12598717521700713700761413)
                    ·
                      refine ⟨2362259535318883818892765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12598717521700713700761413 2362259535318883818892765)
                      ·
                        rfl

theorem cell23_4600484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_4600484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600484 prefixEnd_4600484 := by exact prefixLift 4600484
  have htrace : WordTrace (prefixWord ++ tailWord_4600484) baseStart_4600484 baseEnd_4600484 := by
    simpa [prefixWord, tailWord_4600484, baseEnd_4600484] using wordTrace_append hprefix tailTrace_4600484
  have hstable : (prefixWord ++ tailWord_4600484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600484).length < 2 ^ (prefixWord ++ tailWord_4600484).sum := by decide
  have hdescent : baseEnd_4600484 < baseStart_4600484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600495 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 2, 1, 3]
def baseStart_4600495 : Nat := 118140960795 + 4600495 * 2 ^ 59
def prefixEnd_4600495 : Nat := 4983230072969 + 3 ^ 40 * 4600495 * 2
def baseEnd_4600495 : Nat := 2362265183606083275855215

theorem tailTrace_4600495 : CollatzResearch.WordTrace tailWord_4600495 prefixEnd_4600495 2362265183606083275855215 := by
  unfold tailWord_4600495
  simp only [CollatzResearch.WordTrace]
  refine ⟨167793837468199791838178939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111862558312133194558785959 167793837468199791838178939)
  ·
    refine ⟨251690756202299687757268409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167793837468199791838178939 251690756202299687757268409)
    ·
      refine ⟨188768067151724765817951307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251690756202299687757268409 188768067151724765817951307)
      ·
        refine ⟨283152100727587148726926961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188768067151724765817951307 283152100727587148726926961)
        ·
          refine ⟨212364075545690361545195221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283152100727587148726926961 212364075545690361545195221)
          ·
            refine ⟨4977283020602117848715513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 212364075545690361545195221 4977283020602117848715513)
            ·
              refine ⟨3732962265451588386536635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977283020602117848715513 3732962265451588386536635)
              ·
                refine ⟨5599443398177382579804953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732962265451588386536635 5599443398177382579804953)
                ·
                  refine ⟨4199582548633036934853715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5599443398177382579804953 4199582548633036934853715)
                  ·
                    refine ⟨6299373822949555402280573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4199582548633036934853715 6299373822949555402280573)
                    ·
                      refine ⟨2362265183606083275855215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6299373822949555402280573 2362265183606083275855215)
                      ·
                        rfl

theorem cell23_4600495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 1, 3].length) (baseStart_4600495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600495 prefixEnd_4600495 := by exact prefixLift 4600495
  have htrace : WordTrace (prefixWord ++ tailWord_4600495) baseStart_4600495 baseEnd_4600495 := by
    simpa [prefixWord, tailWord_4600495, baseEnd_4600495] using wordTrace_append hprefix tailTrace_4600495
  have hstable : (prefixWord ++ tailWord_4600495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600495).length < 2 ^ (prefixWord ++ tailWord_4600495).sum := by decide
  have hdescent : baseEnd_4600495 < baseStart_4600495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600535 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_4600535 : Nat := 118140960795 + 4600535 * 2 ^ 59
def prefixEnd_4600535 : Nat := 4983230072969 + 3 ^ 40 * 4600535 * 2
def baseEnd_4600535 : Nat := 2362285722832263119355031

theorem tailTrace_4600535 : CollatzResearch.WordTrace tailWord_4600535 prefixEnd_4600535 2362285722832263119355031 := by
  unfold tailWord_4600535
  simp only [CollatzResearch.WordTrace]
  refine ⟨167795296388054878669635059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111863530925369919113090039 167795296388054878669635059)
  ·
    refine ⟨251692944582082318004452589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167795296388054878669635059 251692944582082318004452589)
    ·
      refine ⟨94384854218280869251669721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251692944582082318004452589 94384854218280869251669721)
      ·
        refine ⟨70788640663710651938752291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94384854218280869251669721 70788640663710651938752291)
        ·
          refine ⟨106182960995565977908128437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70788640663710651938752291 106182960995565977908128437)
          ·
            refine ⟨9954652593334310428887041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106182960995565977908128437 9954652593334310428887041)
            ·
              refine ⟨7465989445000732821665281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9954652593334310428887041 7465989445000732821665281)
              ·
                refine ⟨5599492083750549616248961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7465989445000732821665281 5599492083750549616248961)
                ·
                  refine ⟨4199619062812912212186721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5599492083750549616248961 4199619062812912212186721)
                  ·
                    refine ⟨3149714297109684159140041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4199619062812912212186721 3149714297109684159140041)
                    ·
                      refine ⟨2362285722832263119355031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149714297109684159140041 2362285722832263119355031)
                      ·
                        rfl

theorem cell23_4600535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_4600535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600535 prefixEnd_4600535 := by exact prefixLift 4600535
  have htrace : WordTrace (prefixWord ++ tailWord_4600535) baseStart_4600535 baseEnd_4600535 := by
    simpa [prefixWord, tailWord_4600535, baseEnd_4600535] using wordTrace_append hprefix tailTrace_4600535
  have hstable : (prefixWord ++ tailWord_4600535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600535).length < 2 ^ (prefixWord ++ tailWord_4600535).sum := by decide
  have hdescent : baseEnd_4600535 < baseStart_4600535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600554 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_4600554 : Nat := 118140960795 + 4600554 * 2 ^ 59
def prefixEnd_4600554 : Nat := 4983230072969 + 3 ^ 40 * 4600554 * 2
def baseEnd_4600554 : Nat := 787431826321566181672481

theorem tailTrace_4600554 : CollatzResearch.WordTrace tailWord_4600554 prefixEnd_4600554 787431826321566181672481 := by
  unfold tailWord_4600554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41948997343746511228644179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111863992916657363276384477 41948997343746511228644179)
  ·
    refine ⟨62923496015619766842966269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41948997343746511228644179 62923496015619766842966269)
    ·
      refine ⟨23596311005857412566112351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62923496015619766842966269 23596311005857412566112351)
      ·
        refine ⟨35394466508786118849168527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23596311005857412566112351 35394466508786118849168527)
        ·
          refine ⟨53091699763179178273752791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35394466508786118849168527 53091699763179178273752791)
          ·
            refine ⟨79637549644768767410629187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53091699763179178273752791 79637549644768767410629187)
            ·
              refine ⟨119456324467153151115943781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79637549644768767410629187 119456324467153151115943781)
              ·
                refine ⟨22398060837591215834239459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119456324467153151115943781 22398060837591215834239459)
                ·
                  refine ⟨33597091256386823751359189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22398060837591215834239459 33597091256386823751359189)
                  ·
                    refine ⟨787431826321566181672481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33597091256386823751359189 787431826321566181672481)
                    ·
                      rfl

theorem cell23_4600554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_4600554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600554 prefixEnd_4600554 := by exact prefixLift 4600554
  have htrace : WordTrace (prefixWord ++ tailWord_4600554) baseStart_4600554 baseEnd_4600554 := by
    simpa [prefixWord, tailWord_4600554, baseEnd_4600554] using wordTrace_append hprefix tailTrace_4600554
  have hstable : (prefixWord ++ tailWord_4600554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600554).length < 2 ^ (prefixWord ++ tailWord_4600554).sum := by decide
  have hdescent : baseEnd_4600554 < baseStart_4600554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600561 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_4600561 : Nat := 118140960795 + 4600561 * 2 ^ 59
def prefixEnd_4600561 : Nat := 4983230072969 + 3 ^ 40 * 4600561 * 2
def baseEnd_4600561 : Nat := 2362299073329280017629911

theorem tailTrace_4600561 : CollatzResearch.WordTrace tailWord_4600561 prefixEnd_4600561 2362299073329280017629911 := by
  unfold tailWord_4600561
  simp only [CollatzResearch.WordTrace]
  refine ⟨167796244685960685110081537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111864163123973790073387691 167796244685960685110081537)
  ·
    refine ⟨125847183514470513832561153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167796244685960685110081537 125847183514470513832561153)
    ·
      refine ⟨94385387635852885374420865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125847183514470513832561153 94385387635852885374420865)
      ·
        refine ⟨70789040726889664030815649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94385387635852885374420865 70789040726889664030815649)
        ·
          refine ⟨53091780545167248023111737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70789040726889664030815649 53091780545167248023111737)
          ·
            refine ⟨39818835408875436017333803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53091780545167248023111737 39818835408875436017333803)
            ·
              refine ⟨59728253113313154026000705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39818835408875436017333803 59728253113313154026000705)
              ·
                refine ⟨44796189834984865519500529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59728253113313154026000705 44796189834984865519500529)
                ·
                  refine ⟨33597142376238649139625397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44796189834984865519500529 33597142376238649139625397)
                  ·
                    refine ⟨3149732097772373356839881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33597142376238649139625397 3149732097772373356839881)
                    ·
                      refine ⟨2362299073329280017629911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149732097772373356839881 2362299073329280017629911)
                      ·
                        rfl

theorem cell23_4600561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_4600561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600561 prefixEnd_4600561 := by exact prefixLift 4600561
  have htrace : WordTrace (prefixWord ++ tailWord_4600561) baseStart_4600561 baseEnd_4600561 := by
    simpa [prefixWord, tailWord_4600561, baseEnd_4600561] using wordTrace_append hprefix tailTrace_4600561
  have hstable : (prefixWord ++ tailWord_4600561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600561).length < 2 ^ (prefixWord ++ tailWord_4600561).sum := by decide
  have hdescent : baseEnd_4600561 < baseStart_4600561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600591 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 4, 4, 2]
def baseStart_4600591 : Nat := 118140960795 + 4600591 * 2 ^ 59
def prefixEnd_4600591 : Nat := 4983230072969 + 3 ^ 40 * 4600591 * 2
def baseEnd_4600591 : Nat := 2362314477748914900254773

theorem tailTrace_4600591 : CollatzResearch.WordTrace tailWord_4600591 prefixEnd_4600591 2362314477748914900254773 := by
  unfold tailWord_4600591
  simp only [CollatzResearch.WordTrace]
  refine ⟨167797338875852000233673627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111864892583901333489115751 167797338875852000233673627)
  ·
    refine ⟨251696008313778000350510441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167797338875852000233673627 251696008313778000350510441)
    ·
      refine ⟨188772006235333500262882831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251696008313778000350510441 188772006235333500262882831)
      ·
        refine ⟨283158009353000250394324247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188772006235333500262882831 283158009353000250394324247)
        ·
          refine ⟨424737014029500375591486371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283158009353000250394324247 424737014029500375591486371)
          ·
            refine ⟨637105521044250563387229557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424737014029500375591486371 637105521044250563387229557)
            ·
              refine ⟨59728642597898490317552771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 637105521044250563387229557 59728642597898490317552771)
              ·
                refine ⟨89592963896847735476329157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59728642597898490317552771 89592963896847735476329157)
                ·
                  refine ⟨16798680730658950401811717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89592963896847735476329157 16798680730658950401811717)
                  ·
                    refine ⟨3149752636998553200339697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16798680730658950401811717 3149752636998553200339697)
                    ·
                      refine ⟨2362314477748914900254773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149752636998553200339697 2362314477748914900254773)
                      ·
                        rfl

theorem cell23_4600591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4, 2].length) (baseStart_4600591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600591 prefixEnd_4600591 := by exact prefixLift 4600591
  have htrace : WordTrace (prefixWord ++ tailWord_4600591) baseStart_4600591 baseEnd_4600591 := by
    simpa [prefixWord, tailWord_4600591, baseEnd_4600591] using wordTrace_append hprefix tailTrace_4600591
  have hstable : (prefixWord ++ tailWord_4600591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600591).length < 2 ^ (prefixWord ++ tailWord_4600591).sum := by decide
  have hdescent : baseEnd_4600591 < baseStart_4600591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600608 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4600608 : Nat := 118140960795 + 4600608 * 2 ^ 59
def prefixEnd_4600608 : Nat := 4983230072969 + 3 ^ 40 * 4600608 * 2
def baseEnd_4600608 : Nat := 2362323206920041333742195

theorem tailTrace_4600608 : CollatzResearch.WordTrace tailWord_4600608 prefixEnd_4600608 2362323206920041333742195 := by
  unfold tailWord_4600608
  simp only [CollatzResearch.WordTrace]
  refine ⟨83898979458395206068521239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111865305944526941424694985 83898979458395206068521239)
  ·
    refine ⟨125848469187592809102781859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83898979458395206068521239 125848469187592809102781859)
    ·
      refine ⟨188772703781389213654172789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125848469187592809102781859 188772703781389213654172789)
      ·
        refine ⟨17697440979505238780078699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188772703781389213654172789 17697440979505238780078699)
        ·
          refine ⟨26546161469257858170118049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17697440979505238780078699 26546161469257858170118049)
          ·
            refine ⟨19909621101943393627588537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26546161469257858170118049 19909621101943393627588537)
            ·
              refine ⟨14932215826457545220691403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19909621101943393627588537 14932215826457545220691403)
              ·
                refine ⟨22398323739686317831037105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14932215826457545220691403 22398323739686317831037105)
                ·
                  refine ⟨16798742804764738373277829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22398323739686317831037105 16798742804764738373277829)
                  ·
                    refine ⟨3149764275893388444989593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16798742804764738373277829 3149764275893388444989593)
                    ·
                      refine ⟨2362323206920041333742195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149764275893388444989593 2362323206920041333742195)
                      ·
                        rfl

theorem cell23_4600608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4600608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600608 prefixEnd_4600608 := by exact prefixLift 4600608
  have htrace : WordTrace (prefixWord ++ tailWord_4600608) baseStart_4600608 baseEnd_4600608 := by
    simpa [prefixWord, tailWord_4600608, baseEnd_4600608] using wordTrace_append hprefix tailTrace_4600608
  have hstable : (prefixWord ++ tailWord_4600608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600608).length < 2 ^ (prefixWord ++ tailWord_4600608).sum := by decide
  have hdescent : baseEnd_4600608 < baseStart_4600608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 9, 2]
def baseStart_4600651 : Nat := 118140960795 + 4600651 * 2 ^ 59
def prefixEnd_4600651 : Nat := 4983230072969 + 3 ^ 40 * 4600651 * 2
def baseEnd_4600651 : Nat := 2362345286588184665504497

theorem tailTrace_4600651 : CollatzResearch.WordTrace tailWord_4600651 prefixEnd_4600651 2362345286588184665504497 := by
  unfold tailWord_4600651
  simp only [CollatzResearch.WordTrace]
  refine ⟨167799527255634630480857807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111866351503756420320571871 167799527255634630480857807)
  ·
    refine ⟨251699290883451945721286711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167799527255634630480857807 251699290883451945721286711)
    ·
      refine ⟨377548936325177918581930067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251699290883451945721286711 377548936325177918581930067)
      ·
        refine ⟨566323404487766877872895101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377548936325177918581930067 566323404487766877872895101)
        ·
          refine ⟨212371276682912579202335663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566323404487766877872895101 212371276682912579202335663)
          ·
            refine ⟨318556915024368868803503495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212371276682912579202335663 318556915024368868803503495)
            ·
              refine ⟨477835372536553303205255243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318556915024368868803503495 477835372536553303205255243)
              ·
                refine ⟨716753058804829954807882865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477835372536553303205255243 716753058804829954807882865)
                ·
                  refine ⟨537564794103622466105912149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 716753058804829954807882865 537564794103622466105912149)
                  ·
                    refine ⟨3149793715450912887339329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 537564794103622466105912149 3149793715450912887339329)
                    ·
                      refine ⟨2362345286588184665504497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149793715450912887339329 2362345286588184665504497)
                      ·
                        rfl

theorem cell23_4600651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9, 2].length) (baseStart_4600651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600651 prefixEnd_4600651 := by exact prefixLift 4600651
  have htrace : WordTrace (prefixWord ++ tailWord_4600651) baseStart_4600651 baseEnd_4600651 := by
    simpa [prefixWord, tailWord_4600651, baseEnd_4600651] using wordTrace_append hprefix tailTrace_4600651
  have hstable : (prefixWord ++ tailWord_4600651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600651).length < 2 ^ (prefixWord ++ tailWord_4600651).sum := by decide
  have hdescent : baseEnd_4600651 < baseStart_4600651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600652 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_4600652 : Nat := 118140960795 + 4600652 * 2 ^ 59
def prefixEnd_4600652 : Nat := 4983230072969 + 3 ^ 40 * 4600652 * 2
def baseEnd_4600652 : Nat := 787448600022946387197331

theorem tailTrace_4600652 : CollatzResearch.WordTrace tailWord_4600652 prefixEnd_4600652 787448600022946387197331 := by
  unfold tailWord_4600652
  simp only [CollatzResearch.WordTrace]
  refine ⟨83899781864315503825822105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111866375819087338434429473 83899781864315503825822105)
  ·
    refine ⟨62924836398236627869366579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83899781864315503825822105 62924836398236627869366579)
    ·
      refine ⟨94387254597354941804049869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62924836398236627869366579 94387254597354941804049869)
      ·
        refine ⟨35395220474008103176518701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94387254597354941804049869 35395220474008103176518701)
        ·
          refine ⟨13273207677753038691194513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35395220474008103176518701 13273207677753038691194513)
          ·
            refine ⟨9954905758314779018395885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13273207677753038691194513 9954905758314779018395885)
            ·
              refine ⟨3733089659368042131898457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9954905758314779018395885 3733089659368042131898457)
              ·
                refine ⟨2799817244526031598923843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733089659368042131898457 2799817244526031598923843)
                ·
                  refine ⟨4199725866789047398385765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799817244526031598923843 4199725866789047398385765)
                  ·
                    refine ⟨787448600022946387197331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199725866789047398385765 787448600022946387197331)
                    ·
                      rfl

theorem cell23_4600652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_4600652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600652 prefixEnd_4600652 := by exact prefixLift 4600652
  have htrace : WordTrace (prefixWord ++ tailWord_4600652) baseStart_4600652 baseEnd_4600652 := by
    simpa [prefixWord, tailWord_4600652, baseEnd_4600652] using wordTrace_append hprefix tailTrace_4600652
  have hstable : (prefixWord ++ tailWord_4600652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600652).length < 2 ^ (prefixWord ++ tailWord_4600652).sum := by decide
  have hdescent : baseEnd_4600652 < baseStart_4600652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600661 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_4600661 : Nat := 118140960795 + 4600661 * 2 ^ 59
def prefixEnd_4600661 : Nat := 4983230072969 + 3 ^ 40 * 4600661 * 2
def baseEnd_4600661 : Nat := 787450140464909875459817

theorem tailTrace_4600661 : CollatzResearch.WordTrace tailWord_4600661 prefixEnd_4600661 787450140464909875459817 := by
  unfold tailWord_4600661
  simp only [CollatzResearch.WordTrace]
  refine ⟨167799891985598402188721837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111866594657065601459147891 167799891985598402188721837)
  ·
    refine ⟨62924959494599400820770689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167799891985598402188721837 62924959494599400820770689)
    ·
      refine ⟨47193719620949550615578017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62924959494599400820770689 47193719620949550615578017)
      ·
        refine ⟨35395289715712162961683513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47193719620949550615578017 35395289715712162961683513)
        ·
          refine ⟨26546467286784122221262635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35395289715712162961683513 26546467286784122221262635)
          ·
            refine ⟨39819700930176183331893953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26546467286784122221262635 39819700930176183331893953)
            ·
              refine ⟨29864775697632137498920465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39819700930176183331893953 29864775697632137498920465)
              ·
                refine ⟨22398581773224103124190349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29864775697632137498920465 22398581773224103124190349)
                ·
                  refine ⟨8399468164959038671571381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22398581773224103124190349 8399468164959038671571381)
                  ·
                    refine ⟨787450140464909875459817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8399468164959038671571381 787450140464909875459817)
                    ·
                      rfl

theorem cell23_4600661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_4600661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600661 prefixEnd_4600661 := by exact prefixLift 4600661
  have htrace : WordTrace (prefixWord ++ tailWord_4600661) baseStart_4600661 baseEnd_4600661 := by
    simpa [prefixWord, tailWord_4600661, baseEnd_4600661] using wordTrace_append hprefix tailTrace_4600661
  have hstable : (prefixWord ++ tailWord_4600661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600661).length < 2 ^ (prefixWord ++ tailWord_4600661).sum := by decide
  have hdescent : baseEnd_4600661 < baseStart_4600661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600691 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 6, 4]
def baseStart_4600691 : Nat := 118140960795 + 4600691 * 2 ^ 59
def prefixEnd_4600691 : Nat := 4983230072969 + 3 ^ 40 * 4600691 * 2
def baseEnd_4600691 : Nat := 787455275271454836334771

theorem tailTrace_4600691 : CollatzResearch.WordTrace tailWord_4600691 prefixEnd_4600691 787455275271454836334771 := by
  unfold tailWord_4600691
  simp only [CollatzResearch.WordTrace]
  refine ⟨167800986175489717312313927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111867324116993144874875951 167800986175489717312313927)
  ·
    refine ⟨251701479263234575968470891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167800986175489717312313927 251701479263234575968470891)
    ·
      refine ⟨377552218894851863952706337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251701479263234575968470891 377552218894851863952706337)
      ·
        refine ⟨283164164171138897964529753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377552218894851863952706337 283164164171138897964529753)
        ·
          refine ⟨212373123128354173473397315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283164164171138897964529753 212373123128354173473397315)
          ·
            refine ⟨318559684692531260210095973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212373123128354173473397315 318559684692531260210095973)
            ·
              refine ⟨59729940879849611289392995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 318559684692531260210095973 59729940879849611289392995)
              ·
                refine ⟨89594911319774416934089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59729940879849611289392995 89594911319774416934089493)
                ·
                  refine ⟨4199761468114425793785445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89594911319774416934089493 4199761468114425793785445)
                  ·
                    refine ⟨787455275271454836334771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4199761468114425793785445 787455275271454836334771)
                    ·
                      rfl

theorem cell23_4600691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 4].length) (baseStart_4600691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600691 prefixEnd_4600691 := by exact prefixLift 4600691
  have htrace : WordTrace (prefixWord ++ tailWord_4600691) baseStart_4600691 baseEnd_4600691 := by
    simpa [prefixWord, tailWord_4600691, baseEnd_4600691] using wordTrace_append hprefix tailTrace_4600691
  have hstable : (prefixWord ++ tailWord_4600691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600691).length < 2 ^ (prefixWord ++ tailWord_4600691).sum := by decide
  have hdescent : baseEnd_4600691 < baseStart_4600691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600709 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 1, 1, 3]
def baseStart_4600709 : Nat := 118140960795 + 4600709 * 2 ^ 59
def prefixEnd_4600709 : Nat := 4983230072969 + 3 ^ 40 * 4600709 * 2
def baseEnd_4600709 : Nat := 2362375068466145438579231

theorem tailTrace_4600709 : CollatzResearch.WordTrace tailWord_4600709 prefixEnd_4600709 2362375068466145438579231 := by
  unfold tailWord_4600709
  simp only [CollatzResearch.WordTrace]
  refine ⟨167801642689424506386469181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111867761792949670924312787 167801642689424506386469181)
  ·
    refine ⟨62925616008534189894925943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167801642689424506386469181 62925616008534189894925943)
    ·
      refine ⟨94388424012801284842388915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62925616008534189894925943 94388424012801284842388915)
      ·
        refine ⟨141582636019201927263583373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94388424012801284842388915 141582636019201927263583373)
        ·
          refine ⟨53093488507200722723843765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141582636019201927263583373 53093488507200722723843765)
          ·
            refine ⟨4977514547550067755360353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53093488507200722723843765 4977514547550067755360353)
            ·
              refine ⟨3733135910662550816520265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977514547550067755360353 3733135910662550816520265)
              ·
                refine ⟨2799851932996913112390199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733135910662550816520265 2799851932996913112390199)
                ·
                  refine ⟨4199777899495369668585299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799851932996913112390199 4199777899495369668585299)
                  ·
                    refine ⟨6299666849243054502877949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4199777899495369668585299 6299666849243054502877949)
                    ·
                      refine ⟨2362375068466145438579231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6299666849243054502877949 2362375068466145438579231)
                      ·
                        rfl

theorem cell23_4600709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_4600709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600709 prefixEnd_4600709 := by exact prefixLift 4600709
  have htrace : WordTrace (prefixWord ++ tailWord_4600709) baseStart_4600709 baseEnd_4600709 := by
    simpa [prefixWord, tailWord_4600709, baseEnd_4600709] using wordTrace_append hprefix tailTrace_4600709
  have hstable : (prefixWord ++ tailWord_4600709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600709).length < 2 ^ (prefixWord ++ tailWord_4600709).sum := by decide
  have hdescent : baseEnd_4600709 < baseStart_4600709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600748 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_4600748 : Nat := 118140960795 + 4600748 * 2 ^ 59
def prefixEnd_4600748 : Nat := 4983230072969 + 3 ^ 40 * 4600748 * 2
def baseEnd_4600748 : Nat := 2362395094211670785991551

theorem tailTrace_4600748 : CollatzResearch.WordTrace tailWord_4600748 prefixEnd_4600748 2362395094211670785991551 := by
  unfold tailWord_4600748
  simp only [CollatzResearch.WordTrace]
  refine ⟨83901532568141608023569449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111868710090855477364759265 83901532568141608023569449)
  ·
    refine ⟨62926149426106206017677087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83901532568141608023569449 62926149426106206017677087)
    ·
      refine ⟨94389224139159309026515631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62926149426106206017677087 94389224139159309026515631)
      ·
        refine ⟨141583836208738963539773447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94389224139159309026515631 141583836208738963539773447)
        ·
          refine ⟨212375754313108445309660171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141583836208738963539773447 212375754313108445309660171)
          ·
            refine ⟨318563631469662667964490257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212375754313108445309660171 318563631469662667964490257)
            ·
              refine ⟨238922723602247000973367693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318563631469662667964490257 238922723602247000973367693)
              ·
                refine ⟨89596021350842625365012885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238922723602247000973367693 89596021350842625365012885)
                ·
                  refine ⟨4199813500820748063984979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89596021350842625365012885 4199813500820748063984979)
                  ·
                    refine ⟨6299720251231122095977469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4199813500820748063984979 6299720251231122095977469)
                    ·
                      refine ⟨2362395094211670785991551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6299720251231122095977469 2362395094211670785991551)
                      ·
                        rfl

theorem cell23_4600748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_4600748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600748 prefixEnd_4600748 := by exact prefixLift 4600748
  have htrace : WordTrace (prefixWord ++ tailWord_4600748) baseStart_4600748 baseEnd_4600748 := by
    simpa [prefixWord, tailWord_4600748, baseEnd_4600748] using wordTrace_append hprefix tailTrace_4600748
  have hstable : (prefixWord ++ tailWord_4600748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600748).length < 2 ^ (prefixWord ++ tailWord_4600748).sum := by decide
  have hdescent : baseEnd_4600748 < baseStart_4600748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600792 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_4600792 : Nat := 118140960795 + 4600792 * 2 ^ 59
def prefixEnd_4600792 : Nat := 4983230072969 + 3 ^ 40 * 4600792 * 2
def baseEnd_4600792 : Nat := 2362417687360468613841349

theorem tailTrace_4600792 : CollatzResearch.WordTrace tailWord_4600792 prefixEnd_4600792 2362417687360468613841349 := by
  unfold tailWord_4600792
  simp only [CollatzResearch.WordTrace]
  refine ⟨83902334974061905780870315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111869779965415874374493753 83902334974061905780870315)
  ·
    refine ⟨125853502461092858671305473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83902334974061905780870315 125853502461092858671305473)
    ·
      refine ⟨94390126845819644003479105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125853502461092858671305473 94390126845819644003479105)
      ·
        refine ⟨70792595134364733002609329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94390126845819644003479105 70792595134364733002609329)
        ·
          refine ⟨53094446350773549751956997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70792595134364733002609329 53094446350773549751956997)
          ·
            refine ⟨9955208690770040578491937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53094446350773549751956997 9955208690770040578491937)
            ·
              refine ⟨7466406518077530433868953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9955208690770040578491937 7466406518077530433868953)
              ·
                refine ⟨5599804888558147825401715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7466406518077530433868953 5599804888558147825401715)
                ·
                  refine ⟨8399707332837221738102573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5599804888558147825401715 8399707332837221738102573)
                  ·
                    refine ⟨3149890249813958151788465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8399707332837221738102573 3149890249813958151788465)
                    ·
                      refine ⟨2362417687360468613841349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3149890249813958151788465 2362417687360468613841349)
                      ·
                        rfl

theorem cell23_4600792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_4600792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600792 prefixEnd_4600792 := by exact prefixLift 4600792
  have htrace : WordTrace (prefixWord ++ tailWord_4600792) baseStart_4600792 baseEnd_4600792 := by
    simpa [prefixWord, tailWord_4600792, baseEnd_4600792] using wordTrace_append hprefix tailTrace_4600792
  have hstable : (prefixWord ++ tailWord_4600792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600792).length < 2 ^ (prefixWord ++ tailWord_4600792).sum := by decide
  have hdescent : baseEnd_4600792 < baseStart_4600792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600828 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 7]
def baseStart_4600828 : Nat := 118140960795 + 4600828 * 2 ^ 59
def prefixEnd_4600828 : Nat := 4983230072969 + 3 ^ 40 * 4600828 * 2
def baseEnd_4600828 : Nat := 262492908073781163665687

theorem tailTrace_4600828 : CollatzResearch.WordTrace tailWord_4600828 prefixEnd_4600828 262492908073781163665687 := by
  unfold tailWord_4600828
  simp only [CollatzResearch.WordTrace]
  refine ⟨83902991487996694855025569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111870655317328926473367425 83902991487996694855025569)
  ·
    refine ⟨62927243615997521141269177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83902991487996694855025569 62927243615997521141269177)
    ·
      refine ⟨47195432711998140855951883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62927243615997521141269177 47195432711998140855951883)
      ·
        refine ⟨70793149067997211283927825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47195432711998140855951883 70793149067997211283927825)
        ·
          refine ⟨53094861800997908462945869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70793149067997211283927825 53094861800997908462945869)
          ·
            refine ⟨19910573175374215673604701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53094861800997908462945869 19910573175374215673604701)
            ·
              refine ⟨7466464940765330877601763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19910573175374215673604701 7466464940765330877601763)
              ·
                refine ⟨11199697411147996316402645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7466464940765330877601763 11199697411147996316402645)
                ·
                  refine ⟨262492908073781163665687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11199697411147996316402645 262492908073781163665687)
                  ·
                    rfl

theorem cell23_4600828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_4600828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600828 prefixEnd_4600828 := by exact prefixLift 4600828
  have htrace : WordTrace (prefixWord ++ tailWord_4600828) baseStart_4600828 baseEnd_4600828 := by
    simpa [prefixWord, tailWord_4600828, baseEnd_4600828] using wordTrace_append hprefix tailTrace_4600828
  have hstable : (prefixWord ++ tailWord_4600828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600828).length < 2 ^ (prefixWord ++ tailWord_4600828).sum := by decide
  have hdescent : baseEnd_4600828 < baseStart_4600828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600841 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_4600841 : Nat := 118140960795 + 4600841 * 2 ^ 59
def prefixEnd_4600841 : Nat := 4983230072969 + 3 ^ 40 * 4600841 * 2
def baseEnd_4600841 : Nat := 787480949304179640709541

theorem tailTrace_4600841 : CollatzResearch.WordTrace tailWord_4600841 prefixEnd_4600841 787480949304179640709541 := by
  unfold tailWord_4600841
  simp only [CollatzResearch.WordTrace]
  refine ⟨167806457124946292930274377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111870971416630861953516251 167806457124946292930274377)
  ·
    refine ⟨125854842843709719697705783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167806457124946292930274377 125854842843709719697705783)
    ·
      refine ⟨188782264265564579546558675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125854842843709719697705783 188782264265564579546558675)
      ·
        refine ⟨283173396398346869319838013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188782264265564579546558675 283173396398346869319838013)
        ·
          refine ⟨106190023649380075994939255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283173396398346869319838013 106190023649380075994939255)
          ·
            refine ⟨159285035474070113992408883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106190023649380075994939255 159285035474070113992408883)
            ·
              refine ⟨238927553211105170988613325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159285035474070113992408883 238927553211105170988613325)
              ·
                refine ⟨89597832454164439120729997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238927553211105170988613325 89597832454164439120729997)
                ·
                  refine ⟨33599187170311664670273749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89597832454164439120729997 33599187170311664670273749)
                  ·
                    refine ⟨787480949304179640709541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33599187170311664670273749 787480949304179640709541)
                    ·
                      rfl

theorem cell23_4600841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_4600841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600841 prefixEnd_4600841 := by exact prefixLift 4600841
  have htrace : WordTrace (prefixWord ++ tailWord_4600841) baseStart_4600841 baseEnd_4600841 := by
    simpa [prefixWord, tailWord_4600841, baseEnd_4600841] using wordTrace_append hprefix tailTrace_4600841
  have hstable : (prefixWord ++ tailWord_4600841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600841).length < 2 ^ (prefixWord ++ tailWord_4600841).sum := by decide
  have hdescent : baseEnd_4600841 < baseStart_4600841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600851 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_4600851 : Nat := 118140960795 + 4600851 * 2 ^ 59
def prefixEnd_4600851 : Nat := 4983230072969 + 3 ^ 40 * 4600851 * 2
def baseEnd_4600851 : Nat := 2362447982719083883003577

theorem tailTrace_4600851 : CollatzResearch.WordTrace tailWord_4600851 prefixEnd_4600851 2362447982719083883003577 := by
  unfold tailWord_4600851
  simp only [CollatzResearch.WordTrace]
  refine ⟨167806821854910064638138407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111871214569940043092092271 167806821854910064638138407)
  ·
    refine ⟨251710232782365096957207611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167806821854910064638138407 251710232782365096957207611)
    ·
      refine ⟨377565349173547645435811417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251710232782365096957207611 377565349173547645435811417)
      ·
        refine ⟨283174011880160734076858563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377565349173547645435811417 283174011880160734076858563)
        ·
          refine ⟨424761017820241101115287845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283174011880160734076858563 424761017820241101115287845)
          ·
            refine ⟨79642690841295206459116471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 424761017820241101115287845 79642690841295206459116471)
            ·
              refine ⟨119464036261942809688674707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79642690841295206459116471 119464036261942809688674707)
              ·
                refine ⟨179196054392914214533012061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119464036261942809688674707 179196054392914214533012061)
                ·
                  refine ⟨67198520397342830449879523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179196054392914214533012061 67198520397342830449879523)
                  ·
                    refine ⟨100797780596014245674819285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67198520397342830449879523 100797780596014245674819285)
                    ·
                      refine ⟨2362447982719083883003577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100797780596014245674819285 2362447982719083883003577)
                      ·
                        rfl

theorem cell23_4600851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_4600851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600851 prefixEnd_4600851 := by exact prefixLift 4600851
  have htrace : WordTrace (prefixWord ++ tailWord_4600851) baseStart_4600851 baseEnd_4600851 := by
    simpa [prefixWord, tailWord_4600851, baseEnd_4600851] using wordTrace_append hprefix tailTrace_4600851
  have hstable : (prefixWord ++ tailWord_4600851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600851).length < 2 ^ (prefixWord ++ tailWord_4600851).sum := by decide
  have hdescent : baseEnd_4600851 < baseStart_4600851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600935 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 6]
def baseStart_4600935 : Nat := 118140960795 + 4600935 * 2 ^ 59
def prefixEnd_4600935 : Nat := 4983230072969 + 3 ^ 40 * 4600935 * 2
def baseEnd_4600935 : Nat := 262499012788229061594799

theorem tailTrace_4600935 : CollatzResearch.WordTrace tailWord_4600935 prefixEnd_4600935 262499012788229061594799 := by
  unfold tailWord_4600935
  simp only [CollatzResearch.WordTrace]
  refine ⟨167809885586605746984196259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111873257057737164656130839 167809885586605746984196259)
  ·
    refine ⟨251714828379908620476294389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167809885586605746984196259 251714828379908620476294389)
    ·
      refine ⟨23598265160616433169652599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251714828379908620476294389 23598265160616433169652599)
      ·
        refine ⟨35397397740924649754478899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23598265160616433169652599 35397397740924649754478899)
        ·
          refine ⟨53096096611386974631718349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35397397740924649754478899 53096096611386974631718349)
          ·
            refine ⟨19911036229270115486894381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53096096611386974631718349 19911036229270115486894381)
            ·
              refine ⟨7466638585976293307585393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19911036229270115486894381 7466638585976293307585393)
              ·
                refine ⟨5599978939482219980689045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7466638585976293307585393 5599978939482219980689045)
                ·
                  refine ⟨262499012788229061594799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5599978939482219980689045 262499012788229061594799)
                  ·
                    rfl

theorem cell23_4600935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 6].length) (baseStart_4600935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600935 prefixEnd_4600935 := by exact prefixLift 4600935
  have htrace : WordTrace (prefixWord ++ tailWord_4600935) baseStart_4600935 baseEnd_4600935 := by
    simpa [prefixWord, tailWord_4600935, baseEnd_4600935] using wordTrace_append hprefix tailTrace_4600935
  have hstable : (prefixWord ++ tailWord_4600935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600935).length < 2 ^ (prefixWord ++ tailWord_4600935).sum := by decide
  have hdescent : baseEnd_4600935 < baseStart_4600935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4600979 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 1, 1, 3]
def baseStart_4600979 : Nat := 118140960795 + 4600979 * 2 ^ 59
def prefixEnd_4600979 : Nat := 4983230072969 + 3 ^ 40 * 4600979 * 2
def baseEnd_4600979 : Nat := 2362513708242859382202989

theorem tailTrace_4600979 : CollatzResearch.WordTrace tailWord_4600979 prefixEnd_4600979 2362513708242859382202989 := by
  unfold tailWord_4600979
  simp only [CollatzResearch.WordTrace]
  refine ⟨167811490398446342498797991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111874326932297561665865327 167811490398446342498797991)
  ·
    refine ⟨251717235597669513748196987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167811490398446342498797991 251717235597669513748196987)
    ·
      refine ⟨377575853396504270622295481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251717235597669513748196987 377575853396504270622295481)
      ·
        refine ⟨283181890047378202966721611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377575853396504270622295481 283181890047378202966721611)
        ·
          refine ⟨424772835071067304450082417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283181890047378202966721611 424772835071067304450082417)
          ·
            refine ⟨318579626303300478337561813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424772835071067304450082417 318579626303300478337561813)
            ·
              refine ⟨7466709991483604961036605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 318579626303300478337561813 7466709991483604961036605)
              ·
                refine ⟨2800016246806351860388727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7466709991483604961036605 2800016246806351860388727)
                ·
                  refine ⟨4200024370209527790583091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800016246806351860388727 4200024370209527790583091)
                  ·
                    refine ⟨6300036555314291685874637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200024370209527790583091 6300036555314291685874637)
                    ·
                      refine ⟨2362513708242859382202989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300036555314291685874637 2362513708242859382202989)
                      ·
                        rfl

theorem cell23_4600979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 1, 3].length) (baseStart_4600979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4600979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4600979 prefixEnd_4600979 := by exact prefixLift 4600979
  have htrace : WordTrace (prefixWord ++ tailWord_4600979) baseStart_4600979 baseEnd_4600979 := by
    simpa [prefixWord, tailWord_4600979, baseEnd_4600979] using wordTrace_append hprefix tailTrace_4600979
  have hstable : (prefixWord ++ tailWord_4600979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4600979).length < 2 ^ (prefixWord ++ tailWord_4600979).sum := by decide
  have hdescent : baseEnd_4600979 < baseStart_4600979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4600979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601015 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_4601015 : Nat := 118140960795 + 4601015 * 2 ^ 59
def prefixEnd_4601015 : Nat := 4983230072969 + 3 ^ 40 * 4601015 * 2
def baseEnd_4601015 : Nat := 2362532193546421241352823

theorem tailTrace_4601015 : CollatzResearch.WordTrace tailWord_4601015 prefixEnd_4601015 2362532193546421241352823 := by
  unfold tailWord_4601015
  simp only [CollatzResearch.WordTrace]
  refine ⟨167812803426315920647108499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111875202284210613764738999 167812803426315920647108499)
  ·
    refine ⟨251719205139473880970662749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167812803426315920647108499 251719205139473880970662749)
    ·
      refine ⟨94394701927302705363998531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251719205139473880970662749 94394701927302705363998531)
      ·
        refine ⟨141592052890954058045997797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94394701927302705363998531 141592052890954058045997797)
        ·
          refine ⟨26548509917053885883624587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141592052890954058045997797 26548509917053885883624587)
          ·
            refine ⟨39822764875580828825436881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26548509917053885883624587 39822764875580828825436881)
            ·
              refine ⟨29867073656685621619077661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39822764875580828825436881 29867073656685621619077661)
              ·
                refine ⟨11200152621257108107154123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29867073656685621619077661 11200152621257108107154123)
                ·
                  refine ⟨16800228931885662160731185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11200152621257108107154123 16800228931885662160731185)
                  ·
                    refine ⟨12600171698914246620548389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16800228931885662160731185 12600171698914246620548389)
                    ·
                      refine ⟨2362532193546421241352823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12600171698914246620548389 2362532193546421241352823)
                      ·
                        rfl

theorem cell23_4601015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_4601015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601015 prefixEnd_4601015 := by exact prefixLift 4601015
  have htrace : WordTrace (prefixWord ++ tailWord_4601015) baseStart_4601015 baseEnd_4601015 := by
    simpa [prefixWord, tailWord_4601015, baseEnd_4601015] using wordTrace_append hprefix tailTrace_4601015
  have hstable : (prefixWord ++ tailWord_4601015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601015).length < 2 ^ (prefixWord ++ tailWord_4601015).sum := by decide
  have hdescent : baseEnd_4601015 < baseStart_4601015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601069 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4601069 : Nat := 118140960795 + 4601069 * 2 ^ 59
def prefixEnd_4601069 : Nat := 4983230072969 + 3 ^ 40 * 4601069 * 2
def baseEnd_4601069 : Nat := 2362559921501764030077575

theorem tailTrace_4601069 : CollatzResearch.WordTrace tailWord_4601069 prefixEnd_4601069 2362559921501764030077575 := by
  unfold tailWord_4601069
  simp only [CollatzResearch.WordTrace]
  refine ⟨167814772968120287869574261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111876515312080191913049507 167814772968120287869574261)
  ·
    refine ⟨15732634965761276987772587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167814772968120287869574261 15732634965761276987772587)
    ·
      refine ⟨23598952448641915481658881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15732634965761276987772587 23598952448641915481658881)
      ·
        refine ⟨17699214336481436611244161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23598952448641915481658881 17699214336481436611244161)
        ·
          refine ⟨13274410752361077458433121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17699214336481436611244161 13274410752361077458433121)
          ·
            refine ⟨9955808064270808093824841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13274410752361077458433121 9955808064270808093824841)
            ·
              refine ⟨7466856048203106070368631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9955808064270808093824841 7466856048203106070368631)
              ·
                refine ⟨11200284072304659105552947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7466856048203106070368631 11200284072304659105552947)
                ·
                  refine ⟨16800426108456988658329421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11200284072304659105552947 16800426108456988658329421)
                  ·
                    refine ⟨6300159790671370746873533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16800426108456988658329421 6300159790671370746873533)
                    ·
                      refine ⟨2362559921501764030077575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300159790671370746873533 2362559921501764030077575)
                      ·
                        rfl

theorem cell23_4601069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4601069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601069 prefixEnd_4601069 := by exact prefixLift 4601069
  have htrace : WordTrace (prefixWord ++ tailWord_4601069) baseStart_4601069 baseEnd_4601069 := by
    simpa [prefixWord, tailWord_4601069, baseEnd_4601069] using wordTrace_append hprefix tailTrace_4601069
  have hstable : (prefixWord ++ tailWord_4601069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601069).length < 2 ^ (prefixWord ++ tailWord_4601069).sum := by decide
  have hdescent : baseEnd_4601069 < baseStart_4601069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601090 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_4601090 : Nat := 118140960795 + 4601090 * 2 ^ 59
def prefixEnd_4601090 : Nat := 4983230072969 + 3 ^ 40 * 4601090 * 2
def baseEnd_4601090 : Nat := 2362570704595508447914979

theorem tailTrace_4601090 : CollatzResearch.WordTrace tailWord_4601090 prefixEnd_4601090 2362570704595508447914979 := by
  unfold tailWord_4601090
  simp only [CollatzResearch.WordTrace]
  refine ⟨41953884725261052114022181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111877025934029472304059149 41953884725261052114022181)
  ·
    refine ⟨7866353385986447271379159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41953884725261052114022181 7866353385986447271379159)
    ·
      refine ⟨11799530078979670907068739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7866353385986447271379159 11799530078979670907068739)
      ·
        refine ⟨17699295118469506360603109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11799530078979670907068739 17699295118469506360603109)
        ·
          refine ⟨3318617834713032442613083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17699295118469506360603109 3318617834713032442613083)
          ·
            refine ⟨4977926752069548663919625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318617834713032442613083 4977926752069548663919625)
            ·
              refine ⟨3733445064052161497939719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977926752069548663919625 3733445064052161497939719)
              ·
                refine ⟨5600167596078242246909579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733445064052161497939719 5600167596078242246909579)
                ·
                  refine ⟨8400251394117363370364369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600167596078242246909579 8400251394117363370364369)
                  ·
                    refine ⟨6300188545588022527773277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8400251394117363370364369 6300188545588022527773277)
                    ·
                      refine ⟨2362570704595508447914979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300188545588022527773277 2362570704595508447914979)
                      ·
                        rfl

theorem cell23_4601090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_4601090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601090 prefixEnd_4601090 := by exact prefixLift 4601090
  have htrace : WordTrace (prefixWord ++ tailWord_4601090) baseStart_4601090 baseEnd_4601090 := by
    simpa [prefixWord, tailWord_4601090, baseEnd_4601090] using wordTrace_append hprefix tailTrace_4601090
  have hstable : (prefixWord ++ tailWord_4601090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601090).length < 2 ^ (prefixWord ++ tailWord_4601090).sum := by decide
  have hdescent : baseEnd_4601090 < baseStart_4601090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601096 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_4601096 : Nat := 118140960795 + 4601096 * 2 ^ 59
def prefixEnd_4601096 : Nat := 4983230072969 + 3 ^ 40 * 4601096 * 2
def baseEnd_4601096 : Nat := 2362573785479435424439951

theorem tailTrace_4601096 : CollatzResearch.WordTrace tailWord_4601096 prefixEnd_4601096 2362573785479435424439951 := by
  unfold tailWord_4601096
  simp only [CollatzResearch.WordTrace]
  refine ⟨83907878869511235740403571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111877171826014980987204761 83907878869511235740403571)
  ·
    refine ⟨125861818304266853610605357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83907878869511235740403571 125861818304266853610605357)
    ·
      refine ⟨47198181864100070103977009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125861818304266853610605357 47198181864100070103977009)
      ·
        refine ⟨35398636398075052577982757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47198181864100070103977009 35398636398075052577982757)
        ·
          refine ⟨6637244324639072358371767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35398636398075052577982757 6637244324639072358371767)
          ·
            refine ⟨9955866486958608537557651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637244324639072358371767 9955866486958608537557651)
            ·
              refine ⟨14933799730437912806336477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9955866486958608537557651 14933799730437912806336477)
              ·
                refine ⟨5600174898914217302376179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14933799730437912806336477 5600174898914217302376179)
                ·
                  refine ⟨8400262348371325953564269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600174898914217302376179 8400262348371325953564269)
                  ·
                    refine ⟨3150098380639247232586601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8400262348371325953564269 3150098380639247232586601)
                    ·
                      refine ⟨2362573785479435424439951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150098380639247232586601 2362573785479435424439951)
                      ·
                        rfl

theorem cell23_4601096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_4601096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601096 prefixEnd_4601096 := by exact prefixLift 4601096
  have htrace : WordTrace (prefixWord ++ tailWord_4601096) baseStart_4601096 baseEnd_4601096 := by
    simpa [prefixWord, tailWord_4601096, baseEnd_4601096] using wordTrace_append hprefix tailTrace_4601096
  have hstable : (prefixWord ++ tailWord_4601096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601096).length < 2 ^ (prefixWord ++ tailWord_4601096).sum := by decide
  have hdescent : baseEnd_4601096 < baseStart_4601096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601105 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_4601105 : Nat := 118140960795 + 4601105 * 2 ^ 59
def prefixEnd_4601105 : Nat := 4983230072969 + 3 ^ 40 * 4601105 * 2
def baseEnd_4601105 : Nat := 2362578406805325889227409

theorem tailTrace_4601105 : CollatzResearch.WordTrace tailWord_4601105 prefixEnd_4601105 2362578406805325889227409 := by
  unfold tailWord_4601105
  simp only [CollatzResearch.WordTrace]
  refine ⟨167816085995989866017884769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111877390663993244011923179 167816085995989866017884769)
  ·
    refine ⟨125862064496992399513413577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167816085995989866017884769 125862064496992399513413577)
    ·
      refine ⟨94396548372744299635060183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125862064496992399513413577 94396548372744299635060183)
      ·
        refine ⟨141594822559116449452590275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94396548372744299635060183 141594822559116449452590275)
        ·
          refine ⟨212392233838674674178885413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141594822559116449452590275 212392233838674674178885413)
          ·
            refine ⟨39823543844751501408541015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212392233838674674178885413 39823543844751501408541015)
            ·
              refine ⟨59735315767127252112811523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39823543844751501408541015 59735315767127252112811523)
              ·
                refine ⟨89602973650690878169217285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59735315767127252112811523 89602973650690878169217285)
                ·
                  refine ⟨16800557559504539656728241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89602973650690878169217285 16800557559504539656728241)
                  ·
                    refine ⟨12600418169628404742546181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16800557559504539656728241 12600418169628404742546181)
                    ·
                      refine ⟨2362578406805325889227409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12600418169628404742546181 2362578406805325889227409)
                      ·
                        rfl

theorem cell23_4601105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_4601105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601105 prefixEnd_4601105 := by exact prefixLift 4601105
  have htrace : WordTrace (prefixWord ++ tailWord_4601105) baseStart_4601105 baseEnd_4601105 := by
    simpa [prefixWord, tailWord_4601105, baseEnd_4601105] using wordTrace_append hprefix tailTrace_4601105
  have hstable : (prefixWord ++ tailWord_4601105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601105).length < 2 ^ (prefixWord ++ tailWord_4601105).sum := by decide
  have hdescent : baseEnd_4601105 < baseStart_4601105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601155 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_4601155 : Nat := 118140960795 + 4601155 * 2 ^ 59
def prefixEnd_4601155 : Nat := 4983230072969 + 3 ^ 40 * 4601155 * 2
def baseEnd_4601155 : Nat := 2362604080838050693602179

theorem tailTrace_4601155 : CollatzResearch.WordTrace tailWord_4601155 prefixEnd_4601155 2362604080838050693602179 := by
  unfold tailWord_4601155
  simp only [CollatzResearch.WordTrace]
  refine ⟨167817909645808724557204919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111878606430539149704803279 167817909645808724557204919)
  ·
    refine ⟨251726864468713086835807379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167817909645808724557204919 251726864468713086835807379)
    ·
      refine ⟨377590296703069630253711069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251726864468713086835807379 377590296703069630253711069)
      ·
        refine ⟨141596361263651111345141651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377590296703069630253711069 141596361263651111345141651)
        ·
          refine ⟨212394541895476667017712477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141596361263651111345141651 212394541895476667017712477)
          ·
            refine ⟨79647953210803750131642179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212394541895476667017712477 79647953210803750131642179)
            ·
              refine ⟨119471929816205625197463269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79647953210803750131642179 119471929816205625197463269)
              ·
                refine ⟨22400986840538554724524363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119471929816205625197463269 22400986840538554724524363)
                ·
                  refine ⟨33601480260807832086786545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22400986840538554724524363 33601480260807832086786545)
                  ·
                    refine ⟨25201110195605874065089909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33601480260807832086786545 25201110195605874065089909)
                    ·
                      refine ⟨2362604080838050693602179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25201110195605874065089909 2362604080838050693602179)
                      ·
                        rfl

theorem cell23_4601155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_4601155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601155 prefixEnd_4601155 := by exact prefixLift 4601155
  have htrace : WordTrace (prefixWord ++ tailWord_4601155) baseStart_4601155 baseEnd_4601155 := by
    simpa [prefixWord, tailWord_4601155, baseEnd_4601155] using wordTrace_append hprefix tailTrace_4601155
  have hstable : (prefixWord ++ tailWord_4601155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601155).length < 2 ^ (prefixWord ++ tailWord_4601155).sum := by decide
  have hdescent : baseEnd_4601155 < baseStart_4601155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601172 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4601172 : Nat := 118140960795 + 4601172 * 2 ^ 59
def prefixEnd_4601172 : Nat := 4983230072969 + 3 ^ 40 * 4601172 * 2
def baseEnd_4601172 : Nat := 2362612810009177127089601

theorem tailTrace_4601172 : CollatzResearch.WordTrace tailWord_4601172 prefixEnd_4601172 2362612810009177127089601 := by
  unfold tailWord_4601172
  simp only [CollatzResearch.WordTrace]
  refine ⟨83909264843373568230286885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111879019791164757640382513 83909264843373568230286885)
  ·
    refine ⟨15732987158132544043178791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83909264843373568230286885 15732987158132544043178791)
    ·
      refine ⟨23599480737198816064768187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15732987158132544043178791 23599480737198816064768187)
      ·
        refine ⟨35399221105798224097152281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23599480737198816064768187 35399221105798224097152281)
        ·
          refine ⟨26549415829348668072864211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35399221105798224097152281 26549415829348668072864211)
          ·
            refine ⟨39824123744023002109296317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26549415829348668072864211 39824123744023002109296317)
            ·
              refine ⟨14934046404008625790986119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39824123744023002109296317 14934046404008625790986119)
              ·
                refine ⟨22401069606012938686479179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14934046404008625790986119 22401069606012938686479179)
                ·
                  refine ⟨33601604409019408029718769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22401069606012938686479179 33601604409019408029718769)
                  ·
                    refine ⟨25201203306764556022289077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33601604409019408029718769 25201203306764556022289077)
                    ·
                      refine ⟨2362612810009177127089601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25201203306764556022289077 2362612810009177127089601)
                      ·
                        rfl

theorem cell23_4601172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4601172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601172 prefixEnd_4601172 := by exact prefixLift 4601172
  have htrace : WordTrace (prefixWord ++ tailWord_4601172) baseStart_4601172 baseEnd_4601172 := by
    simpa [prefixWord, tailWord_4601172, baseEnd_4601172] using wordTrace_append hprefix tailTrace_4601172
  have hstable : (prefixWord ++ tailWord_4601172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601172).length < 2 ^ (prefixWord ++ tailWord_4601172).sum := by decide
  have hdescent : baseEnd_4601172 < baseStart_4601172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601185 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4601185 : Nat := 118140960795 + 4601185 * 2 ^ 59
def prefixEnd_4601185 : Nat := 4983230072969 + 3 ^ 40 * 4601185 * 2
def baseEnd_4601185 : Nat := 2362619485257685576227041

theorem tailTrace_4601185 : CollatzResearch.WordTrace tailWord_4601185 prefixEnd_4601185 2362619485257685576227041 := by
  unfold tailWord_4601185
  simp only [CollatzResearch.WordTrace]
  refine ⟨167819003835700039680797009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111879335890466693120531339 167819003835700039680797009)
  ·
    refine ⟨125864252876775029760597757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167819003835700039680797009 125864252876775029760597757)
    ·
      refine ⟨47199094828790636160224159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125864252876775029760597757 47199094828790636160224159)
      ·
        refine ⟨70798642243185954240336239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47199094828790636160224159 70798642243185954240336239)
        ·
          refine ⟨106197963364778931360504359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70798642243185954240336239 106197963364778931360504359)
          ·
            refine ⟨159296945047168397040756539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106197963364778931360504359 159296945047168397040756539)
            ·
              refine ⟨238945417570752595561134809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159296945047168397040756539 238945417570752595561134809)
              ·
                refine ⟨179209063178064446670851107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238945417570752595561134809 179209063178064446670851107)
                ·
                  refine ⟨268813594767096670006276661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179209063178064446670851107 268813594767096670006276661)
                  ·
                    refine ⟨25201274509415312813088437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 268813594767096670006276661 25201274509415312813088437)
                    ·
                      refine ⟨2362619485257685576227041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25201274509415312813088437 2362619485257685576227041)
                      ·
                        rfl

theorem cell23_4601185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4601185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601185 prefixEnd_4601185 := by exact prefixLift 4601185
  have htrace : WordTrace (prefixWord ++ tailWord_4601185) baseStart_4601185 baseEnd_4601185 := by
    simpa [prefixWord, tailWord_4601185, baseEnd_4601185] using wordTrace_append hprefix tailTrace_4601185
  have hstable : (prefixWord ++ tailWord_4601185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601185).length < 2 ^ (prefixWord ++ tailWord_4601185).sum := by decide
  have hdescent : baseEnd_4601185 < baseStart_4601185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601219 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3]
def baseStart_4601219 : Nat := 118140960795 + 4601219 * 2 ^ 59
def prefixEnd_4601219 : Nat := 4983230072969 + 3 ^ 40 * 4601219 * 2
def baseEnd_4601219 : Nat := 2362636943599938443201885

theorem tailTrace_4601219 : CollatzResearch.WordTrace tailWord_4601219 prefixEnd_4601219 2362636943599938443201885 := by
  unfold tailWord_4601219
  simp only [CollatzResearch.WordTrace]
  refine ⟨167820243917576863487534711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111880162611717908991689807 167820243917576863487534711)
  ·
    refine ⟨251730365876365295231302067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167820243917576863487534711 251730365876365295231302067)
    ·
      refine ⟨377595548814547942846953101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251730365876365295231302067 377595548814547942846953101)
      ·
        refine ⟨141598330805455478567607413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377595548814547942846953101 141598330805455478567607413)
        ·
          refine ⟨13274843513011451115713195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141598330805455478567607413 13274843513011451115713195)
          ·
            refine ⟨19912265269517176673569793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13274843513011451115713195 19912265269517176673569793)
            ·
              refine ⟨14934198952137882505177345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19912265269517176673569793 14934198952137882505177345)
              ·
                refine ⟨11200649214103411878883009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14934198952137882505177345 11200649214103411878883009)
                ·
                  refine ⟨8400486910577558909162257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11200649214103411878883009 8400486910577558909162257)
                  ·
                    refine ⟨6300365182933169181871693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8400486910577558909162257 6300365182933169181871693)
                    ·
                      refine ⟨2362636943599938443201885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300365182933169181871693 2362636943599938443201885)
                      ·
                        rfl

theorem cell23_4601219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_4601219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601219 prefixEnd_4601219 := by exact prefixLift 4601219
  have htrace : WordTrace (prefixWord ++ tailWord_4601219) baseStart_4601219 baseEnd_4601219 := by
    simpa [prefixWord, tailWord_4601219, baseEnd_4601219] using wordTrace_append hprefix tailTrace_4601219
  have hstable : (prefixWord ++ tailWord_4601219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601219).length < 2 ^ (prefixWord ++ tailWord_4601219).sum := by decide
  have hdescent : baseEnd_4601219 < baseStart_4601219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601306 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_4601306 : Nat := 118140960795 + 4601306 * 2 ^ 59
def prefixEnd_4601306 : Nat := 4983230072969 + 3 ^ 40 * 4601306 * 2
def baseEnd_4601306 : Nat := 2362681616416879602813985

theorem tailTrace_4601306 : CollatzResearch.WordTrace tailWord_4601306 prefixEnd_4601306 2362681616416879602813985 := by
  unfold tailWord_4601306
  simp only [CollatzResearch.WordTrace]
  refine ⟨41955854267065419336487943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111882278045507784897301181 41955854267065419336487943)
  ·
    refine ⟨62933781400598129004731915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41955854267065419336487943 62933781400598129004731915)
    ·
      refine ⟨94400672100897193507097873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62933781400598129004731915 94400672100897193507097873)
      ·
        refine ⟨70800504075672895130323405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94400672100897193507097873 70800504075672895130323405)
        ·
          refine ⟨26550189028377335673871277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70800504075672895130323405 26550189028377335673871277)
          ·
            refine ⟨9956320885641500877701729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26550189028377335673871277 9956320885641500877701729)
            ·
              refine ⟨7467240664231125658276297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9956320885641500877701729 7467240664231125658276297)
              ·
                refine ⟨5600430498173344243707223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467240664231125658276297 5600430498173344243707223)
                ·
                  refine ⟨8400645747260016365560835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600430498173344243707223 8400645747260016365560835)
                  ·
                    refine ⟨12600968620890024548341253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8400645747260016365560835 12600968620890024548341253)
                    ·
                      refine ⟨2362681616416879602813985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12600968620890024548341253 2362681616416879602813985)
                      ·
                        rfl

theorem cell23_4601306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_4601306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601306 prefixEnd_4601306 := by exact prefixLift 4601306
  have htrace : WordTrace (prefixWord ++ tailWord_4601306) baseStart_4601306 baseEnd_4601306 := by
    simpa [prefixWord, tailWord_4601306, baseEnd_4601306] using wordTrace_append hprefix tailTrace_4601306
  have hstable : (prefixWord ++ tailWord_4601306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601306).length < 2 ^ (prefixWord ++ tailWord_4601306).sum := by decide
  have hdescent : baseEnd_4601306 < baseStart_4601306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601323 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 1, 2, 2]
def baseStart_4601323 : Nat := 118140960795 + 4601323 * 2 ^ 59
def prefixEnd_4601323 : Nat := 4983230072969 + 3 ^ 40 * 4601323 * 2
def baseEnd_4601323 : Nat := 2362690345588006036301407

theorem tailTrace_4601323 : CollatzResearch.WordTrace tailWord_4601323 prefixEnd_4601323 2362690345588006036301407 := by
  unfold tailWord_4601323
  simp only [CollatzResearch.WordTrace]
  refine ⟨167824037109200089249320623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111882691406133392832880415 167824037109200089249320623)
  ·
    refine ⟨251736055663800133873980935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167824037109200089249320623 251736055663800133873980935)
    ·
      refine ⟨377604083495700200810971403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251736055663800133873980935 377604083495700200810971403)
      ·
        refine ⟨566406125243550301216457105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377604083495700200810971403 566406125243550301216457105)
        ·
          refine ⟨424804593932662725912342829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566406125243550301216457105 424804593932662725912342829)
          ·
            refine ⟨159301722724748522217128561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424804593932662725912342829 159301722724748522217128561)
            ·
              refine ⟨119476292043561391662846421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159301722724748522217128561 119476292043561391662846421)
              ·
                refine ⟨2800225594770970117097963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119476292043561391662846421 2800225594770970117097963)
                ·
                  refine ⟨4200338392156455175646945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800225594770970117097963 4200338392156455175646945)
                  ·
                    refine ⟨3150253794117341381735209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200338392156455175646945 3150253794117341381735209)
                    ·
                      refine ⟨2362690345588006036301407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150253794117341381735209 2362690345588006036301407)
                      ·
                        rfl

theorem cell23_4601323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 2, 2].length) (baseStart_4601323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601323 prefixEnd_4601323 := by exact prefixLift 4601323
  have htrace : WordTrace (prefixWord ++ tailWord_4601323) baseStart_4601323 baseEnd_4601323 := by
    simpa [prefixWord, tailWord_4601323, baseEnd_4601323] using wordTrace_append hprefix tailTrace_4601323
  have hstable : (prefixWord ++ tailWord_4601323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601323).length < 2 ^ (prefixWord ++ tailWord_4601323).sum := by decide
  have hdescent : baseEnd_4601323 < baseStart_4601323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601326 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4601326 : Nat := 118140960795 + 4601326 * 2 ^ 59
def prefixEnd_4601326 : Nat := 4983230072969 + 3 ^ 40 * 4601326 * 2
def baseEnd_4601326 : Nat := 2362691886029969524563893

theorem tailTrace_4601326 : CollatzResearch.WordTrace tailWord_4601326 prefixEnd_4601326 2362691886029969524563893 := by
  unfold tailWord_4601326
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978018316023652595209979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111882764352126147174453221 20978018316023652595209979)
  ·
    refine ⟨31467027474035478892814969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20978018316023652595209979 31467027474035478892814969)
    ·
      refine ⟨23600270605526609169611227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31467027474035478892814969 23600270605526609169611227)
      ·
        refine ⟨35400405908289913754416841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23600270605526609169611227 35400405908289913754416841)
        ·
          refine ⟨26550304431217435315812631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35400405908289913754416841 26550304431217435315812631)
          ·
            refine ⟨39825456646826152973718947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26550304431217435315812631 39825456646826152973718947)
            ·
              refine ⟨59738184970239229460578421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39825456646826152973718947 59738184970239229460578421)
              ·
                refine ⟨5600454840959927761929227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59738184970239229460578421 5600454840959927761929227)
                ·
                  refine ⟨8400682261439891642893841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600454840959927761929227 8400682261439891642893841)
                  ·
                    refine ⟨6300511696079918732170381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8400682261439891642893841 6300511696079918732170381)
                    ·
                      refine ⟨2362691886029969524563893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300511696079918732170381 2362691886029969524563893)
                      ·
                        rfl

theorem cell23_4601326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4601326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601326 prefixEnd_4601326 := by exact prefixLift 4601326
  have htrace : WordTrace (prefixWord ++ tailWord_4601326) baseStart_4601326 baseEnd_4601326 := by
    simpa [prefixWord, tailWord_4601326, baseEnd_4601326] using wordTrace_append hprefix tailTrace_4601326
  have hstable : (prefixWord ++ tailWord_4601326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601326).length < 2 ^ (prefixWord ++ tailWord_4601326).sum := by decide
  have hdescent : baseEnd_4601326 < baseStart_4601326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601346 : List Nat := [3, 4, 1, 2, 1, 2, 2, 8]
def baseStart_4601346 : Nat := 118140960795 + 4601346 * 2 ^ 59
def prefixEnd_4601346 : Nat := 4983230072969 + 3 ^ 40 * 4601346 * 2
def baseEnd_4601346 : Nat := 87507487246039238752363

theorem tailTrace_4601346 : CollatzResearch.WordTrace tailWord_4601346 prefixEnd_4601346 87507487246039238752363 := by
  unfold tailWord_4601346
  simp only [CollatzResearch.WordTrace]
  refine ⟨41956218997029191044351973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111883250658744509451605261 41956218997029191044351973)
  ·
    refine ⟨7866791061942973320815995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41956218997029191044351973 7866791061942973320815995)
    ·
      refine ⟨11800186592914459981223993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7866791061942973320815995 11800186592914459981223993)
      ·
        refine ⟨8850139944685844985917995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11800186592914459981223993 8850139944685844985917995)
        ·
          refine ⟨13275209917028767478876993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8850139944685844985917995 13275209917028767478876993)
          ·
            refine ⟨9956407437771575609157745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13275209917028767478876993 9956407437771575609157745)
            ·
              refine ⟨7467305578328681706868309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9956407437771575609157745 7467305578328681706868309)
              ·
                refine ⟨87507487246039238752363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7467305578328681706868309 87507487246039238752363)
                ·
                  rfl

theorem cell23_4601346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_4601346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601346 prefixEnd_4601346 := by exact prefixLift 4601346
  have htrace : WordTrace (prefixWord ++ tailWord_4601346) baseStart_4601346 baseEnd_4601346 := by
    simpa [prefixWord, tailWord_4601346, baseEnd_4601346] using wordTrace_append hprefix tailTrace_4601346
  have hstable : (prefixWord ++ tailWord_4601346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601346).length < 2 ^ (prefixWord ++ tailWord_4601346).sum := by decide
  have hdescent : baseEnd_4601346 < baseStart_4601346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601349 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_4601349 : Nat := 118140960795 + 4601349 * 2 ^ 59
def prefixEnd_4601349 : Nat := 4983230072969 + 3 ^ 40 * 4601349 * 2
def baseEnd_4601349 : Nat := 2362703696085022934576287

theorem tailTrace_4601349 : CollatzResearch.WordTrace tailWord_4601349 prefixEnd_4601349 2362703696085022934576287 := by
  unfold tailWord_4601349
  simp only [CollatzResearch.WordTrace]
  refine ⟨167824985407105895689767101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111883323604737263793178067 167824985407105895689767101)
  ·
    refine ⟨62934369527664710883662663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167824985407105895689767101 62934369527664710883662663)
    ·
      refine ⟨94401554291497066325493995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62934369527664710883662663 94401554291497066325493995)
      ·
        refine ⟨141602331437245599488240993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94401554291497066325493995 141602331437245599488240993)
        ·
          refine ⟨106201748577934199616180745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141602331437245599488240993 106201748577934199616180745)
          ·
            refine ⟨79651311433450649712135559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106201748577934199616180745 79651311433450649712135559)
            ·
              refine ⟨119476967150175974568203339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79651311433450649712135559 119476967150175974568203339)
              ·
                refine ⟨179215450725263961852305009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119476967150175974568203339 179215450725263961852305009)
                ·
                  refine ⟨134411588043947971389228757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179215450725263961852305009 134411588043947971389228757)
                  ·
                    refine ⟨3150271594780030579435049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134411588043947971389228757 3150271594780030579435049)
                    ·
                      refine ⟨2362703696085022934576287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150271594780030579435049 2362703696085022934576287)
                      ·
                        rfl

theorem cell23_4601349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_4601349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601349 prefixEnd_4601349 := by exact prefixLift 4601349
  have htrace : WordTrace (prefixWord ++ tailWord_4601349) baseStart_4601349 baseEnd_4601349 := by
    simpa [prefixWord, tailWord_4601349, baseEnd_4601349] using wordTrace_append hprefix tailTrace_4601349
  have hstable : (prefixWord ++ tailWord_4601349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601349).length < 2 ^ (prefixWord ++ tailWord_4601349).sum := by decide
  have hdescent : baseEnd_4601349 < baseStart_4601349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601357 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4601357 : Nat := 118140960795 + 4601357 * 2 ^ 59
def prefixEnd_4601357 : Nat := 4983230072969 + 3 ^ 40 * 4601357 * 2
def baseEnd_4601357 : Nat := 2362707803930258903276251

theorem tailTrace_4601357 : CollatzResearch.WordTrace tailWord_4601357 prefixEnd_4601357 2362707803930258903276251 := by
  unfold tailWord_4601357
  simp only [CollatzResearch.WordTrace]
  refine ⟨167825277191076913056058325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111883518127384608704038883 167825277191076913056058325)
  ·
    refine ⟨3933404934165865149751367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 167825277191076913056058325 3933404934165865149751367)
    ·
      refine ⟨5900107401248797724627051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933404934165865149751367 5900107401248797724627051)
      ·
        refine ⟨8850161101873196586940577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900107401248797724627051 8850161101873196586940577)
        ·
          refine ⟨6637620826404897440205433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8850161101873196586940577 6637620826404897440205433)
          ·
            refine ⟨4978215619803673080154075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6637620826404897440205433 4978215619803673080154075)
            ·
              refine ⟨7467323429705509620231113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978215619803673080154075 7467323429705509620231113)
              ·
                refine ⟨5600492572279132215173335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467323429705509620231113 5600492572279132215173335)
                ·
                  refine ⟨8400738858418698322760003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600492572279132215173335 8400738858418698322760003)
                  ·
                    refine ⟨12601108287628047484140005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8400738858418698322760003 12601108287628047484140005)
                    ·
                      refine ⟨2362707803930258903276251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12601108287628047484140005 2362707803930258903276251)
                      ·
                        rfl

theorem cell23_4601357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4601357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601357 prefixEnd_4601357 := by exact prefixLift 4601357
  have htrace : WordTrace (prefixWord ++ tailWord_4601357) baseStart_4601357 baseEnd_4601357 := by
    simpa [prefixWord, tailWord_4601357, baseEnd_4601357] using wordTrace_append hprefix tailTrace_4601357
  have hstable : (prefixWord ++ tailWord_4601357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601357).length < 2 ^ (prefixWord ++ tailWord_4601357).sum := by decide
  have hdescent : baseEnd_4601357 < baseStart_4601357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601374 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4601374 : Nat := 118140960795 + 4601374 * 2 ^ 59
def prefixEnd_4601374 : Nat := 4983230072969 + 3 ^ 40 * 4601374 * 2
def baseEnd_4601374 : Nat := 2362716533101385336763673

theorem tailTrace_4601374 : CollatzResearch.WordTrace tailWord_4601374 prefixEnd_4601374 2362716533101385336763673 := by
  unfold tailWord_4601374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978237154001915619928397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111883931488010216639618117 20978237154001915619928397)
  ·
    refine ⟨7866838932750718357473149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20978237154001915619928397 7866838932750718357473149)
    ·
      refine ⟨2950064599781519384052431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7866838932750718357473149 2950064599781519384052431)
      ·
        refine ⟨4425096899672279076078647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2950064599781519384052431 4425096899672279076078647)
        ·
          refine ⟨6637645349508418614117971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425096899672279076078647 6637645349508418614117971)
          ·
            refine ⟨9956468024262627921176957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637645349508418614117971 9956468024262627921176957)
            ·
              refine ⟨3733675509098485470441359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9956468024262627921176957 3733675509098485470441359)
              ·
                refine ⟨5600513263647728205662039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733675509098485470441359 5600513263647728205662039)
                ·
                  refine ⟨8400769895471592308493059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600513263647728205662039 8400769895471592308493059)
                  ·
                    refine ⟨12601154843207388462739589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8400769895471592308493059 12601154843207388462739589)
                    ·
                      refine ⟨2362716533101385336763673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12601154843207388462739589 2362716533101385336763673)
                      ·
                        rfl

theorem cell23_4601374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4601374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601374 prefixEnd_4601374 := by exact prefixLift 4601374
  have htrace : WordTrace (prefixWord ++ tailWord_4601374) baseStart_4601374 baseEnd_4601374 := by
    simpa [prefixWord, tailWord_4601374, baseEnd_4601374] using wordTrace_append hprefix tailTrace_4601374
  have hstable : (prefixWord ++ tailWord_4601374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601374).length < 2 ^ (prefixWord ++ tailWord_4601374).sum := by decide
  have hdescent : baseEnd_4601374 < baseStart_4601374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
