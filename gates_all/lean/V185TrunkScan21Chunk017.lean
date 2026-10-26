import V185TrunkScan21Chunk016

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_206109 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 4]
def baseStart_206109 : Nat := 118140960795 + 206109 * 2 ^ 59
def prefixEnd_206109 : Nat := 4983230072969 + 3 ^ 40 * 206109 * 2
def baseEnd_206109 : Nat := 47036881874506369462057

theorem tailTrace_206109 : CollatzResearch.WordTrace tailWord_206109 prefixEnd_206109 47036881874506369462057 := by
  unfold tailWord_206109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517412810309768459845381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5011608540206512306563587 7517412810309768459845381)
  ·
    refine ⟨1409514901933081586221009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7517412810309768459845381 1409514901933081586221009)
    ·
      refine ⟨1057136176449811189665757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1409514901933081586221009 1057136176449811189665757)
      ·
        refine ⟨396426066168679196124659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1057136176449811189665757 396426066168679196124659)
        ·
          refine ⟨594639099253018794186989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396426066168679196124659 594639099253018794186989)
          ·
            refine ⟨222989662219882047820121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 594639099253018794186989 222989662219882047820121)
            ·
              refine ⟨167242246664911535865091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222989662219882047820121 167242246664911535865091)
              ·
                refine ⟨250863369997367303797637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167242246664911535865091 250863369997367303797637)
                ·
                  refine ⟨47036881874506369462057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250863369997367303797637 47036881874506369462057)
                  ·
                    rfl

theorem cell21_206109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_206109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206109 prefixEnd_206109 := by exact prefixLift 206109
  have htrace : WordTrace (prefixWord ++ tailWord_206109) baseStart_206109 baseEnd_206109 := by
    simpa [prefixWord, tailWord_206109, baseEnd_206109] using wordTrace_append hprefix tailTrace_206109
  have hstable : (prefixWord ++ tailWord_206109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206109).length < 2 ^ (prefixWord ++ tailWord_206109).sum := by decide
  have hdescent : baseEnd_206109 < baseStart_206109 := by decide
  rcases family_descends (prefixWord ++ tailWord_206109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206151 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_206151 : Nat := 118140960795 + 206151 * 2 ^ 59
def prefixEnd_206151 : Nat := 4983230072969 + 3 ^ 40 * 206151 * 2
def baseEnd_206151 : Nat := 47046466846723629761971

theorem tailTrace_206151 : CollatzResearch.WordTrace tailWord_206151 prefixEnd_206151 47046466846723629761971 := by
  unfold tailWord_206151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7518944676157609632874307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5012629784105073088582871 7518944676157609632874307)
  ·
    refine ⟨11278417014236414449311461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7518944676157609632874307 11278417014236414449311461)
    ·
      refine ⟨2114703190169327709245899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11278417014236414449311461 2114703190169327709245899)
      ·
        refine ⟨3172054785253991563868849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114703190169327709245899 3172054785253991563868849)
        ·
          refine ⟨2379041088940493672901637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172054785253991563868849 2379041088940493672901637)
          ·
            refine ⟨446070204176342563669057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2379041088940493672901637 446070204176342563669057)
            ·
              refine ⟨334552653132256922751793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446070204176342563669057 334552653132256922751793)
              ·
                refine ⟨250914489849192692063845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334552653132256922751793 250914489849192692063845)
                ·
                  refine ⟨47046466846723629761971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250914489849192692063845 47046466846723629761971)
                  ·
                    rfl

theorem cell21_206151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_206151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206151 prefixEnd_206151 := by exact prefixLift 206151
  have htrace : WordTrace (prefixWord ++ tailWord_206151) baseStart_206151 baseEnd_206151 := by
    simpa [prefixWord, tailWord_206151, baseEnd_206151] using wordTrace_append hprefix tailTrace_206151
  have hstable : (prefixWord ++ tailWord_206151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206151).length < 2 ^ (prefixWord ++ tailWord_206151).sum := by decide
  have hdescent : baseEnd_206151 < baseStart_206151 := by decide
  rcases family_descends (prefixWord ++ tailWord_206151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206165 : List Nat := [1, 3, 2, 2, 3, 1, 3, 6]
def baseStart_206165 : Nat := 118140960795 + 206165 * 2 ^ 59
def prefixEnd_206165 : Nat := 4983230072969 + 3 ^ 40 * 206165 * 2
def baseEnd_206165 : Nat := 15683220612487572176203

theorem tailTrace_206165 : CollatzResearch.WordTrace tailWord_206165 prefixEnd_206165 15683220612487572176203 := by
  unfold tailWord_206165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519455298106890023883949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5012970198737926682589299 7519455298106890023883949)
  ·
    refine ⟨2819795736790083758956481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7519455298106890023883949 2819795736790083758956481)
    ·
      refine ⟨2114846802592562819217361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2819795736790083758956481 2114846802592562819217361)
      ·
        refine ⟨1586135101944422114413021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2114846802592562819217361 1586135101944422114413021)
        ·
          refine ⟨594800663229158292904883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1586135101944422114413021 594800663229158292904883)
          ·
            refine ⟨892200994843737439357325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594800663229158292904883 892200994843737439357325)
            ·
              refine ⟨334575373066401539758997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 892200994843737439357325 334575373066401539758997)
              ·
                refine ⟨15683220612487572176203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 334575373066401539758997 15683220612487572176203)
                ·
                  rfl

theorem cell21_206165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_206165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206165 prefixEnd_206165 := by exact prefixLift 206165
  have htrace : WordTrace (prefixWord ++ tailWord_206165) baseStart_206165 baseEnd_206165 := by
    simpa [prefixWord, tailWord_206165, baseEnd_206165] using wordTrace_append hprefix tailTrace_206165
  have hstable : (prefixWord ++ tailWord_206165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206165).length < 2 ^ (prefixWord ++ tailWord_206165).sum := by decide
  have hdescent : baseEnd_206165 < baseStart_206165 := by decide
  rcases family_descends (prefixWord ++ tailWord_206165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206179 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_206179 : Nat := 118140960795 + 206179 * 2 ^ 59
def prefixEnd_206179 : Nat := 4983230072969 + 3 ^ 40 * 206179 * 2
def baseEnd_206179 : Nat := 47052856828201803295247

theorem tailTrace_206179 : CollatzResearch.WordTrace tailWord_206179 prefixEnd_206179 47052856828201803295247 := by
  unfold tailWord_206179
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519965920056170414893591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5013310613370780276595727 7519965920056170414893591)
  ·
    refine ⟨11279948880084255622340387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7519965920056170414893591 11279948880084255622340387)
    ·
      refine ⟨16919923320126383433510581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279948880084255622340387 16919923320126383433510581)
      ·
        refine ⟨1586242811261848446891617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16919923320126383433510581 1586242811261848446891617)
        ·
          refine ⟨1189682108446386335168713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586242811261848446891617 1189682108446386335168713)
          ·
            refine ⟨892261581334789751376535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189682108446386335168713 892261581334789751376535)
            ·
              refine ⟨1338392372002184627064803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892261581334789751376535 1338392372002184627064803)
              ·
                refine ⟨2007588558003276940597205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338392372002184627064803 2007588558003276940597205)
                ·
                  refine ⟨47052856828201803295247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2007588558003276940597205 47052856828201803295247)
                  ·
                    rfl

theorem cell21_206179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_206179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206179 prefixEnd_206179 := by exact prefixLift 206179
  have htrace : WordTrace (prefixWord ++ tailWord_206179) baseStart_206179 baseEnd_206179 := by
    simpa [prefixWord, tailWord_206179, baseEnd_206179] using wordTrace_append hprefix tailTrace_206179
  have hstable : (prefixWord ++ tailWord_206179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206179).length < 2 ^ (prefixWord ++ tailWord_206179).sum := by decide
  have hdescent : baseEnd_206179 < baseStart_206179 := by decide
  rcases family_descends (prefixWord ++ tailWord_206179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206272 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_206272 : Nat := 118140960795 + 206272 * 2 ^ 59
def prefixEnd_206272 : Nat := 4983230072969 + 3 ^ 40 * 206272 * 2
def baseEnd_206272 : Nat := 47074080695254308245057

theorem tailTrace_206272 : CollatzResearch.WordTrace tailWord_206272 prefixEnd_206272 47074080695254308245057 := by
  unfold tailWord_206272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761678954359623649014535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5015571939146164865352713 3761678954359623649014535)
  ·
    refine ⟨5642518431539435473521803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3761678954359623649014535 5642518431539435473521803)
    ·
      refine ⟨8463777647309153210282705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5642518431539435473521803 8463777647309153210282705)
      ·
        refine ⟨6347833235481864907712029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8463777647309153210282705 6347833235481864907712029)
        ·
          refine ⟨2380437463305699340392011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6347833235481864907712029 2380437463305699340392011)
          ·
            refine ⟨3570656194958549010588017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380437463305699340392011 3570656194958549010588017)
            ·
              refine ⟨2677992146218911757941013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570656194958549010588017 2677992146218911757941013)
              ·
                refine ⟨125530881854011488653485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2677992146218911757941013 125530881854011488653485)
                ·
                  refine ⟨47074080695254308245057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125530881854011488653485 47074080695254308245057)
                  ·
                    rfl

theorem cell21_206272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_206272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206272 prefixEnd_206272 := by exact prefixLift 206272
  have htrace : WordTrace (prefixWord ++ tailWord_206272) baseStart_206272 baseEnd_206272 := by
    simpa [prefixWord, tailWord_206272, baseEnd_206272] using wordTrace_append hprefix tailTrace_206272
  have hstable : (prefixWord ++ tailWord_206272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206272).length < 2 ^ (prefixWord ++ tailWord_206272).sum := by decide
  have hdescent : baseEnd_206272 < baseStart_206272 := by decide
  rcases family_descends (prefixWord ++ tailWord_206272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206317 : List Nat := [1, 5, 1, 3, 2, 9]
def baseStart_206317 : Nat := 118140960795 + 206317 * 2 ^ 59
def prefixEnd_206317 : Nat := 4983230072969 + 3 ^ 40 * 206317 * 2
def baseEnd_206317 : Nat := 1743864826234971481295

theorem tailTrace_206317 : CollatzResearch.WordTrace tailWord_206317 prefixEnd_206317 1743864826234971481295 := by
  unfold tailWord_206317
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524999193556219983417205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5016666129037479988944803 7524999193556219983417205)
  ·
    refine ⟨705468674395895623445363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7524999193556219983417205 705468674395895623445363)
    ·
      refine ⟨1058203011593843435168045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705468674395895623445363 1058203011593843435168045)
      ·
        refine ⟨396826129347691288188017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1058203011593843435168045 396826129347691288188017)
        ·
          refine ⟨297619597010768466141013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396826129347691288188017 297619597010768466141013)
          ·
            refine ⟨1743864826234971481295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 297619597010768466141013 1743864826234971481295)
            ·
              rfl

theorem cell21_206317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 9].length) (baseStart_206317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206317 prefixEnd_206317 := by exact prefixLift 206317
  have htrace : WordTrace (prefixWord ++ tailWord_206317) baseStart_206317 baseEnd_206317 := by
    simpa [prefixWord, tailWord_206317, baseEnd_206317] using wordTrace_append hprefix tailTrace_206317
  have hstable : (prefixWord ++ tailWord_206317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206317).length < 2 ^ (prefixWord ++ tailWord_206317).sum := by decide
  have hdescent : baseEnd_206317 < baseStart_206317 := by decide
  rcases family_descends (prefixWord ++ tailWord_206317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206348 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_206348 : Nat := 118140960795 + 206348 * 2 ^ 59
def prefixEnd_206348 : Nat := 4983230072969 + 3 ^ 40 * 206348 * 2
def baseEnd_206348 : Nat := 47091424930695064978235

theorem tailTrace_206348 : CollatzResearch.WordTrace tailWord_206348 prefixEnd_206348 47091424930695064978235 := by
  unfold tailWord_206348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763064928221956138897849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5017419904295941518530465 3763064928221956138897849)
  ·
    refine ⟨2822298696166467104173387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3763064928221956138897849 2822298696166467104173387)
    ·
      refine ⟨4233448044249700656260081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822298696166467104173387 4233448044249700656260081)
      ·
        refine ⟨3175086033187275492195061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4233448044249700656260081 3175086033187275492195061)
        ·
          refine ⟨297664315611307077393287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3175086033187275492195061 297664315611307077393287)
          ·
            refine ⟨446496473416960616089931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297664315611307077393287 446496473416960616089931)
            ·
              refine ⟨669744710125440924134897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446496473416960616089931 669744710125440924134897)
              ·
                refine ⟨502308532594080693101173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669744710125440924134897 502308532594080693101173)
                ·
                  refine ⟨47091424930695064978235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 502308532594080693101173 47091424930695064978235)
                  ·
                    rfl

theorem cell21_206348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_206348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206348 prefixEnd_206348 := by exact prefixLift 206348
  have htrace : WordTrace (prefixWord ++ tailWord_206348) baseStart_206348 baseEnd_206348 := by
    simpa [prefixWord, tailWord_206348, baseEnd_206348] using wordTrace_append hprefix tailTrace_206348
  have hstable : (prefixWord ++ tailWord_206348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206348).length < 2 ^ (prefixWord ++ tailWord_206348).sum := by decide
  have hdescent : baseEnd_206348 < baseStart_206348 := by decide
  rcases family_descends (prefixWord ++ tailWord_206348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206365 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 3]
def baseStart_206365 : Nat := 118140960795 + 206365 * 2 ^ 59
def prefixEnd_206365 : Nat := 4983230072969 + 3 ^ 40 * 206365 * 2
def baseEnd_206365 : Nat := 47095304562306813194867

theorem tailTrace_206365 : CollatzResearch.WordTrace tailWord_206365 prefixEnd_206365 47095304562306813194867 := by
  unfold tailWord_206365
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526749897382324181164549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5017833264921549454109699 7526749897382324181164549)
  ·
    refine ⟨1411265605759185783968353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7526749897382324181164549 1411265605759185783968353)
    ·
      refine ⟨1058449204319389337976265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1411265605759185783968353 1058449204319389337976265)
      ·
        refine ⟨793836903239542003482199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058449204319389337976265 793836903239542003482199)
        ·
          refine ⟨1190755354859313005223299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793836903239542003482199 1190755354859313005223299)
          ·
            refine ⟨1786133032288969507834949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190755354859313005223299 1786133032288969507834949)
            ·
              refine ⟨334899943554181782719053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1786133032288969507834949 334899943554181782719053)
              ·
                refine ⟨125587478832818168519645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334899943554181782719053 125587478832818168519645)
                ·
                  refine ⟨47095304562306813194867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125587478832818168519645 47095304562306813194867)
                  ·
                    rfl

theorem cell21_206365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_206365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206365 prefixEnd_206365 := by exact prefixLift 206365
  have htrace : WordTrace (prefixWord ++ tailWord_206365) baseStart_206365 baseEnd_206365 := by
    simpa [prefixWord, tailWord_206365, baseEnd_206365] using wordTrace_append hprefix tailTrace_206365
  have hstable : (prefixWord ++ tailWord_206365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206365).length < 2 ^ (prefixWord ++ tailWord_206365).sum := by decide
  have hdescent : baseEnd_206365 < baseStart_206365 := by decide
  rcases family_descends (prefixWord ++ tailWord_206365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206396 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_206396 : Nat := 118140960795 + 206396 * 2 ^ 59
def prefixEnd_206396 : Nat := 4983230072969 + 3 ^ 40 * 206396 * 2
def baseEnd_206396 : Nat := 47102379184657648178137

theorem tailTrace_206396 : CollatzResearch.WordTrace tailWord_206396 prefixEnd_206396 47102379184657648178137 := by
  unfold tailWord_206396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763940280135008237771521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5018587040180010983695361 3763940280135008237771521)
  ·
    refine ⟨2822955210101256178328641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3763940280135008237771521 2822955210101256178328641)
    ·
      refine ⟨2117216407575942133746481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2822955210101256178328641 2117216407575942133746481)
      ·
        refine ⟨1587912305681956600309861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117216407575942133746481 1587912305681956600309861)
        ·
          refine ⟨297733557315366862558099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1587912305681956600309861 297733557315366862558099)
          ·
            refine ⟨446600335973050293837149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297733557315366862558099 446600335973050293837149)
            ·
              refine ⟨167475125989893860188931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446600335973050293837149 167475125989893860188931)
              ·
                refine ⟨251212688984840790283397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167475125989893860188931 251212688984840790283397)
                ·
                  refine ⟨47102379184657648178137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251212688984840790283397 47102379184657648178137)
                  ·
                    rfl

theorem cell21_206396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_206396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206396 prefixEnd_206396 := by exact prefixLift 206396
  have htrace : WordTrace (prefixWord ++ tailWord_206396) baseStart_206396 baseEnd_206396 := by
    simpa [prefixWord, tailWord_206396, baseEnd_206396] using wordTrace_append hprefix tailTrace_206396
  have hstable : (prefixWord ++ tailWord_206396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206396).length < 2 ^ (prefixWord ++ tailWord_206396).sum := by decide
  have hdescent : baseEnd_206396 < baseStart_206396 := by decide
  rcases family_descends (prefixWord ++ tailWord_206396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206514 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_206514 : Nat := 118140960795 + 206514 * 2 ^ 59
def prefixEnd_206514 : Nat := 4983230072969 + 3 ^ 40 * 206514 * 2
def baseEnd_206514 : Nat := 47129308392315665211229

theorem tailTrace_206514 : CollatzResearch.WordTrace tailWord_206514 prefixEnd_206514 47129308392315665211229 := by
  unfold tailWord_206514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883046093460630657084649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5021456249228348418892397 1883046093460630657084649)
  ·
    refine ⟨1412284570095472992813487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1883046093460630657084649 1412284570095472992813487)
    ·
      refine ⟨2118426855143209489220231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412284570095472992813487 2118426855143209489220231)
      ·
        refine ⟨3177640282714814233830347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118426855143209489220231 3177640282714814233830347)
        ·
          refine ⟨4766460424072221350745521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177640282714814233830347 4766460424072221350745521)
          ·
            refine ⟨3574845318054166013059141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4766460424072221350745521 3574845318054166013059141)
            ·
              refine ⟨670283497135156127448589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3574845318054166013059141 670283497135156127448589)
              ·
                refine ⟨251356311425683547793221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670283497135156127448589 251356311425683547793221)
                ·
                  refine ⟨47129308392315665211229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251356311425683547793221 47129308392315665211229)
                  ·
                    rfl

theorem cell21_206514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_206514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206514 prefixEnd_206514 := by exact prefixLift 206514
  have htrace : WordTrace (prefixWord ++ tailWord_206514) baseStart_206514 baseEnd_206514 := by
    simpa [prefixWord, tailWord_206514, baseEnd_206514] using wordTrace_append hprefix tailTrace_206514
  have hstable : (prefixWord ++ tailWord_206514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206514).length < 2 ^ (prefixWord ++ tailWord_206514).sum := by decide
  have hdescent : baseEnd_206514 < baseStart_206514 := by decide
  rcases family_descends (prefixWord ++ tailWord_206514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206548 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_206548 : Nat := 118140960795 + 206548 * 2 ^ 59
def prefixEnd_206548 : Nat := 4983230072969 + 3 ^ 40 * 206548 * 2
def baseEnd_206548 : Nat := 47137067655539161644493

theorem tailTrace_206548 : CollatzResearch.WordTrace tailWord_206548 prefixEnd_206548 47137067655539161644493 := by
  unfold tailWord_206548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766712227859673217538149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5022282970479564290050865 3766712227859673217538149)
  ·
    refine ⟨706258542723688728288403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3766712227859673217538149 706258542723688728288403)
    ·
      refine ⟨1059387814085533092432605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706258542723688728288403 1059387814085533092432605)
      ·
        refine ⟨397270430282074909662227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1059387814085533092432605 397270430282074909662227)
        ·
          refine ⟨595905645423112364493341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397270430282074909662227 595905645423112364493341)
          ·
            refine ⟨223464617033667136685003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595905645423112364493341 223464617033667136685003)
            ·
              refine ⟨335196925550500705027505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223464617033667136685003 335196925550500705027505)
              ·
                refine ⟨251397694162875528770629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335196925550500705027505 251397694162875528770629)
                ·
                  refine ⟨47137067655539161644493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251397694162875528770629 47137067655539161644493)
                  ·
                    rfl

theorem cell21_206548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_206548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206548 prefixEnd_206548 := by exact prefixLift 206548
  have htrace : WordTrace (prefixWord ++ tailWord_206548) baseStart_206548 baseEnd_206548 := by
    simpa [prefixWord, tailWord_206548, baseEnd_206548] using wordTrace_append hprefix tailTrace_206548
  have hstable : (prefixWord ++ tailWord_206548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206548).length < 2 ^ (prefixWord ++ tailWord_206548).sum := by decide
  have hdescent : baseEnd_206548 < baseStart_206548 := by decide
  rcases family_descends (prefixWord ++ tailWord_206548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206559 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_206559 : Nat := 118140960795 + 206559 * 2 ^ 59
def prefixEnd_206559 : Nat := 4983230072969 + 3 ^ 40 * 206559 * 2
def baseEnd_206559 : Nat := 47139578005405586961137

theorem tailTrace_206559 : CollatzResearch.WordTrace tailWord_206559 prefixEnd_206559 47139578005405586961137 := by
  unfold tailWord_206559
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533825658679495313726731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5022550439119663542484487 7533825658679495313726731)
  ·
    refine ⟨11300738488019242970590097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7533825658679495313726731 11300738488019242970590097)
    ·
      refine ⟨8475553866014432227942573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11300738488019242970590097 8475553866014432227942573)
      ·
        refine ⟨3178332699755412085478465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8475553866014432227942573 3178332699755412085478465)
        ·
          refine ⟨2383749524816559064108849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3178332699755412085478465 2383749524816559064108849)
          ·
            refine ⟨1787812143612419298081637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383749524816559064108849 1787812143612419298081637)
            ·
              refine ⟨335214776927328618390307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1787812143612419298081637 335214776927328618390307)
              ·
                refine ⟨502822165390992927585461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335214776927328618390307 502822165390992927585461)
                ·
                  refine ⟨47139578005405586961137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 502822165390992927585461 47139578005405586961137)
                  ·
                    rfl

theorem cell21_206559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_206559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206559 prefixEnd_206559 := by exact prefixLift 206559
  have htrace : WordTrace (prefixWord ++ tailWord_206559) baseStart_206559 baseEnd_206559 := by
    simpa [prefixWord, tailWord_206559, baseEnd_206559] using wordTrace_append hprefix tailTrace_206559
  have hstable : (prefixWord ++ tailWord_206559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206559).length < 2 ^ (prefixWord ++ tailWord_206559).sum := by decide
  have hdescent : baseEnd_206559 < baseStart_206559 := by decide
  rcases family_descends (prefixWord ++ tailWord_206559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206666 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_206666 : Nat := 118140960795 + 206666 * 2 ^ 59
def prefixEnd_206666 : Nat := 4983230072969 + 3 ^ 40 * 206666 * 2
def baseEnd_206666 : Nat := 47163996863197178677585

theorem tailTrace_206666 : CollatzResearch.WordTrace tailWord_206666 prefixEnd_206666 47163996863197178677585 := by
  unfold tailWord_206666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884432067322963146967963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5025152179527901725247901 1884432067322963146967963)
  ·
    refine ⟨2826648100984444720451945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1884432067322963146967963 2826648100984444720451945)
    ·
      refine ⟨2119986075738333540338959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2826648100984444720451945 2119986075738333540338959)
      ·
        refine ⟨3179979113607500310508439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119986075738333540338959 3179979113607500310508439)
        ·
          refine ⟨4769968670411250465762659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179979113607500310508439 4769968670411250465762659)
          ·
            refine ⟨7154953005616875698643989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769968670411250465762659 7154953005616875698643989)
            ·
              refine ⟨335388422138291048373937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7154953005616875698643989 335388422138291048373937)
              ·
                refine ⟨251541316603718286280453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335388422138291048373937 251541316603718286280453)
                ·
                  refine ⟨47163996863197178677585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251541316603718286280453 47163996863197178677585)
                  ·
                    rfl

theorem cell21_206666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_206666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206666 prefixEnd_206666 := by exact prefixLift 206666
  have htrace : WordTrace (prefixWord ++ tailWord_206666) baseStart_206666 baseEnd_206666 := by
    simpa [prefixWord, tailWord_206666, baseEnd_206666] using wordTrace_append hprefix tailTrace_206666
  have hstable : (prefixWord ++ tailWord_206666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206666).length < 2 ^ (prefixWord ++ tailWord_206666).sum := by decide
  have hdescent : baseEnd_206666 < baseStart_206666 := by decide
  rcases family_descends (prefixWord ++ tailWord_206666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206725 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_206725 : Nat := 118140960795 + 206725 * 2 ^ 59
def prefixEnd_206725 : Nat := 4983230072969 + 3 ^ 40 * 206725 * 2
def baseEnd_206725 : Nat := 47177461467026187194131

theorem tailTrace_206725 : CollatzResearch.WordTrace tailWord_206725 prefixEnd_206725 47177461467026187194131 := by
  unfold tailWord_206725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539880176078105664269629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5026586784052070442846419 7539880176078105664269629)
  ·
    refine ⟨2827455066029289624101111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7539880176078105664269629 2827455066029289624101111)
    ·
      refine ⟨4241182599043934436151667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827455066029289624101111 4241182599043934436151667)
      ·
        refine ⟨6361773898565901654227501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241182599043934436151667 6361773898565901654227501)
        ·
          refine ⟨2385665211962213120335313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6361773898565901654227501 2385665211962213120335313)
          ·
            refine ⟨1789248908971659840251485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385665211962213120335313 1789248908971659840251485)
            ·
              refine ⟨670968340864372440094307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1789248908971659840251485 670968340864372440094307)
              ·
                refine ⟨1006452511296558660141461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670968340864372440094307 1006452511296558660141461)
                ·
                  refine ⟨47177461467026187194131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1006452511296558660141461 47177461467026187194131)
                  ·
                    rfl

theorem cell21_206725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_206725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206725 prefixEnd_206725 := by exact prefixLift 206725
  have htrace : WordTrace (prefixWord ++ tailWord_206725) baseStart_206725 baseEnd_206725 := by
    simpa [prefixWord, tailWord_206725, baseEnd_206725] using wordTrace_append hprefix tailTrace_206725
  have hstable : (prefixWord ++ tailWord_206725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206725).length < 2 ^ (prefixWord ++ tailWord_206725).sum := by decide
  have hdescent : baseEnd_206725 < baseStart_206725 := by decide
  rcases family_descends (prefixWord ++ tailWord_206725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206728 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_206728 : Nat := 118140960795 + 206728 * 2 ^ 59
def prefixEnd_206728 : Nat := 4983230072969 + 3 ^ 40 * 206728 * 2
def baseEnd_206728 : Nat := 47178146107898848644125

theorem tailTrace_206728 : CollatzResearch.WordTrace tailWord_206728 prefixEnd_206728 47178146107898848644125 := by
  unfold tailWord_206728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769994797533618588314419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5026659730044824784419225 3769994797533618588314419)
  ·
    refine ⟨5654992196300427882471629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3769994797533618588314419 5654992196300427882471629)
    ·
      refine ⟨2120622073612660455926861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5654992196300427882471629 2120622073612660455926861)
      ·
        refine ⟨795233277604747670972573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2120622073612660455926861 795233277604747670972573)
        ·
          refine ⟨298212479101780376614715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795233277604747670972573 298212479101780376614715)
          ·
            refine ⟨447318718652670564922073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298212479101780376614715 447318718652670564922073)
            ·
              refine ⟨335489038989502923691555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447318718652670564922073 335489038989502923691555)
              ·
                refine ⟨503233558484254385537333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335489038989502923691555 503233558484254385537333)
                ·
                  refine ⟨47178146107898848644125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 503233558484254385537333 47178146107898848644125)
                  ·
                    rfl

theorem cell21_206728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_206728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206728 prefixEnd_206728 := by exact prefixLift 206728
  have htrace : WordTrace (prefixWord ++ tailWord_206728) baseStart_206728 baseEnd_206728 := by
    simpa [prefixWord, tailWord_206728, baseEnd_206728] using wordTrace_append hprefix tailTrace_206728
  have hstable : (prefixWord ++ tailWord_206728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206728).length < 2 ^ (prefixWord ++ tailWord_206728).sum := by decide
  have hdescent : baseEnd_206728 < baseStart_206728 := by decide
  rcases family_descends (prefixWord ++ tailWord_206728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206756 : List Nat := [2, 3, 1, 2, 1, 4, 1, 7]
def baseStart_206756 : Nat := 118140960795 + 206756 * 2 ^ 59
def prefixEnd_206756 : Nat := 4983230072969 + 3 ^ 40 * 206756 * 2
def baseEnd_206756 : Nat := 15728178696459007392467

theorem tailTrace_206756 : CollatzResearch.WordTrace tailWord_206756 prefixEnd_206756 15728178696459007392467 := by
  unfold tailWord_206756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3770505419482898979324061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5027340559310531972432081 3770505419482898979324061)
  ·
    refine ⟨1413939532306087117246523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3770505419482898979324061 1413939532306087117246523)
    ·
      refine ⟨2120909298459130675869785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413939532306087117246523 2120909298459130675869785)
      ·
        refine ⟨1590681973844348006902339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2120909298459130675869785 1590681973844348006902339)
        ·
          refine ⟨2386022960766522010353509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590681973844348006902339 2386022960766522010353509)
          ·
            refine ⟨447379305143722876941283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2386022960766522010353509 447379305143722876941283)
            ·
              refine ⟨671068957715584315411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447379305143722876941283 671068957715584315411925)
              ·
                refine ⟨15728178696459007392467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671068957715584315411925 15728178696459007392467)
                ·
                  rfl

theorem cell21_206756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_206756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206756 prefixEnd_206756 := by exact prefixLift 206756
  have htrace : WordTrace (prefixWord ++ tailWord_206756) baseStart_206756 baseEnd_206756 := by
    simpa [prefixWord, tailWord_206756, baseEnd_206756] using wordTrace_append hprefix tailTrace_206756
  have hstable : (prefixWord ++ tailWord_206756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206756).length < 2 ^ (prefixWord ++ tailWord_206756).sum := by decide
  have hdescent : baseEnd_206756 < baseStart_206756 := by decide
  rcases family_descends (prefixWord ++ tailWord_206756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206770 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_206770 : Nat := 118140960795 + 206770 * 2 ^ 59
def prefixEnd_206770 : Nat := 4983230072969 + 3 ^ 40 * 206770 * 2
def baseEnd_206770 : Nat := 47187731080116108944039

theorem tailTrace_206770 : CollatzResearch.WordTrace tailWord_206770 prefixEnd_206770 47187731080116108944039 := by
  unfold tailWord_206770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885380365228769587414441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5027680973943385566438509 1885380365228769587414441)
  ·
    refine ⟨1414035273921577190560831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1885380365228769587414441 1414035273921577190560831)
    ·
      refine ⟨2121052910882365785841247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414035273921577190560831 2121052910882365785841247)
      ·
        refine ⟨3181579366323548678761871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121052910882365785841247 3181579366323548678761871)
        ·
          refine ⟨4772369049485323018142807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181579366323548678761871 4772369049485323018142807)
          ·
            refine ⟨7158553574227984527214211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772369049485323018142807 7158553574227984527214211)
            ·
              refine ⟨10737830361341976790821317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158553574227984527214211 10737830361341976790821317)
              ·
                refine ⟨2013343192751620648278997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10737830361341976790821317 2013343192751620648278997)
                ·
                  refine ⟨47187731080116108944039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2013343192751620648278997 47187731080116108944039)
                  ·
                    rfl

theorem cell21_206770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_206770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206770 prefixEnd_206770 := by exact prefixLift 206770
  have htrace : WordTrace (prefixWord ++ tailWord_206770) baseStart_206770 baseEnd_206770 := by
    simpa [prefixWord, tailWord_206770, baseEnd_206770] using wordTrace_append hprefix tailTrace_206770
  have hstable : (prefixWord ++ tailWord_206770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206770).length < 2 ^ (prefixWord ++ tailWord_206770).sum := by decide
  have hdescent : baseEnd_206770 < baseStart_206770 := by decide
  rcases family_descends (prefixWord ++ tailWord_206770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206894 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_206894 : Nat := 118140960795 + 206894 * 2 ^ 59
def prefixEnd_206894 : Nat := 4983230072969 + 3 ^ 40 * 206894 * 2
def baseEnd_206894 : Nat := 47216029569519448877119

theorem tailTrace_206894 : CollatzResearch.WordTrace tailWord_206894 prefixEnd_206894 47216029569519448877119 := by
  unfold tailWord_206894
  simp only [CollatzResearch.WordTrace]
  refine ⟨943255514058230940896467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5030696074977231684781157 943255514058230940896467)
  ·
    refine ⟨1414883271087346411344701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943255514058230940896467 1414883271087346411344701)
    ·
      refine ⟨530581226657754904254263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1414883271087346411344701 530581226657754904254263)
      ·
        refine ⟨795871839986632356381395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530581226657754904254263 795871839986632356381395)
        ·
          refine ⟨1193807759979948534572093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795871839986632356381395 1193807759979948534572093)
          ·
            refine ⟨447677909992480700464535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1193807759979948534572093 447677909992480700464535)
            ·
              refine ⟨671516864988721050696803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447677909992480700464535 671516864988721050696803)
              ·
                refine ⟨1007275297483081576045205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671516864988721050696803 1007275297483081576045205)
                ·
                  refine ⟨47216029569519448877119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1007275297483081576045205 47216029569519448877119)
                  ·
                    rfl

theorem cell21_206894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_206894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206894 prefixEnd_206894 := by exact prefixLift 206894
  have htrace : WordTrace (prefixWord ++ tailWord_206894) baseStart_206894 baseEnd_206894 := by
    simpa [prefixWord, tailWord_206894, baseEnd_206894] using wordTrace_append hprefix tailTrace_206894
  have hstable : (prefixWord ++ tailWord_206894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206894).length < 2 ^ (prefixWord ++ tailWord_206894).sum := by decide
  have hdescent : baseEnd_206894 < baseStart_206894 := by decide
  rcases family_descends (prefixWord ++ tailWord_206894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206953 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_206953 : Nat := 118140960795 + 206953 * 2 ^ 59
def prefixEnd_206953 : Nat := 4983230072969 + 3 ^ 40 * 206953 * 2
def baseEnd_206953 : Nat := 47229494173348457393665

theorem tailTrace_206953 : CollatzResearch.WordTrace tailWord_206953 prefixEnd_206953 47229494173348457393665 := by
  unfold tailWord_206953
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548196019252100603569513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5032130679501400402379675 7548196019252100603569513)
  ·
    refine ⟨5661147014439075452677135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7548196019252100603569513 5661147014439075452677135)
    ·
      refine ⟨8491720521658613179015703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661147014439075452677135 8491720521658613179015703)
      ·
        refine ⟨12737580782487919768523555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491720521658613179015703 12737580782487919768523555)
        ·
          refine ⟨19106371173731879652785333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737580782487919768523555 19106371173731879652785333)
          ·
            refine ⟨1791222297537363717448625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19106371173731879652785333 1791222297537363717448625)
            ·
              refine ⟨1343416723153022788086469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1791222297537363717448625 1343416723153022788086469)
              ·
                refine ⟨251890635591191772766213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1343416723153022788086469 251890635591191772766213)
                ·
                  refine ⟨47229494173348457393665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251890635591191772766213 47229494173348457393665)
                  ·
                    rfl

theorem cell21_206953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_206953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206953 prefixEnd_206953 := by exact prefixLift 206953
  have htrace : WordTrace (prefixWord ++ tailWord_206953) baseStart_206953 baseEnd_206953 := by
    simpa [prefixWord, tailWord_206953, baseEnd_206953] using wordTrace_append hprefix tailTrace_206953
  have hstable : (prefixWord ++ tailWord_206953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206953).length < 2 ^ (prefixWord ++ tailWord_206953).sum := by decide
  have hdescent : baseEnd_206953 < baseStart_206953 := by decide
  rcases family_descends (prefixWord ++ tailWord_206953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206967 : List Nat := [1, 1, 3, 1, 1, 5, 1, 8]
def baseStart_206967 : Nat := 118140960795 + 206967 * 2 ^ 59
def prefixEnd_206967 : Nat := 4983230072969 + 3 ^ 40 * 206967 * 2
def baseEnd_206967 : Nat := 15744229721362514720101

theorem tailTrace_206967 : CollatzResearch.WordTrace tailWord_206967 prefixEnd_206967 15744229721362514720101 := by
  unfold tailWord_206967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548706641201380994579155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5032471094134253996386103 7548706641201380994579155)
  ·
    refine ⟨11323059961802071491868733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7548706641201380994579155 11323059961802071491868733)
    ·
      refine ⟨4246147485675776809450775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11323059961802071491868733 4246147485675776809450775)
      ·
        refine ⟨6369221228513665214176163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246147485675776809450775 6369221228513665214176163)
        ·
          refine ⟨9553831842770497821264245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369221228513665214176163 9553831842770497821264245)
          ·
            refine ⟨895671735259734170743523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9553831842770497821264245 895671735259734170743523)
            ·
              refine ⟨1343507602889601256115285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895671735259734170743523 1343507602889601256115285)
              ·
                refine ⟨15744229721362514720101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1343507602889601256115285 15744229721362514720101)
                ·
                  rfl

theorem cell21_206967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_206967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206967 prefixEnd_206967 := by exact prefixLift 206967
  have htrace : WordTrace (prefixWord ++ tailWord_206967) baseStart_206967 baseEnd_206967 := by
    simpa [prefixWord, tailWord_206967, baseEnd_206967] using wordTrace_append hprefix tailTrace_206967
  have hstable : (prefixWord ++ tailWord_206967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206967).length < 2 ^ (prefixWord ++ tailWord_206967).sum := by decide
  have hdescent : baseEnd_206967 < baseStart_206967 := by decide
  rcases family_descends (prefixWord ++ tailWord_206967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_206984 : List Nat := [2, 1, 3, 4, 1, 1, 2, 7]
def baseStart_206984 : Nat := 118140960795 + 206984 * 2 ^ 59
def prefixEnd_206984 : Nat := 4983230072969 + 3 ^ 40 * 206984 * 2
def baseEnd_206984 : Nat := 15745522931899764125645

theorem tailTrace_206984 : CollatzResearch.WordTrace tailWord_206984 prefixEnd_206984 15745522931899764125645 := by
  unfold tailWord_206984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774663341069896448974003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5032884454759861931965337 3774663341069896448974003)
  ·
    refine ⟨5661995011604844673461005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774663341069896448974003 5661995011604844673461005)
    ·
      refine ⟨2123248129351816752547877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5661995011604844673461005 2123248129351816752547877)
      ·
        refine ⟨398109024253465641102727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2123248129351816752547877 398109024253465641102727)
        ·
          refine ⟨597163536380198461654091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398109024253465641102727 597163536380198461654091)
          ·
            refine ⟨895745304570297692481137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597163536380198461654091 895745304570297692481137)
            ·
              refine ⟨671808978427723269360853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895745304570297692481137 671808978427723269360853)
              ·
                refine ⟨15745522931899764125645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671808978427723269360853 15745522931899764125645)
                ·
                  rfl

theorem cell21_206984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_206984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_206984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_206984 prefixEnd_206984 := by exact prefixLift 206984
  have htrace : WordTrace (prefixWord ++ tailWord_206984) baseStart_206984 baseEnd_206984 := by
    simpa [prefixWord, tailWord_206984, baseEnd_206984] using wordTrace_append hprefix tailTrace_206984
  have hstable : (prefixWord ++ tailWord_206984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_206984).length < 2 ^ (prefixWord ++ tailWord_206984).sum := by decide
  have hdescent : baseEnd_206984 < baseStart_206984 := by decide
  rcases family_descends (prefixWord ++ tailWord_206984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207018 : List Nat := [3, 1, 5, 1, 2, 2, 1, 6]
def baseStart_207018 : Nat := 118140960795 + 207018 * 2 ^ 59
def prefixEnd_207018 : Nat := 4983230072969 + 3 ^ 40 * 207018 * 2
def baseEnd_207018 : Nat := 15748109352974262936733

theorem tailTrace_207018 : CollatzResearch.WordTrace tailWord_207018 prefixEnd_207018 15748109352974262936733 := by
  unfold tailWord_207018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887641691004154176171427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5033711176011077803123805 1887641691004154176171427)
  ·
    refine ⟨2831462536506231264257141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887641691004154176171427 2831462536506231264257141)
    ·
      refine ⟨265449612797459181024107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2831462536506231264257141 265449612797459181024107)
      ·
        refine ⟨398174419196188771536161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265449612797459181024107 398174419196188771536161)
        ·
          refine ⟨298630814397141578652121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398174419196188771536161 298630814397141578652121)
          ·
            refine ⟨223973110797856183989091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298630814397141578652121 223973110797856183989091)
            ·
              refine ⟨335959666196784275983637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223973110797856183989091 335959666196784275983637)
              ·
                refine ⟨15748109352974262936733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 335959666196784275983637 15748109352974262936733)
                ·
                  rfl

theorem cell21_207018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_207018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207018 prefixEnd_207018 := by exact prefixLift 207018
  have htrace : WordTrace (prefixWord ++ tailWord_207018) baseStart_207018 baseEnd_207018 := by
    simpa [prefixWord, tailWord_207018, baseEnd_207018] using wordTrace_append hprefix tailTrace_207018
  have hstable : (prefixWord ++ tailWord_207018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207018).length < 2 ^ (prefixWord ++ tailWord_207018).sum := by decide
  have hdescent : baseEnd_207018 < baseStart_207018 := by decide
  rcases family_descends (prefixWord ++ tailWord_207018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207136 : List Nat := [2, 1, 1, 5, 2, 2, 2, 6]
def baseStart_207136 : Nat := 118140960795 + 207136 * 2 ^ 59
def prefixEnd_207136 : Nat := 4983230072969 + 3 ^ 40 * 207136 * 2
def baseEnd_207136 : Nat := 15757085755526935281097

theorem tailTrace_207136 : CollatzResearch.WordTrace tailWord_207136 prefixEnd_207136 15757085755526935281097 := by
  unfold tailWord_207136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777435288794561428740631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5036580385059415238320841 3777435288794561428740631)
  ·
    refine ⟨5666152933191842143110947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777435288794561428740631 5666152933191842143110947)
    ·
      refine ⟨8499229399787763214666421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666152933191842143110947 8499229399787763214666421)
      ·
        refine ⟨796802756230102801374977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8499229399787763214666421 796802756230102801374977)
        ·
          refine ⟨597602067172577101031233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796802756230102801374977 597602067172577101031233)
          ·
            refine ⟨448201550379432825773425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597602067172577101031233 448201550379432825773425)
            ·
              refine ⟨336151162784574619330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448201550379432825773425 336151162784574619330069)
              ·
                refine ⟨15757085755526935281097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 336151162784574619330069 15757085755526935281097)
                ·
                  rfl

theorem cell21_207136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_207136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207136 prefixEnd_207136 := by exact prefixLift 207136
  have htrace : WordTrace (prefixWord ++ tailWord_207136) baseStart_207136 baseEnd_207136 := by
    simpa [prefixWord, tailWord_207136, baseEnd_207136] using wordTrace_append hprefix tailTrace_207136
  have hstable : (prefixWord ++ tailWord_207136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207136).length < 2 ^ (prefixWord ++ tailWord_207136).sum := by decide
  have hdescent : baseEnd_207136 < baseStart_207136 := by decide
  rcases family_descends (prefixWord ++ tailWord_207136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207167 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 3]
def baseStart_207167 : Nat := 118140960795 + 207167 * 2 ^ 59
def prefixEnd_207167 : Nat := 4983230072969 + 3 ^ 40 * 207167 * 2
def baseEnd_207167 : Nat := 47278331888931640826561

theorem tailTrace_207167 : CollatzResearch.WordTrace tailWord_207167 prefixEnd_207167 47278331888931640826561 := by
  unfold tailWord_207167
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556001240476815151859755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5037334160317876767906503 7556001240476815151859755)
  ·
    refine ⟨11334001860715222727789633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7556001240476815151859755 11334001860715222727789633)
    ·
      refine ⟨8500501395536417045842225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11334001860715222727789633 8500501395536417045842225)
      ·
        refine ⟨6375376046652312784381669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8500501395536417045842225 6375376046652312784381669)
        ·
          refine ⟨1195383008747308647071563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6375376046652312784381669 1195383008747308647071563)
          ·
            refine ⟨1793074513120962970607345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195383008747308647071563 1793074513120962970607345)
            ·
              refine ⟨1344805884840722227955509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793074513120962970607345 1344805884840722227955509)
              ·
                refine ⟨126075551703817708870829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1344805884840722227955509 126075551703817708870829)
                ·
                  refine ⟨47278331888931640826561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126075551703817708870829 47278331888931640826561)
                  ·
                    rfl

theorem cell21_207167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3].length) (baseStart_207167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207167 prefixEnd_207167 := by exact prefixLift 207167
  have htrace : WordTrace (prefixWord ++ tailWord_207167) baseStart_207167 baseEnd_207167 := by
    simpa [prefixWord, tailWord_207167, baseEnd_207167] using wordTrace_append hprefix tailTrace_207167
  have hstable : (prefixWord ++ tailWord_207167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207167).length < 2 ^ (prefixWord ++ tailWord_207167).sum := by decide
  have hdescent : baseEnd_207167 < baseStart_207167 := by decide
  rcases family_descends (prefixWord ++ tailWord_207167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207184 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_207184 : Nat := 118140960795 + 207184 * 2 ^ 59
def prefixEnd_207184 : Nat := 4983230072969 + 3 ^ 40 * 207184 * 2
def baseEnd_207184 : Nat := 47282211520543389043193

theorem tailTrace_207184 : CollatzResearch.WordTrace tailWord_207184 prefixEnd_207184 47282211520543389043193 := by
  unfold tailWord_207184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778310640707613527614303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5037747520943484703485737 3778310640707613527614303)
  ·
    refine ⟨5667465961061420291421455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778310640707613527614303 5667465961061420291421455)
    ·
      refine ⟨8501198941592130437132183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5667465961061420291421455 8501198941592130437132183)
      ·
        refine ⟨12751798412388195655698275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501198941592130437132183 12751798412388195655698275)
        ·
          refine ⟨19127697618582293483547413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751798412388195655698275 19127697618582293483547413)
          ·
            refine ⟨896610825871045007041285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19127697618582293483547413 896610825871045007041285)
            ·
              refine ⟨168114529850820938820241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 896610825871045007041285 168114529850820938820241)
              ·
                refine ⟨126085897388115704115181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168114529850820938820241 126085897388115704115181)
                ·
                  refine ⟨47282211520543389043193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126085897388115704115181 47282211520543389043193)
                  ·
                    rfl

theorem cell21_207184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_207184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207184 prefixEnd_207184 := by exact prefixLift 207184
  have htrace : WordTrace (prefixWord ++ tailWord_207184) baseStart_207184 baseEnd_207184 := by
    simpa [prefixWord, tailWord_207184, baseEnd_207184] using wordTrace_append hprefix tailTrace_207184
  have hstable : (prefixWord ++ tailWord_207184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207184).length < 2 ^ (prefixWord ++ tailWord_207184).sum := by decide
  have hdescent : baseEnd_207184 < baseStart_207184 := by decide
  rcases family_descends (prefixWord ++ tailWord_207184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207243 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 3]
def baseStart_207243 : Nat := 118140960795 + 207243 * 2 ^ 59
def prefixEnd_207243 : Nat := 4983230072969 + 3 ^ 40 * 207243 * 2
def baseEnd_207243 : Nat := 47295676124372397559739

theorem tailTrace_207243 : CollatzResearch.WordTrace tailWord_207243 prefixEnd_207243 47295676124372397559739 := by
  unfold tailWord_207243
  simp only [CollatzResearch.WordTrace]
  refine ⟨7558773188201480131626383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5039182125467653421084255 7558773188201480131626383)
  ·
    refine ⟨11338159782302220197439575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7558773188201480131626383 11338159782302220197439575)
    ·
      refine ⟨17007239673453330296159363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11338159782302220197439575 17007239673453330296159363)
      ·
        refine ⟨25510859510179995444239045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17007239673453330296159363 25510859510179995444239045)
        ·
          refine ⟨4783286158158749145794821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25510859510179995444239045 4783286158158749145794821)
          ·
            refine ⟨896866154654765464836529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4783286158158749145794821 896866154654765464836529)
            ·
              refine ⟨672649615991074098627397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896866154654765464836529 672649615991074098627397)
              ·
                refine ⟨126121802998326393492637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672649615991074098627397 126121802998326393492637)
                ·
                  refine ⟨47295676124372397559739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126121802998326393492637 47295676124372397559739)
                  ·
                    rfl

theorem cell21_207243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3].length) (baseStart_207243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207243 prefixEnd_207243 := by exact prefixLift 207243
  have htrace : WordTrace (prefixWord ++ tailWord_207243) baseStart_207243 baseEnd_207243 := by
    simpa [prefixWord, tailWord_207243, baseEnd_207243] using wordTrace_append hprefix tailTrace_207243
  have hstable : (prefixWord ++ tailWord_207243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207243).length < 2 ^ (prefixWord ++ tailWord_207243).sum := by decide
  have hdescent : baseEnd_207243 < baseStart_207243 := by decide
  rcases family_descends (prefixWord ++ tailWord_207243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207308 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_207308 : Nat := 118140960795 + 207308 * 2 ^ 59
def prefixEnd_207308 : Nat := 4983230072969 + 3 ^ 40 * 207308 * 2
def baseEnd_207308 : Nat := 47310510009946728976273

theorem tailTrace_207308 : CollatzResearch.WordTrace tailWord_207308 prefixEnd_207308 47310510009946728976273 := by
  unfold tailWord_207308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3780571966482998116371289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5040762621977330821828385 3780571966482998116371289)
  ·
    refine ⟨2835428974862248587278467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3780571966482998116371289 2835428974862248587278467)
    ·
      refine ⟨4253143462293372880917701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835428974862248587278467 4253143462293372880917701)
      ·
        refine ⟨797464399180007415172069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4253143462293372880917701 797464399180007415172069)
        ·
          refine ⟨149524574846251390344763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 797464399180007415172069 149524574846251390344763)
          ·
            refine ⟨224286862269377085517145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149524574846251390344763 224286862269377085517145)
            ·
              refine ⟨168215146702032814137859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224286862269377085517145 168215146702032814137859)
              ·
                refine ⟨252322720053049221206789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168215146702032814137859 252322720053049221206789)
                ·
                  refine ⟨47310510009946728976273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252322720053049221206789 47310510009946728976273)
                  ·
                    rfl

theorem cell21_207308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_207308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207308 prefixEnd_207308 := by exact prefixLift 207308
  have htrace : WordTrace (prefixWord ++ tailWord_207308) baseStart_207308 baseEnd_207308 := by
    simpa [prefixWord, tailWord_207308, baseEnd_207308] using wordTrace_append hprefix tailTrace_207308
  have hstable : (prefixWord ++ tailWord_207308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207308).length < 2 ^ (prefixWord ++ tailWord_207308).sum := by decide
  have hdescent : baseEnd_207308 < baseStart_207308 := by decide
  rcases family_descends (prefixWord ++ tailWord_207308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207350 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_207350 : Nat := 118140960795 + 207350 * 2 ^ 59
def prefixEnd_207350 : Nat := 4983230072969 + 3 ^ 40 * 207350 * 2
def baseEnd_207350 : Nat := 47320094982163989276187

theorem tailTrace_207350 : CollatzResearch.WordTrace tailWord_207350 prefixEnd_207350 47320094982163989276187 := by
  unfold tailWord_207350
  simp only [CollatzResearch.WordTrace]
  refine ⟨472667237425864837860719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5041783865875891603847669 472667237425864837860719)
  ·
    refine ⟨709000856138797256791079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472667237425864837860719 709000856138797256791079)
    ·
      refine ⟨1063501284208195885186619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709000856138797256791079 1063501284208195885186619)
      ·
        refine ⟨1595251926312293827779929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063501284208195885186619 1595251926312293827779929)
        ·
          refine ⟨1196438944734220370834947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595251926312293827779929 1196438944734220370834947)
          ·
            refine ⟨1794658417101330556252421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196438944734220370834947 1794658417101330556252421)
            ·
              refine ⟨336498453206499479297329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1794658417101330556252421 336498453206499479297329)
              ·
                refine ⟨252373839904874609472997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336498453206499479297329 252373839904874609472997)
                ·
                  refine ⟨47320094982163989276187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252373839904874609472997 47320094982163989276187)
                  ·
                    rfl

theorem cell21_207350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_207350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207350 prefixEnd_207350 := by exact prefixLift 207350
  have htrace : WordTrace (prefixWord ++ tailWord_207350) baseStart_207350 baseEnd_207350 := by
    simpa [prefixWord, tailWord_207350, baseEnd_207350] using wordTrace_append hprefix tailTrace_207350
  have hstable : (prefixWord ++ tailWord_207350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207350).length < 2 ^ (prefixWord ++ tailWord_207350).sum := by decide
  have hdescent : baseEnd_207350 < baseStart_207350 := by decide
  rcases family_descends (prefixWord ++ tailWord_207350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207364 : List Nat := [2, 3, 2, 3, 1, 1, 3, 6]
def baseStart_207364 : Nat := 118140960795 + 207364 * 2 ^ 59
def prefixEnd_207364 : Nat := 4983230072969 + 3 ^ 40 * 207364 * 2
def baseEnd_207364 : Nat := 15774429990967692014275

theorem tailTrace_207364 : CollatzResearch.WordTrace tailWord_207364 prefixEnd_207364 15774429990967692014275 := by
  unfold tailWord_207364
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781593210381558898390573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5042124280508745197854097 3781593210381558898390573)
  ·
    refine ⟨1418097453893084586896465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3781593210381558898390573 1418097453893084586896465)
    ·
      refine ⟨1063573090419813440172349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1418097453893084586896465 1063573090419813440172349)
      ·
        refine ⟨398839908907430040064631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1063573090419813440172349 398839908907430040064631)
        ·
          refine ⟨598259863361145060096947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398839908907430040064631 598259863361145060096947)
          ·
            refine ⟨897389795041717590145421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598259863361145060096947 897389795041717590145421)
            ·
              refine ⟨336521173140644096304533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897389795041717590145421 336521173140644096304533)
              ·
                refine ⟨15774429990967692014275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 336521173140644096304533 15774429990967692014275)
                ·
                  rfl

theorem cell21_207364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_207364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207364 prefixEnd_207364 := by exact prefixLift 207364
  have htrace : WordTrace (prefixWord ++ tailWord_207364) baseStart_207364 baseEnd_207364 := by
    simpa [prefixWord, tailWord_207364, baseEnd_207364] using wordTrace_append hprefix tailTrace_207364
  have hstable : (prefixWord ++ tailWord_207364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207364).length < 2 ^ (prefixWord ++ tailWord_207364).sum := by decide
  have hdescent : baseEnd_207364 < baseStart_207364 := by decide
  rcases family_descends (prefixWord ++ tailWord_207364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207395 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 3]
def baseStart_207395 : Nat := 118140960795 + 207395 * 2 ^ 59
def prefixEnd_207395 : Nat := 4983230072969 + 3 ^ 40 * 207395 * 2
def baseEnd_207395 : Nat := 47330364595253911026095

theorem tailTrace_207395 : CollatzResearch.WordTrace tailWord_207395 prefixEnd_207395 47330364595253911026095 := by
  unfold tailWord_207395
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564317083650810091159639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5042878055767206727439759 7564317083650810091159639)
  ·
    refine ⟨11346475625476215136739459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7564317083650810091159639 11346475625476215136739459)
    ·
      refine ⟨17019713438214322705109189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11346475625476215136739459 17019713438214322705109189)
      ·
        refine ⟨3191196269665185507207973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17019713438214322705109189 3191196269665185507207973)
        ·
          refine ⟨598349300562222282601495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3191196269665185507207973 598349300562222282601495)
          ·
            refine ⟨897523950843333423902243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598349300562222282601495 897523950843333423902243)
            ·
              refine ⟨1346285926265000135853365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897523950843333423902243 1346285926265000135853365)
              ·
                refine ⟨126214305587343762736253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1346285926265000135853365 126214305587343762736253)
                ·
                  refine ⟨47330364595253911026095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126214305587343762736253 47330364595253911026095)
                  ·
                    rfl

theorem cell21_207395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3].length) (baseStart_207395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207395 prefixEnd_207395 := by exact prefixLift 207395
  have htrace : WordTrace (prefixWord ++ tailWord_207395) baseStart_207395 baseEnd_207395 := by
    simpa [prefixWord, tailWord_207395, baseEnd_207395] using wordTrace_append hprefix tailTrace_207395
  have hstable : (prefixWord ++ tailWord_207395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207395).length < 2 ^ (prefixWord ++ tailWord_207395).sum := by decide
  have hdescent : baseEnd_207395 < baseStart_207395 := by decide
  rcases family_descends (prefixWord ++ tailWord_207395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207409 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_207409 : Nat := 118140960795 + 207409 * 2 ^ 59
def prefixEnd_207409 : Nat := 4983230072969 + 3 ^ 40 * 207409 * 2
def baseEnd_207409 : Nat := 47333559585992997792733

theorem tailTrace_207409 : CollatzResearch.WordTrace tailWord_207409 prefixEnd_207409 47333559585992997792733 := by
  unfold tailWord_207409
  simp only [CollatzResearch.WordTrace]
  refine ⟨7564827705600090482169281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5043218470400060321446187 7564827705600090482169281)
  ·
    refine ⟨5673620779200067861626961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7564827705600090482169281 5673620779200067861626961)
    ·
      refine ⟨4255215584400050896220221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5673620779200067861626961 4255215584400050896220221)
      ·
        refine ⟨1595705844150019086082583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4255215584400050896220221 1595705844150019086082583)
        ·
          refine ⟨2393558766225028629123875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595705844150019086082583 2393558766225028629123875)
          ·
            refine ⟨3590338149337542943685813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393558766225028629123875 3590338149337542943685813)
            ·
              refine ⟨336594201500394650970545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3590338149337542943685813 336594201500394650970545)
              ·
                refine ⟨252445651125295988227909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336594201500394650970545 252445651125295988227909)
                ·
                  refine ⟨47333559585992997792733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252445651125295988227909 47333559585992997792733)
                  ·
                    rfl

theorem cell21_207409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_207409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207409 prefixEnd_207409 := by exact prefixLift 207409
  have htrace : WordTrace (prefixWord ++ tailWord_207409) baseStart_207409 baseEnd_207409 := by
    simpa [prefixWord, tailWord_207409, baseEnd_207409] using wordTrace_append hprefix tailTrace_207409
  have hstable : (prefixWord ++ tailWord_207409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207409).length < 2 ^ (prefixWord ++ tailWord_207409).sum := by decide
  have hdescent : baseEnd_207409 < baseStart_207409 := by decide
  rcases family_descends (prefixWord ++ tailWord_207409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207468 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_207468 : Nat := 118140960795 + 207468 * 2 ^ 59
def prefixEnd_207468 : Nat := 4983230072969 + 3 ^ 40 * 207468 * 2
def baseEnd_207468 : Nat := 47347024189822006309279

theorem tailTrace_207468 : CollatzResearch.WordTrace tailWord_207468 prefixEnd_207468 47347024189822006309279 := by
  unfold tailWord_207468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783489806193171779283529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5044653074924229039044705 3783489806193171779283529)
  ·
    refine ⟨2837617354644878834462647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3783489806193171779283529 2837617354644878834462647)
    ·
      refine ⟨4256426031967318251693971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2837617354644878834462647 4256426031967318251693971)
      ·
        refine ⟨6384639047950977377540957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256426031967318251693971 6384639047950977377540957)
        ·
          refine ⟨2394239642981616516577859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6384639047950977377540957 2394239642981616516577859)
          ·
            refine ⟨3591359464472424774866789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394239642981616516577859 3591359464472424774866789)
            ·
              refine ⟨673379899588579645287523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3591359464472424774866789 673379899588579645287523)
              ·
                refine ⟨1010069849382869467931285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673379899588579645287523 1010069849382869467931285)
                ·
                  refine ⟨47347024189822006309279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1010069849382869467931285 47347024189822006309279)
                  ·
                    rfl

theorem cell21_207468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_207468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207468 prefixEnd_207468 := by exact prefixLift 207468
  have htrace : WordTrace (prefixWord ++ tailWord_207468) baseStart_207468 baseEnd_207468 := by
    simpa [prefixWord, tailWord_207468, baseEnd_207468] using wordTrace_append hprefix tailTrace_207468
  have hstable : (prefixWord ++ tailWord_207468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207468).length < 2 ^ (prefixWord ++ tailWord_207468).sum := by decide
  have hdescent : baseEnd_207468 < baseStart_207468 := by decide
  rcases family_descends (prefixWord ++ tailWord_207468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207564 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_207564 : Nat := 118140960795 + 207564 * 2 ^ 59
def prefixEnd_207564 : Nat := 4983230072969 + 3 ^ 40 * 207564 * 2
def baseEnd_207564 : Nat := 47368932697747172709083

theorem tailTrace_207564 : CollatzResearch.WordTrace tailWord_207564 prefixEnd_207564 47368932697747172709083 := by
  unfold tailWord_207564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785240510019275977030873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5046987346692367969374497 3785240510019275977030873)
  ·
    refine ⟨2838930382514456982773155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3785240510019275977030873 2838930382514456982773155)
    ·
      refine ⟨4258395573771685474159733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838930382514456982773155 4258395573771685474159733)
      ·
        refine ⟨399224585041095513202475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4258395573771685474159733 399224585041095513202475)
        ·
          refine ⟨598836877561643269803713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399224585041095513202475 598836877561643269803713)
          ·
            refine ⟨449127658171232452352785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598836877561643269803713 449127658171232452352785)
            ·
              refine ⟨336845743628424339264589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449127658171232452352785 336845743628424339264589)
              ·
                refine ⟨126317153860659127224221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336845743628424339264589 126317153860659127224221)
                ·
                  refine ⟨47368932697747172709083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126317153860659127224221 47368932697747172709083)
                  ·
                    rfl

theorem cell21_207564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_207564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207564 prefixEnd_207564 := by exact prefixLift 207564
  have htrace : WordTrace (prefixWord ++ tailWord_207564) baseStart_207564 baseEnd_207564 := by
    simpa [prefixWord, tailWord_207564, baseEnd_207564] using wordTrace_append hprefix tailTrace_207564
  have hstable : (prefixWord ++ tailWord_207564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207564).length < 2 ^ (prefixWord ++ tailWord_207564).sum := by decide
  have hdescent : baseEnd_207564 < baseStart_207564 := by decide
  rcases family_descends (prefixWord ++ tailWord_207564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207606 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_207606 : Nat := 118140960795 + 207606 * 2 ^ 59
def prefixEnd_207606 : Nat := 4983230072969 + 3 ^ 40 * 207606 * 2
def baseEnd_207606 : Nat := 47378517669964433008997

theorem tailTrace_207606 : CollatzResearch.WordTrace tailWord_207606 prefixEnd_207606 47378517669964433008997 := by
  unfold tailWord_207606
  simp only [CollatzResearch.WordTrace]
  refine ⟨473250805367899570443167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5048008590590928751393781 473250805367899570443167)
  ·
    refine ⟨709876208051849355664751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473250805367899570443167 709876208051849355664751)
    ·
      refine ⟨1064814312077774033497127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709876208051849355664751 1064814312077774033497127)
      ·
        refine ⟨1597221468116661050245691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064814312077774033497127 1597221468116661050245691)
        ·
          refine ⟨2395832202174991575368537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597221468116661050245691 2395832202174991575368537)
          ·
            refine ⟨1796874151631243681526403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395832202174991575368537 1796874151631243681526403)
            ·
              refine ⟨2695311227446865522289605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796874151631243681526403 2695311227446865522289605)
              ·
                refine ⟨505370855146287285429301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2695311227446865522289605 505370855146287285429301)
                ·
                  refine ⟨47378517669964433008997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 505370855146287285429301 47378517669964433008997)
                  ·
                    rfl

theorem cell21_207606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_207606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207606 prefixEnd_207606 := by exact prefixLift 207606
  have htrace : WordTrace (prefixWord ++ tailWord_207606) baseStart_207606 baseEnd_207606 := by
    simpa [prefixWord, tailWord_207606, baseEnd_207606] using wordTrace_append hprefix tailTrace_207606
  have hstable : (prefixWord ++ tailWord_207606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207606).length < 2 ^ (prefixWord ++ tailWord_207606).sum := by decide
  have hdescent : baseEnd_207606 < baseStart_207606 := by decide
  rcases family_descends (prefixWord ++ tailWord_207606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207620 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_207620 : Nat := 118140960795 + 207620 * 2 ^ 59
def prefixEnd_207620 : Nat := 4983230072969 + 3 ^ 40 * 207620 * 2
def baseEnd_207620 : Nat := 47381712660703519775635

theorem tailTrace_207620 : CollatzResearch.WordTrace tailWord_207620 prefixEnd_207620 47381712660703519775635 := by
  unfold tailWord_207620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786261753917836759050157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5048349005223782345400209 3786261753917836759050157)
  ·
    refine ⟨1419848157719188784643809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3786261753917836759050157 1419848157719188784643809)
    ·
      refine ⟨1064886118289391588482857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1419848157719188784643809 1064886118289391588482857)
      ·
        refine ⟨798664588717043691362143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064886118289391588482857 798664588717043691362143)
        ·
          refine ⟨1197996883075565537043215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798664588717043691362143 1197996883075565537043215)
          ·
            refine ⟨1796995324613348305564823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197996883075565537043215 1796995324613348305564823)
            ·
              refine ⟨2695492986920022458347235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796995324613348305564823 2695492986920022458347235)
              ·
                refine ⟨4043239480380033687520853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695492986920022458347235 4043239480380033687520853)
                ·
                  refine ⟨47381712660703519775635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4043239480380033687520853 47381712660703519775635)
                  ·
                    rfl

theorem cell21_207620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_207620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207620 prefixEnd_207620 := by exact prefixLift 207620
  have htrace : WordTrace (prefixWord ++ tailWord_207620) baseStart_207620 baseEnd_207620 := by
    simpa [prefixWord, tailWord_207620, baseEnd_207620] using wordTrace_append hprefix tailTrace_207620
  have hstable : (prefixWord ++ tailWord_207620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207620).length < 2 ^ (prefixWord ++ tailWord_207620).sum := by decide
  have hdescent : baseEnd_207620 < baseStart_207620 := by decide
  rcases family_descends (prefixWord ++ tailWord_207620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207665 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_207665 : Nat := 118140960795 + 207665 * 2 ^ 59
def prefixEnd_207665 : Nat := 4983230072969 + 3 ^ 40 * 207665 * 2
def baseEnd_207665 : Nat := 47391982273793441525543

theorem tailTrace_207665 : CollatzResearch.WordTrace tailWord_207665 prefixEnd_207665 47391982273793441525543 := by
  unfold tailWord_207665
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574164792672646203488449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5049443195115097468992299 7574164792672646203488449)
  ·
    refine ⟨5680623594504484652616337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7574164792672646203488449 5680623594504484652616337)
    ·
      refine ⟨4260467695878363489462253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680623594504484652616337 4260467695878363489462253)
      ·
        refine ⟨1597675385954386308548345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4260467695878363489462253 1597675385954386308548345)
        ·
          refine ⟨1198256539465789731411259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597675385954386308548345 1198256539465789731411259)
          ·
            refine ⟨1797384809198684597116889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198256539465789731411259 1797384809198684597116889)
            ·
              refine ⟨1348038606899013447837667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797384809198684597116889 1348038606899013447837667)
              ·
                refine ⟨2022057910348520171756501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348038606899013447837667 2022057910348520171756501)
                ·
                  refine ⟨47391982273793441525543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2022057910348520171756501 47391982273793441525543)
                  ·
                    rfl

theorem cell21_207665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_207665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207665 prefixEnd_207665 := by exact prefixLift 207665
  have htrace : WordTrace (prefixWord ++ tailWord_207665) baseStart_207665 baseEnd_207665 := by
    simpa [prefixWord, tailWord_207665, baseEnd_207665] using wordTrace_append hprefix tailTrace_207665
  have hstable : (prefixWord ++ tailWord_207665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207665).length < 2 ^ (prefixWord ++ tailWord_207665).sum := by decide
  have hdescent : baseEnd_207665 < baseStart_207665 := by decide
  rcases family_descends (prefixWord ++ tailWord_207665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207696 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_207696 : Nat := 118140960795 + 207696 * 2 ^ 59
def prefixEnd_207696 : Nat := 4983230072969 + 3 ^ 40 * 207696 * 2
def baseEnd_207696 : Nat := 47399056896144276508813

theorem tailTrace_207696 : CollatzResearch.WordTrace tailWord_207696 prefixEnd_207696 47399056896144276508813 := by
  unfold tailWord_207696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787647727780169248933471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5050196970373558998577961 3787647727780169248933471)
  ·
    refine ⟨5681471591670253873400207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787647727780169248933471 5681471591670253873400207)
    ·
      refine ⟨8522207387505380810100311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681471591670253873400207 8522207387505380810100311)
      ·
        refine ⟨12783311081258071215150467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522207387505380810100311 12783311081258071215150467)
        ·
          refine ⟨19174966621887106822725701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12783311081258071215150467 19174966621887106822725701)
          ·
            refine ⟨3595306241603832529261069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19174966621887106822725701 3595306241603832529261069)
            ·
              refine ⟨1348239840601437198472901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3595306241603832529261069 1348239840601437198472901)
              ·
                refine ⟨252794970112769474713669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1348239840601437198472901 252794970112769474713669)
                ·
                  refine ⟨47399056896144276508813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252794970112769474713669 47399056896144276508813)
                  ·
                    rfl

theorem cell21_207696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_207696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207696 prefixEnd_207696 := by exact prefixLift 207696
  have htrace : WordTrace (prefixWord ++ tailWord_207696) baseStart_207696 baseEnd_207696 := by
    simpa [prefixWord, tailWord_207696, baseEnd_207696] using wordTrace_append hprefix tailTrace_207696
  have hstable : (prefixWord ++ tailWord_207696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207696).length < 2 ^ (prefixWord ++ tailWord_207696).sum := by decide
  have hdescent : baseEnd_207696 < baseStart_207696 := by decide
  rcases family_descends (prefixWord ++ tailWord_207696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207831 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_207831 : Nat := 118140960795 + 207831 * 2 ^ 59
def prefixEnd_207831 : Nat := 4983230072969 + 3 ^ 40 * 207831 * 2
def baseEnd_207831 : Nat := 47429865735414041758537

theorem tailTrace_207831 : CollatzResearch.WordTrace tailWord_207831 prefixEnd_207831 47429865735414041758537 := by
  unfold tailWord_207831
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580219310071256554031347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5053479540047504369354231 7580219310071256554031347)
  ·
    refine ⟨11370328965106884831047021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580219310071256554031347 11370328965106884831047021)
    ·
      refine ⟨4263873361915081811642633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11370328965106884831047021 4263873361915081811642633)
      ·
        refine ⟨3197905021436311358731975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4263873361915081811642633 3197905021436311358731975)
        ·
          refine ⟨4796857532154467038097963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197905021436311358731975 4796857532154467038097963)
          ·
            refine ⟨7195286298231700557146945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796857532154467038097963 7195286298231700557146945)
            ·
              refine ⟨5396464723673775417860209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7195286298231700557146945 5396464723673775417860209)
              ·
                refine ⟨4047348542755331563395157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5396464723673775417860209 4047348542755331563395157)
                ·
                  refine ⟨47429865735414041758537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4047348542755331563395157 47429865735414041758537)
                  ·
                    rfl

theorem cell21_207831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_207831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207831 prefixEnd_207831 := by exact prefixLift 207831
  have htrace : WordTrace (prefixWord ++ tailWord_207831) baseStart_207831 baseEnd_207831 := by
    simpa [prefixWord, tailWord_207831, baseEnd_207831] using wordTrace_append hprefix tailTrace_207831
  have hstable : (prefixWord ++ tailWord_207831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207831).length < 2 ^ (prefixWord ++ tailWord_207831).sum := by decide
  have hdescent : baseEnd_207831 < baseStart_207831 := by decide
  rcases family_descends (prefixWord ++ tailWord_207831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207860 : List Nat := [2, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_207860 : Nat := 118140960795 + 207860 * 2 ^ 59
def prefixEnd_207860 : Nat := 4983230072969 + 3 ^ 40 * 207860 * 2
def baseEnd_207860 : Nat := 47436483930516435775145

theorem tailTrace_207860 : CollatzResearch.WordTrace tailWord_207860 prefixEnd_207860 47436483930516435775145 := by
  unfold tailWord_207860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790638513483097253418517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5054184684644129671224689 3790638513483097253418517)
  ·
    refine ⟨177686180319520183753993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3790638513483097253418517 177686180319520183753993)
    ·
      refine ⟨133264635239640137815495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177686180319520183753993 133264635239640137815495)
      ·
        refine ⟨199896952859460206723243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133264635239640137815495 199896952859460206723243)
        ·
          refine ⟨299845429289190310084865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199896952859460206723243 299845429289190310084865)
          ·
            refine ⟨224884071966892732563649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299845429289190310084865 224884071966892732563649)
            ·
              refine ⟨168663053975169549422737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224884071966892732563649 168663053975169549422737)
              ·
                refine ⟨126497290481377162067053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168663053975169549422737 126497290481377162067053)
                ·
                  refine ⟨47436483930516435775145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126497290481377162067053 47436483930516435775145)
                  ·
                    rfl

theorem cell21_207860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_207860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207860 prefixEnd_207860 := by exact prefixLift 207860
  have htrace : WordTrace (prefixWord ++ tailWord_207860) baseStart_207860 baseEnd_207860 := by
    simpa [prefixWord, tailWord_207860, baseEnd_207860] using wordTrace_append hprefix tailTrace_207860
  have hstable : (prefixWord ++ tailWord_207860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207860).length < 2 ^ (prefixWord ++ tailWord_207860).sum := by decide
  have hdescent : baseEnd_207860 < baseStart_207860 := by decide
  rcases family_descends (prefixWord ++ tailWord_207860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207868 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_207868 : Nat := 118140960795 + 207868 * 2 ^ 59
def prefixEnd_207868 : Nat := 4983230072969 + 3 ^ 40 * 207868 * 2
def baseEnd_207868 : Nat := 47438309639510199641795

theorem tailTrace_207868 : CollatzResearch.WordTrace tailWord_207868 prefixEnd_207868 47438309639510199641795 := by
  unfold tailWord_207868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790784405468605936564129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5054379207291474582085505 3790784405468605936564129)
  ·
    refine ⟨2843088304101454452423097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3790784405468605936564129 2843088304101454452423097)
    ·
      refine ⟨2132316228076090839317323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843088304101454452423097 2132316228076090839317323)
      ·
        refine ⟨3198474342114136258975985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132316228076090839317323 3198474342114136258975985)
        ·
          refine ⟨2398855756585602194231989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198474342114136258975985 2398855756585602194231989)
          ·
            refine ⟨224892727179900205709249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2398855756585602194231989 224892727179900205709249)
            ·
              refine ⟨168669545384925154281937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224892727179900205709249 168669545384925154281937)
              ·
                refine ⟨126502159038693865711453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168669545384925154281937 126502159038693865711453)
                ·
                  refine ⟨47438309639510199641795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126502159038693865711453 47438309639510199641795)
                  ·
                    rfl

theorem cell21_207868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_207868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207868 prefixEnd_207868 := by exact prefixLift 207868
  have htrace : WordTrace (prefixWord ++ tailWord_207868) baseStart_207868 baseEnd_207868 := by
    simpa [prefixWord, tailWord_207868, baseEnd_207868] using wordTrace_append hprefix tailTrace_207868
  have hstable : (prefixWord ++ tailWord_207868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207868).length < 2 ^ (prefixWord ++ tailWord_207868).sum := by decide
  have hdescent : baseEnd_207868 < baseStart_207868 := by decide
  rcases family_descends (prefixWord ++ tailWord_207868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207893 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_207893 : Nat := 118140960795 + 207893 * 2 ^ 59
def prefixEnd_207893 : Nat := 4983230072969 + 3 ^ 40 * 207893 * 2
def baseEnd_207893 : Nat := 47444014980115711725077

theorem tailTrace_207893 : CollatzResearch.WordTrace tailWord_207893 prefixEnd_207893 47444014980115711725077 := by
  unfold tailWord_207893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582480635846641142788333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5054987090564427428525555 7582480635846641142788333)
  ·
    refine ⟨2843430238442490428545625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7582480635846641142788333 2843430238442490428545625)
    ·
      refine ⟨2132572678831867821409219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843430238442490428545625 2132572678831867821409219)
      ·
        refine ⟨3198859018247801732113829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132572678831867821409219 3198859018247801732113829)
        ·
          refine ⟨599786065921462824771343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3198859018247801732113829 599786065921462824771343)
          ·
            refine ⟨899679098882194237157015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599786065921462824771343 899679098882194237157015)
            ·
              refine ⟨1349518648323291355735523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899679098882194237157015 1349518648323291355735523)
              ·
                refine ⟨2024277972484937033603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349518648323291355735523 2024277972484937033603285)
                ·
                  refine ⟨47444014980115711725077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2024277972484937033603285 47444014980115711725077)
                  ·
                    rfl

theorem cell21_207893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_207893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207893 prefixEnd_207893 := by exact prefixLift 207893
  have htrace : WordTrace (prefixWord ++ tailWord_207893) baseStart_207893 baseEnd_207893 := by
    simpa [prefixWord, tailWord_207893, baseEnd_207893] using wordTrace_append hprefix tailTrace_207893
  have hstable : (prefixWord ++ tailWord_207893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207893).length < 2 ^ (prefixWord ++ tailWord_207893).sum := by decide
  have hdescent : baseEnd_207893 < baseStart_207893 := by decide
  rcases family_descends (prefixWord ++ tailWord_207893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207983 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_207983 : Nat := 118140960795 + 207983 * 2 ^ 59
def prefixEnd_207983 : Nat := 4983230072969 + 3 ^ 40 * 207983 * 2
def baseEnd_207983 : Nat := 47464554206295555224893

theorem tailTrace_207983 : CollatzResearch.WordTrace tailWord_207983 prefixEnd_207983 47464554206295555224893 := by
  unfold tailWord_207983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585763205520586513564603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5057175470347057675709735 7585763205520586513564603)
  ·
    refine ⟨11378644808280879770346905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7585763205520586513564603 11378644808280879770346905)
    ·
      refine ⟨8533983606210659827760179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11378644808280879770346905 8533983606210659827760179)
      ·
        refine ⟨12800975409315989741640269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8533983606210659827760179 12800975409315989741640269)
        ·
          refine ⟨4800365778493496153115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12800975409315989741640269 4800365778493496153115101)
          ·
            refine ⟨1800137166935061057418163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4800365778493496153115101 1800137166935061057418163)
            ·
              refine ⟨2700205750402591586127245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800137166935061057418163 2700205750402591586127245)
              ·
                refine ⟨1012577156400971844797717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700205750402591586127245 1012577156400971844797717)
                ·
                  refine ⟨47464554206295555224893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1012577156400971844797717 47464554206295555224893)
                  ·
                    rfl

theorem cell21_207983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_207983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_207983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_207983 prefixEnd_207983 := by exact prefixLift 207983
  have htrace : WordTrace (prefixWord ++ tailWord_207983) baseStart_207983 baseEnd_207983 := by
    simpa [prefixWord, tailWord_207983, baseEnd_207983] using wordTrace_append hprefix tailTrace_207983
  have hstable : (prefixWord ++ tailWord_207983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207983).length < 2 ^ (prefixWord ++ tailWord_207983).sum := by decide
  have hdescent : baseEnd_207983 < baseStart_207983 := by decide
  rcases family_descends (prefixWord ++ tailWord_207983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208031 : List Nat := [1, 1, 2, 6, 3, 8]
def baseStart_208031 : Nat := 118140960795 + 208031 * 2 ^ 59
def prefixEnd_208031 : Nat := 4983230072969 + 3 ^ 40 * 208031 * 2
def baseEnd_208031 : Nat := 1758352165194745867585

theorem tailTrace_208031 : CollatzResearch.WordTrace tailWord_208031 prefixEnd_208031 1758352165194745867585 := by
  unfold tailWord_208031
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587513909346690711311947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5058342606231127140874631 7587513909346690711311947)
  ·
    refine ⟨11381270864020036066967921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7587513909346690711311947 11381270864020036066967921)
    ·
      refine ⟨8535953148015027050225941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11381270864020036066967921 8535953148015027050225941)
      ·
        refine ⟨400122803813204392979341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8535953148015027050225941 400122803813204392979341)
        ·
          refine ⟨150046051429951647367253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400122803813204392979341 150046051429951647367253)
          ·
            refine ⟨1758352165194745867585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 150046051429951647367253 1758352165194745867585)
            ·
              rfl

theorem cell21_208031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 8].length) (baseStart_208031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208031 prefixEnd_208031 := by exact prefixLift 208031
  have htrace : WordTrace (prefixWord ++ tailWord_208031) baseStart_208031 baseEnd_208031 := by
    simpa [prefixWord, tailWord_208031, baseEnd_208031] using wordTrace_append hprefix tailTrace_208031
  have hstable : (prefixWord ++ tailWord_208031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208031).length < 2 ^ (prefixWord ++ tailWord_208031).sum := by decide
  have hdescent : baseEnd_208031 < baseStart_208031 := by decide
  rcases family_descends (prefixWord ++ tailWord_208031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208034 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_208034 : Nat := 118140960795 + 208034 * 2 ^ 59
def prefixEnd_208034 : Nat := 4983230072969 + 3 ^ 40 * 208034 * 2
def baseEnd_208034 : Nat := 47476193101130799874789

theorem tailTrace_208034 : CollatzResearch.WordTrace tailWord_208034 prefixEnd_208034 47476193101130799874789 := by
  unfold tailWord_208034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896905832083955555917789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5058415552223881482447437 1896905832083955555917789)
  ·
    refine ⟨711339687031483333469171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1896905832083955555917789 711339687031483333469171)
    ·
      refine ⟨1067009530547225000203757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711339687031483333469171 1067009530547225000203757)
      ·
        refine ⟨400128573955209375076409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1067009530547225000203757 400128573955209375076409)
        ·
          refine ⟨300096430466407031307307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400128573955209375076409 300096430466407031307307)
          ·
            refine ⟨450144645699610546960961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300096430466407031307307 450144645699610546960961)
            ·
              refine ⟨337608484274707910220721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450144645699610546960961 337608484274707910220721)
              ·
                refine ⟨253206363206030932665541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337608484274707910220721 253206363206030932665541)
                ·
                  refine ⟨47476193101130799874789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253206363206030932665541 47476193101130799874789)
                  ·
                    rfl

theorem cell21_208034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_208034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208034 prefixEnd_208034 := by exact prefixLift 208034
  have htrace : WordTrace (prefixWord ++ tailWord_208034) baseStart_208034 baseEnd_208034 := by
    simpa [prefixWord, tailWord_208034, baseEnd_208034] using wordTrace_append hprefix tailTrace_208034
  have hstable : (prefixWord ++ tailWord_208034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208034).length < 2 ^ (prefixWord ++ tailWord_208034).sum := by decide
  have hdescent : baseEnd_208034 < baseStart_208034 := by decide
  rcases family_descends (prefixWord ++ tailWord_208034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208062 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_208062 : Nat := 118140960795 + 208062 * 2 ^ 59
def prefixEnd_208062 : Nat := 4983230072969 + 3 ^ 40 * 208062 * 2
def baseEnd_208062 : Nat := 47482583082608973408065

theorem tailTrace_208062 : CollatzResearch.WordTrace tailWord_208062 prefixEnd_208062 47482583082608973408065 := by
  unfold tailWord_208062
  simp only [CollatzResearch.WordTrace]
  refine ⟨948580571529297875711305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5059096381489588670460293 948580571529297875711305)
  ·
    refine ⟨711435428646973406783479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 948580571529297875711305 711435428646973406783479)
    ·
      refine ⟨1067153142970460110175219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 711435428646973406783479 1067153142970460110175219)
      ·
        refine ⟨1600729714455690165262829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067153142970460110175219 1600729714455690165262829)
        ·
          refine ⟨600273642920883811973561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1600729714455690165262829 600273642920883811973561)
          ·
            refine ⟨450205232190662858980171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600273642920883811973561 450205232190662858980171)
            ·
              refine ⟨675307848285994288470257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450205232190662858980171 675307848285994288470257)
              ·
                refine ⟨506480886214495716352693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675307848285994288470257 506480886214495716352693)
                ·
                  refine ⟨47482583082608973408065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 506480886214495716352693 47482583082608973408065)
                  ·
                    rfl

theorem cell21_208062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_208062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208062 prefixEnd_208062 := by exact prefixLift 208062
  have htrace : WordTrace (prefixWord ++ tailWord_208062) baseStart_208062 baseEnd_208062 := by
    simpa [prefixWord, tailWord_208062, baseEnd_208062] using wordTrace_append hprefix tailTrace_208062
  have hstable : (prefixWord ++ tailWord_208062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208062).length < 2 ^ (prefixWord ++ tailWord_208062).sum := by decide
  have hdescent : baseEnd_208062 < baseStart_208062 := by decide
  rcases family_descends (prefixWord ++ tailWord_208062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208093 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_208093 : Nat := 118140960795 + 208093 * 2 ^ 59
def prefixEnd_208093 : Nat := 4983230072969 + 3 ^ 40 * 208093 * 2
def baseEnd_208093 : Nat := 47489657704959808391335

theorem tailTrace_208093 : CollatzResearch.WordTrace tailWord_208093 prefixEnd_208093 47489657704959808391335 := by
  unfold tailWord_208093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589775235122075300068933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5059850156748050200045955 7589775235122075300068933)
  ·
    refine ⟨1423082856585389118762925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7589775235122075300068933 1423082856585389118762925)
    ·
      refine ⟨533656071219520919536097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1423082856585389118762925 533656071219520919536097)
      ·
        refine ⟨400242053414640689652073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533656071219520919536097 400242053414640689652073)
        ·
          refine ⟨300181540060980517239055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400242053414640689652073 300181540060980517239055)
          ·
            refine ⟨450272310091470775858583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300181540060980517239055 450272310091470775858583)
            ·
              refine ⟨675408465137206163787875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450272310091470775858583 675408465137206163787875)
              ·
                refine ⟨1013112697705809245681813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675408465137206163787875 1013112697705809245681813)
                ·
                  refine ⟨47489657704959808391335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1013112697705809245681813 47489657704959808391335)
                  ·
                    rfl

theorem cell21_208093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_208093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208093 prefixEnd_208093 := by exact prefixLift 208093
  have htrace : WordTrace (prefixWord ++ tailWord_208093) baseStart_208093 baseEnd_208093 := by
    simpa [prefixWord, tailWord_208093, baseEnd_208093] using wordTrace_append hprefix tailTrace_208093
  have hstable : (prefixWord ++ tailWord_208093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208093).length < 2 ^ (prefixWord ++ tailWord_208093).sum := by decide
  have hdescent : baseEnd_208093 < baseStart_208093 := by decide
  rcases family_descends (prefixWord ++ tailWord_208093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208124 : List Nat := [2, 2, 2, 1, 5, 2, 2, 5]
def baseStart_208124 : Nat := 118140960795 + 208124 * 2 ^ 59
def prefixEnd_208124 : Nat := 4983230072969 + 3 ^ 40 * 208124 * 2
def baseEnd_208124 : Nat := 15832244109103547791535

theorem tailTrace_208124 : CollatzResearch.WordTrace tailWord_208124 prefixEnd_208124 15832244109103547791535 := by
  unfold tailWord_208124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795452949004883797223713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5060603932006511729631617 3795452949004883797223713)
  ·
    refine ⟨2846589711753662847917785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3795452949004883797223713 2846589711753662847917785)
    ·
      refine ⟨2134942283815247135938339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2846589711753662847917785 2134942283815247135938339)
      ·
        refine ⟨3202413425722870703907509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134942283815247135938339 3202413425722870703907509)
        ·
          refine ⟨300226258661519128491329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3202413425722870703907509 300226258661519128491329)
          ·
            refine ⟨225169693996139346368497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300226258661519128491329 225169693996139346368497)
            ·
              refine ⟨168877270497104509776373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225169693996139346368497 168877270497104509776373)
              ·
                refine ⟨15832244109103547791535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168877270497104509776373 15832244109103547791535)
                ·
                  rfl

theorem cell21_208124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_208124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208124 prefixEnd_208124 := by exact prefixLift 208124
  have htrace : WordTrace (prefixWord ++ tailWord_208124) baseStart_208124 baseEnd_208124 := by
    simpa [prefixWord, tailWord_208124, baseEnd_208124] using wordTrace_append hprefix tailTrace_208124
  have hstable : (prefixWord ++ tailWord_208124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208124).length < 2 ^ (prefixWord ++ tailWord_208124).sum := by decide
  have hdescent : baseEnd_208124 < baseStart_208124 := by decide
  rcases family_descends (prefixWord ++ tailWord_208124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208228 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_208228 : Nat := 118140960795 + 208228 * 2 ^ 59
def prefixEnd_208228 : Nat := 4983230072969 + 3 ^ 40 * 208228 * 2
def baseEnd_208228 : Nat := 47520466544229573641059

theorem tailTrace_208228 : CollatzResearch.WordTrace tailWord_208228 prefixEnd_208228 47520466544229573641059 := by
  unfold tailWord_208228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797349544816496678116669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5063132726421995570822225 3797349544816496678116669)
  ·
    refine ⟨1424006079306186254293751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3797349544816496678116669 1424006079306186254293751)
    ·
      refine ⟨2136009118959279381440627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424006079306186254293751 2136009118959279381440627)
      ·
        refine ⟨3204013678438919072160941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136009118959279381440627 3204013678438919072160941)
        ·
          refine ⟨1201505129414594652060353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3204013678438919072160941 1201505129414594652060353)
          ·
            refine ⟨901128847060945989045265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201505129414594652060353 901128847060945989045265)
            ·
              refine ⟨675846635295709491783949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901128847060945989045265 675846635295709491783949)
              ·
                refine ⟨253442488235891059418981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675846635295709491783949 253442488235891059418981)
                ·
                  refine ⟨47520466544229573641059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253442488235891059418981 47520466544229573641059)
                  ·
                    rfl

theorem cell21_208228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_208228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208228 prefixEnd_208228 := by exact prefixLift 208228
  have htrace : WordTrace (prefixWord ++ tailWord_208228) baseStart_208228 baseEnd_208228 := by
    simpa [prefixWord, tailWord_208228, baseEnd_208228] using wordTrace_append hprefix tailTrace_208228
  have hstable : (prefixWord ++ tailWord_208228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208228).length < 2 ^ (prefixWord ++ tailWord_208228).sum := by decide
  have hdescent : baseEnd_208228 < baseStart_208228 := by decide
  rcases family_descends (prefixWord ++ tailWord_208228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208324 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_208324 : Nat := 118140960795 + 208324 * 2 ^ 59
def prefixEnd_208324 : Nat := 4983230072969 + 3 ^ 40 * 208324 * 2
def baseEnd_208324 : Nat := 47542375052154740040863

theorem tailTrace_208324 : CollatzResearch.WordTrace tailWord_208324 prefixEnd_208324 47542375052154740040863 := by
  unfold tailWord_208324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799100248642600875864013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5065466998190134501152017 3799100248642600875864013)
  ·
    refine ⟨1424662593240975328449005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3799100248642600875864013 1424662593240975328449005)
    ·
      refine ⟨534248472465365748168377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1424662593240975328449005 534248472465365748168377)
      ·
        refine ⟨400686354349024311126283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534248472465365748168377 400686354349024311126283)
        ·
          refine ⟨601029531523536466689425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400686354349024311126283 601029531523536466689425)
          ·
            refine ⟨450772148642652350017069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601029531523536466689425 450772148642652350017069)
            ·
              refine ⟨169039555740994631256401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450772148642652350017069 169039555740994631256401)
              ·
                refine ⟨126779666805745973442301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169039555740994631256401 126779666805745973442301)
                ·
                  refine ⟨47542375052154740040863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126779666805745973442301 47542375052154740040863)
                  ·
                    rfl

theorem cell21_208324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_208324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208324 prefixEnd_208324 := by exact prefixLift 208324
  have htrace : WordTrace (prefixWord ++ tailWord_208324) baseStart_208324 baseEnd_208324 := by
    simpa [prefixWord, tailWord_208324, baseEnd_208324] using wordTrace_append hprefix tailTrace_208324
  have hstable : (prefixWord ++ tailWord_208324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208324).length < 2 ^ (prefixWord ++ tailWord_208324).sum := by decide
  have hdescent : baseEnd_208324 < baseStart_208324 := by decide
  rcases family_descends (prefixWord ++ tailWord_208324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208366 : List Nat := [4, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_208366 : Nat := 118140960795 + 208366 * 2 ^ 59
def prefixEnd_208366 : Nat := 4983230072969 + 3 ^ 40 * 208366 * 2
def baseEnd_208366 : Nat := 47551960024372000340777

theorem tailTrace_208366 : CollatzResearch.WordTrace tailWord_208366 prefixEnd_208366 47551960024372000340777 := by
  unfold tailWord_208366
  simp only [CollatzResearch.WordTrace]
  refine ⟨949966545391630365594619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5066488242088695283171301 949966545391630365594619)
  ·
    refine ⟨1424949818087445548391929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949966545391630365594619 1424949818087445548391929)
    ·
      refine ⟨1068712363565584161293947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1424949818087445548391929 1068712363565584161293947)
      ·
        refine ⟨1603068545348376241940921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068712363565584161293947 1603068545348376241940921)
        ·
          refine ⟨1202301409011282181455691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603068545348376241940921 1202301409011282181455691)
          ·
            refine ⟨1803452113516923272183537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202301409011282181455691 1803452113516923272183537)
            ·
              refine ⟨1352589085137692454137653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803452113516923272183537 1352589085137692454137653)
              ·
                refine ⟨126805226731658667575405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1352589085137692454137653 126805226731658667575405)
                ·
                  refine ⟨47551960024372000340777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126805226731658667575405 47551960024372000340777)
                  ·
                    rfl

theorem cell21_208366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_208366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208366 prefixEnd_208366 := by exact prefixLift 208366
  have htrace : WordTrace (prefixWord ++ tailWord_208366) baseStart_208366 baseEnd_208366 := by
    simpa [prefixWord, tailWord_208366, baseEnd_208366] using wordTrace_append hprefix tailTrace_208366
  have hstable : (prefixWord ++ tailWord_208366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208366).length < 2 ^ (prefixWord ++ tailWord_208366).sum := by decide
  have hdescent : baseEnd_208366 < baseStart_208366 := by decide
  rcases family_descends (prefixWord ++ tailWord_208366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208394 : List Nat := [3, 1, 2, 2, 2, 2, 3, 6]
def baseStart_208394 : Nat := 118140960795 + 208394 * 2 ^ 59
def prefixEnd_208394 : Nat := 4983230072969 + 3 ^ 40 * 208394 * 2
def baseEnd_208394 : Nat := 15852783335283391291351

theorem tailTrace_208394 : CollatzResearch.WordTrace tailWord_208394 prefixEnd_208394 15852783335283391291351 := by
  unfold tailWord_208394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900188401757900926694059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5067169071354402471184157 1900188401757900926694059)
  ·
    refine ⟨2850282602636851390041089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900188401757900926694059 2850282602636851390041089)
    ·
      refine ⟨2137711951977638542530817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2850282602636851390041089 2137711951977638542530817)
      ·
        refine ⟨1603283963983228906898113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2137711951977638542530817 1603283963983228906898113)
        ·
          refine ⟨1202462972987421680173585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603283963983228906898113 1202462972987421680173585)
          ·
            refine ⟨901847229740566260130189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202462972987421680173585 901847229740566260130189)
            ·
              refine ⟨338192711152712347548821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 901847229740566260130189 338192711152712347548821)
              ·
                refine ⟨15852783335283391291351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 338192711152712347548821 15852783335283391291351)
                ·
                  rfl

theorem cell21_208394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_208394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208394 prefixEnd_208394 := by exact prefixLift 208394
  have htrace : WordTrace (prefixWord ++ tailWord_208394) baseStart_208394 baseEnd_208394 := by
    simpa [prefixWord, tailWord_208394, baseEnd_208394] using wordTrace_append hprefix tailTrace_208394
  have hstable : (prefixWord ++ tailWord_208394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208394).length < 2 ^ (prefixWord ++ tailWord_208394).sum := by decide
  have hdescent : baseEnd_208394 < baseStart_208394 := by decide
  rcases family_descends (prefixWord ++ tailWord_208394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208439 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_208439 : Nat := 118140960795 + 208439 * 2 ^ 59
def prefixEnd_208439 : Nat := 4983230072969 + 3 ^ 40 * 208439 * 2
def baseEnd_208439 : Nat := 47568619618940095623961

theorem tailTrace_208439 : CollatzResearch.WordTrace tailWord_208439 prefixEnd_208439 47568619618940095623961 := by
  unfold tailWord_208439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602394891868576392164371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5068263261245717594776247 7602394891868576392164371)
  ·
    refine ⟨11403592337802864588246557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7602394891868576392164371 11403592337802864588246557)
    ·
      refine ⟨4276347126676074220592459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11403592337802864588246557 4276347126676074220592459)
      ·
        refine ⟨6414520690014111330888689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276347126676074220592459 6414520690014111330888689)
        ·
          refine ⟨4810890517510583498166517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6414520690014111330888689 4810890517510583498166517)
          ·
            refine ⟨451020986016617202953111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4810890517510583498166517 451020986016617202953111)
            ·
              refine ⟨676531479024925804429667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451020986016617202953111 676531479024925804429667)
              ·
                refine ⟨1014797218537388706644501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676531479024925804429667 1014797218537388706644501)
                ·
                  refine ⟨47568619618940095623961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1014797218537388706644501 47568619618940095623961)
                  ·
                    rfl

theorem cell21_208439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_208439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208439 prefixEnd_208439 := by exact prefixLift 208439
  have htrace : WordTrace (prefixWord ++ tailWord_208439) baseStart_208439 baseEnd_208439 := by
    simpa [prefixWord, tailWord_208439, baseEnd_208439] using wordTrace_append hprefix tailTrace_208439
  have hstable : (prefixWord ++ tailWord_208439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208439).length < 2 ^ (prefixWord ++ tailWord_208439).sum := by decide
  have hdescent : baseEnd_208439 < baseStart_208439 := by decide
  rcases family_descends (prefixWord ++ tailWord_208439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208453 : List Nat := [1, 3, 1, 1, 1, 4, 2, 8]
def baseStart_208453 : Nat := 118140960795 + 208453 * 2 ^ 59
def prefixEnd_208453 : Nat := 4983230072969 + 3 ^ 40 * 208453 * 2
def baseEnd_208453 : Nat := 15857271536559727463533

theorem tailTrace_208453 : CollatzResearch.WordTrace tailWord_208453 prefixEnd_208453 15857271536559727463533 := by
  unfold tailWord_208453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602905513817856783174013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5068603675878571188782675 7602905513817856783174013)
  ·
    refine ⟨2851089567681696293690255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7602905513817856783174013 2851089567681696293690255)
    ·
      refine ⟨4276634351522544440535383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851089567681696293690255 4276634351522544440535383)
      ·
        refine ⟨6414951527283816660803075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276634351522544440535383 6414951527283816660803075)
        ·
          refine ⟨9622427290925724991204613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414951527283816660803075 9622427290925724991204613)
          ·
            refine ⟨1804205117048573435850865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9622427290925724991204613 1804205117048573435850865)
            ·
              refine ⟨1353153837786430076888149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804205117048573435850865 1353153837786430076888149)
              ·
                refine ⟨15857271536559727463533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1353153837786430076888149 15857271536559727463533)
                ·
                  rfl

theorem cell21_208453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_208453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208453 prefixEnd_208453 := by exact prefixLift 208453
  have htrace : WordTrace (prefixWord ++ tailWord_208453) baseStart_208453 baseEnd_208453 := by
    simpa [prefixWord, tailWord_208453, baseEnd_208453] using wordTrace_append hprefix tailTrace_208453
  have hstable : (prefixWord ++ tailWord_208453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208453).length < 2 ^ (prefixWord ++ tailWord_208453).sum := by decide
  have hdescent : baseEnd_208453 < baseStart_208453 := by decide
  rcases family_descends (prefixWord ++ tailWord_208453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208546 : List Nat := [3, 3, 1, 4, 10]
def baseStart_208546 : Nat := 118140960795 + 208546 * 2 ^ 59
def prefixEnd_208546 : Nat := 4983230072969 + 3 ^ 40 * 208546 * 2
def baseEnd_208546 : Nat := 587568376255946757289

theorem tailTrace_208546 : CollatzResearch.WordTrace tailWord_208546 prefixEnd_208546 587568376255946757289 := by
  unfold tailWord_208546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901574375620233416577373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5070865001653955777539661 1901574375620233416577373)
  ·
    refine ⟨713090390857587531216515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1901574375620233416577373 713090390857587531216515)
    ·
      refine ⟨1069635586286381296824773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 713090390857587531216515 1069635586286381296824773)
      ·
        refine ⟨200556672428696493154645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1069635586286381296824773 200556672428696493154645)
        ·
          refine ⟨587568376255946757289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 200556672428696493154645 587568376255946757289)
          ·
            rfl

theorem cell21_208546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 10].length) (baseStart_208546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208546 prefixEnd_208546 := by exact prefixLift 208546
  have htrace : WordTrace (prefixWord ++ tailWord_208546) baseStart_208546 baseEnd_208546 := by
    simpa [prefixWord, tailWord_208546, baseEnd_208546] using wordTrace_append hprefix tailTrace_208546
  have hstable : (prefixWord ++ tailWord_208546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208546).length < 2 ^ (prefixWord ++ tailWord_208546).sum := by decide
  have hdescent : baseEnd_208546 < baseStart_208546 := by decide
  rcases family_descends (prefixWord ++ tailWord_208546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208594 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_208594 : Nat := 118140960795 + 208594 * 2 ^ 59
def prefixEnd_208594 : Nat := 4983230072969 + 3 ^ 40 * 208594 * 2
def baseEnd_208594 : Nat := 47603992730694270540311

theorem tailTrace_208594 : CollatzResearch.WordTrace tailWord_208594 prefixEnd_208594 47603992730694270540311 := by
  unfold tailWord_208594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902012051576759466014209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5072032137538025242704557 1902012051576759466014209)
  ·
    refine ⟨1426509038682569599510657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902012051576759466014209 1426509038682569599510657)
    ·
      refine ⟨1069881779011927199632993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1426509038682569599510657 1069881779011927199632993)
      ·
        refine ⟨802411334258945399724745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069881779011927199632993 802411334258945399724745)
        ·
          refine ⟨601808500694209049793559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802411334258945399724745 601808500694209049793559)
          ·
            refine ⟨902712751041313574690339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601808500694209049793559 902712751041313574690339)
            ·
              refine ⟨1354069126561970362035509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902712751041313574690339 1354069126561970362035509)
              ·
                refine ⟨126943980615184721440829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1354069126561970362035509 126943980615184721440829)
                ·
                  refine ⟨47603992730694270540311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126943980615184721440829 47603992730694270540311)
                  ·
                    rfl

theorem cell21_208594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_208594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208594 prefixEnd_208594 := by exact prefixLift 208594
  have htrace : WordTrace (prefixWord ++ tailWord_208594) baseStart_208594 baseEnd_208594 := by
    simpa [prefixWord, tailWord_208594, baseEnd_208594] using wordTrace_append hprefix tailTrace_208594
  have hstable : (prefixWord ++ tailWord_208594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208594).length < 2 ^ (prefixWord ++ tailWord_208594).sum := by decide
  have hdescent : baseEnd_208594 < baseStart_208594 := by decide
  rcases family_descends (prefixWord ++ tailWord_208594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208636 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_208636 : Nat := 118140960795 + 208636 * 2 ^ 59
def prefixEnd_208636 : Nat := 4983230072969 + 3 ^ 40 * 208636 * 2
def baseEnd_208636 : Nat := 47613577702911530840225

theorem tailTrace_208636 : CollatzResearch.WordTrace tailWord_208636 prefixEnd_208636 47613577702911530840225 := by
  unfold tailWord_208636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804790036077439518542881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5073053381436586024723841 3804790036077439518542881)
  ·
    refine ⟨2853592527058079638907161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3804790036077439518542881 2853592527058079638907161)
    ·
      refine ⟨2140194395293559729180371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2853592527058079638907161 2140194395293559729180371)
      ·
        refine ⟨3210291592940339593770557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140194395293559729180371 3210291592940339593770557)
        ·
          refine ⟨1203859347352627347663959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3210291592940339593770557 1203859347352627347663959)
          ·
            refine ⟨1805789021028941021495939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203859347352627347663959 1805789021028941021495939)
            ·
              refine ⟨2708683531543411532243909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805789021028941021495939 2708683531543411532243909)
              ·
                refine ⟨507878162164389662295733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2708683531543411532243909 507878162164389662295733)
                ·
                  refine ⟨47613577702911530840225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 507878162164389662295733 47613577702911530840225)
                  ·
                    rfl

theorem cell21_208636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_208636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208636 prefixEnd_208636 := by exact prefixLift 208636
  have htrace : WordTrace (prefixWord ++ tailWord_208636) baseStart_208636 baseEnd_208636 := by
    simpa [prefixWord, tailWord_208636, baseEnd_208636] using wordTrace_append hprefix tailTrace_208636
  have hstable : (prefixWord ++ tailWord_208636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208636).length < 2 ^ (prefixWord ++ tailWord_208636).sum := by decide
  have hdescent : baseEnd_208636 < baseStart_208636 := by decide
  rcases family_descends (prefixWord ++ tailWord_208636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208684 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_208684 : Nat := 118140960795 + 208684 * 2 ^ 59
def prefixEnd_208684 : Nat := 4983230072969 + 3 ^ 40 * 208684 * 2
def baseEnd_208684 : Nat := 47624531956874114040127

theorem tailTrace_208684 : CollatzResearch.WordTrace tailWord_208684 prefixEnd_208684 47624531956874114040127 := by
  unfold tailWord_208684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805665387990491617416553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5074220517320655489888737 3805665387990491617416553)
  ·
    refine ⟨2854249040992868713062415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3805665387990491617416553 2854249040992868713062415)
    ·
      refine ⟨4281373561489303069593623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854249040992868713062415 4281373561489303069593623)
      ·
        refine ⟨6422060342233954604390435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281373561489303069593623 6422060342233954604390435)
        ·
          refine ⟨9633090513350931906585653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422060342233954604390435 9633090513350931906585653)
          ·
            refine ⟨903102235626649866242405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9633090513350931906585653 903102235626649866242405)
            ·
              refine ⟨169331669179996849920451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 903102235626649866242405 169331669179996849920451)
              ·
                refine ⟨253997503769995274880677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169331669179996849920451 253997503769995274880677)
                ·
                  refine ⟨47624531956874114040127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253997503769995274880677 47624531956874114040127)
                  ·
                    rfl

theorem cell21_208684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_208684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208684 prefixEnd_208684 := by exact prefixLift 208684
  have htrace : WordTrace (prefixWord ++ tailWord_208684) baseStart_208684 baseEnd_208684 := by
    simpa [prefixWord, tailWord_208684, baseEnd_208684] using wordTrace_append hprefix tailTrace_208684
  have hstable : (prefixWord ++ tailWord_208684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208684).length < 2 ^ (prefixWord ++ tailWord_208684).sum := by decide
  have hdescent : baseEnd_208684 < baseStart_208684 := by decide
  rcases family_descends (prefixWord ++ tailWord_208684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208729 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 3]
def baseStart_208729 : Nat := 118140960795 + 208729 * 2 ^ 59
def prefixEnd_208729 : Nat := 4983230072969 + 3 ^ 40 * 208729 * 2
def baseEnd_208729 : Nat := 47634801569964035790035

theorem tailTrace_208729 : CollatzResearch.WordTrace tailWord_208729 prefixEnd_208729 47634801569964035790035 := by
  unfold tailWord_208729
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612972060817955920221241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075314707211970613480827 7612972060817955920221241)
  ·
    refine ⟨5709729045613466940165931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7612972060817955920221241 5709729045613466940165931)
    ·
      refine ⟨8564593568420200410248897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709729045613466940165931 8564593568420200410248897)
      ·
        refine ⟨6423445176315150307686673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8564593568420200410248897 6423445176315150307686673)
        ·
          refine ⟨4817583882236362730765005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6423445176315150307686673 4817583882236362730765005)
          ·
            refine ⟨1806593955838636024036877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4817583882236362730765005 1806593955838636024036877)
            ·
              refine ⟨677472733439488509013829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1806593955838636024036877 677472733439488509013829)
              ·
                refine ⟨127026137519904095440093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 677472733439488509013829 127026137519904095440093)
                ·
                  refine ⟨47634801569964035790035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127026137519904095440093 47634801569964035790035)
                  ·
                    rfl

theorem cell21_208729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_208729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208729 prefixEnd_208729 := by exact prefixLift 208729
  have htrace : WordTrace (prefixWord ++ tailWord_208729) baseStart_208729 baseEnd_208729 := by
    simpa [prefixWord, tailWord_208729, baseEnd_208729] using wordTrace_append hprefix tailTrace_208729
  have hstable : (prefixWord ++ tailWord_208729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208729).length < 2 ^ (prefixWord ++ tailWord_208729).sum := by decide
  have hdescent : baseEnd_208729 < baseStart_208729 := by decide
  rcases family_descends (prefixWord ++ tailWord_208729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208732 : List Nat := [2, 2, 4, 2, 3, 1, 1, 6]
def baseStart_208732 : Nat := 118140960795 + 208732 * 2 ^ 59
def prefixEnd_208732 : Nat := 4983230072969 + 3 ^ 40 * 208732 * 2
def baseEnd_208732 : Nat := 15878495403612232413343

theorem tailTrace_208732 : CollatzResearch.WordTrace tailWord_208732 prefixEnd_208732 15878495403612232413343 := by
  unfold tailWord_208732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806540739903543716290225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5075387653204724955053633 3806540739903543716290225)
  ·
    refine ⟨2854905554927657787217669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3806540739903543716290225 2854905554927657787217669)
    ·
      refine ⟨535294791548935835103313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2854905554927657787217669 535294791548935835103313)
      ·
        refine ⟨401471093661701876327485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535294791548935835103313 401471093661701876327485)
        ·
          refine ⟨150551660123138203622807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401471093661701876327485 150551660123138203622807)
          ·
            refine ⟨225827490184707305434211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150551660123138203622807 225827490184707305434211)
            ·
              refine ⟨338741235277060958151317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225827490184707305434211 338741235277060958151317)
              ·
                refine ⟨15878495403612232413343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 338741235277060958151317 15878495403612232413343)
                ·
                  rfl

theorem cell21_208732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_208732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208732 prefixEnd_208732 := by exact prefixLift 208732
  have htrace : WordTrace (prefixWord ++ tailWord_208732) baseStart_208732 baseEnd_208732 := by
    simpa [prefixWord, tailWord_208732, baseEnd_208732] using wordTrace_append hprefix tailTrace_208732
  have hstable : (prefixWord ++ tailWord_208732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208732).length < 2 ^ (prefixWord ++ tailWord_208732).sum := by decide
  have hdescent : baseEnd_208732 < baseStart_208732 := by decide
  rcases family_descends (prefixWord ++ tailWord_208732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208743 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_208743 : Nat := 118140960795 + 208743 * 2 ^ 59
def prefixEnd_208743 : Nat := 4983230072969 + 3 ^ 40 * 208743 * 2
def baseEnd_208743 : Nat := 47637996560703122556673

theorem tailTrace_208743 : CollatzResearch.WordTrace tailWord_208743 prefixEnd_208743 47637996560703122556673 := by
  unfold tailWord_208743
  simp only [CollatzResearch.WordTrace]
  refine ⟨7613482682767236311230883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075655121844824207487255 7613482682767236311230883)
  ·
    refine ⟨11420224024150854466846325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7613482682767236311230883 11420224024150854466846325)
    ·
      refine ⟨1070646002264142606266843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11420224024150854466846325 1070646002264142606266843)
      ·
        refine ⟨1605969003396213909400265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070646002264142606266843 1605969003396213909400265)
        ·
          refine ⟨1204476752547160432050199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605969003396213909400265 1204476752547160432050199)
          ·
            refine ⟨1806715128820740648075299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204476752547160432050199 1806715128820740648075299)
            ·
              refine ⟨2710072693231110972112949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806715128820740648075299 2710072693231110972112949)
              ·
                refine ⟨254069314990416653635589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2710072693231110972112949 254069314990416653635589)
                ·
                  refine ⟨47637996560703122556673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254069314990416653635589 47637996560703122556673)
                  ·
                    rfl

theorem cell21_208743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_208743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208743 prefixEnd_208743 := by exact prefixLift 208743
  have htrace : WordTrace (prefixWord ++ tailWord_208743) baseStart_208743 baseEnd_208743 := by
    simpa [prefixWord, tailWord_208743, baseEnd_208743] using wordTrace_append hprefix tailTrace_208743
  have hstable : (prefixWord ++ tailWord_208743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208743).length < 2 ^ (prefixWord ++ tailWord_208743).sum := by decide
  have hdescent : baseEnd_208743 < baseStart_208743 := by decide
  rcases family_descends (prefixWord ++ tailWord_208743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208746 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_208746 : Nat := 118140960795 + 208746 * 2 ^ 59
def prefixEnd_208746 : Nat := 4983230072969 + 3 ^ 40 * 208746 * 2
def baseEnd_208746 : Nat := 47638681201575784006667

theorem tailTrace_208746 : CollatzResearch.WordTrace tailWord_208746 prefixEnd_208746 47638681201575784006667 := by
  unfold tailWord_208746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903398025439091955897523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5075728067837578549060061 1903398025439091955897523)
  ·
    refine ⟨2855097038158637933846285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903398025439091955897523 2855097038158637933846285)
    ·
      refine ⟨1070661389309489225192357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2855097038158637933846285 1070661389309489225192357)
      ·
        refine ⟨200749010495529229723567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1070661389309489225192357 200749010495529229723567)
        ·
          refine ⟨301123515743293844585351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200749010495529229723567 301123515743293844585351)
          ·
            refine ⟨451685273614940766878027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301123515743293844585351 451685273614940766878027)
            ·
              refine ⟨677527910422411150317041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451685273614940766878027 677527910422411150317041)
              ·
                refine ⟨508145932816808362737781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677527910422411150317041 508145932816808362737781)
                ·
                  refine ⟨47638681201575784006667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508145932816808362737781 47638681201575784006667)
                  ·
                    rfl

theorem cell21_208746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_208746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208746 prefixEnd_208746 := by exact prefixLift 208746
  have htrace : WordTrace (prefixWord ++ tailWord_208746) baseStart_208746 baseEnd_208746 := by
    simpa [prefixWord, tailWord_208746, baseEnd_208746] using wordTrace_append hprefix tailTrace_208746
  have hstable : (prefixWord ++ tailWord_208746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208746).length < 2 ^ (prefixWord ++ tailWord_208746).sum := by decide
  have hdescent : baseEnd_208746 < baseStart_208746 := by decide
  rcases family_descends (prefixWord ++ tailWord_208746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208814 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_208814 : Nat := 118140960795 + 208814 * 2 ^ 59
def prefixEnd_208814 : Nat := 4983230072969 + 3 ^ 40 * 208814 * 2
def baseEnd_208814 : Nat := 47654199728022776873195

theorem tailTrace_208814 : CollatzResearch.WordTrace tailWord_208814 prefixEnd_208814 47654199728022776873195 := by
  unfold tailWord_208814
  simp only [CollatzResearch.WordTrace]
  refine ⟨952009033188751929633187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5077381510340010291376997 952009033188751929633187)
  ·
    refine ⟨1428013549783127894449781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 952009033188751929633187 1428013549783127894449781)
    ·
      refine ⟨133876270292168240104667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1428013549783127894449781 133876270292168240104667)
      ·
        refine ⟨200814405438252360157001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133876270292168240104667 200814405438252360157001)
        ·
          refine ⟨150610804078689270117751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200814405438252360157001 150610804078689270117751)
          ·
            refine ⟨225916206118033905176627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150610804078689270117751 225916206118033905176627)
            ·
              refine ⟨338874309177050857764941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225916206118033905176627 338874309177050857764941)
              ·
                refine ⟨127077865941394071661853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338874309177050857764941 127077865941394071661853)
                ·
                  refine ⟨47654199728022776873195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127077865941394071661853 47654199728022776873195)
                  ·
                    rfl

theorem cell21_208814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_208814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208814 prefixEnd_208814 := by exact prefixLift 208814
  have htrace : WordTrace (prefixWord ++ tailWord_208814) baseStart_208814 baseEnd_208814 := by
    simpa [prefixWord, tailWord_208814, baseEnd_208814] using wordTrace_append hprefix tailTrace_208814
  have hstable : (prefixWord ++ tailWord_208814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208814).length < 2 ^ (prefixWord ++ tailWord_208814).sum := by decide
  have hdescent : baseEnd_208814 < baseStart_208814 := by decide
  rcases family_descends (prefixWord ++ tailWord_208814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208853 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 4]
def baseStart_208853 : Nat := 118140960795 + 208853 * 2 ^ 59
def prefixEnd_208853 : Nat := 4983230072969 + 3 ^ 40 * 208853 * 2
def baseEnd_208853 : Nat := 47663100059367375723115

theorem tailTrace_208853 : CollatzResearch.WordTrace tailWord_208853 prefixEnd_208853 47663100059367375723115 := by
  unfold tailWord_208853
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617494712368725097735213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5078329808245816731823475 7617494712368725097735213)
  ·
    refine ⟨2856560517138271911650705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7617494712368725097735213 2856560517138271911650705)
    ·
      refine ⟨2142420387853703933738029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2856560517138271911650705 2142420387853703933738029)
      ·
        refine ⟨803407645445138975151761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2142420387853703933738029 803407645445138975151761)
        ·
          refine ⟨602555734083854231363821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803407645445138975151761 602555734083854231363821)
          ·
            refine ⟨225958400281445336761433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602555734083854231363821 225958400281445336761433)
            ·
              refine ⟨169468800211084002571075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225958400281445336761433 169468800211084002571075)
              ·
                refine ⟨254203200316626003856613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169468800211084002571075 254203200316626003856613)
                ·
                  refine ⟨47663100059367375723115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254203200316626003856613 47663100059367375723115)
                  ·
                    rfl

theorem cell21_208853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_208853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208853 prefixEnd_208853 := by exact prefixLift 208853
  have htrace : WordTrace (prefixWord ++ tailWord_208853) baseStart_208853 baseEnd_208853 := by
    simpa [prefixWord, tailWord_208853, baseEnd_208853] using wordTrace_append hprefix tailTrace_208853
  have hstable : (prefixWord ++ tailWord_208853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208853).length < 2 ^ (prefixWord ++ tailWord_208853).sum := by decide
  have hdescent : baseEnd_208853 < baseStart_208853 := by decide
  rcases family_descends (prefixWord ++ tailWord_208853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208957 : List Nat := [1, 4, 1, 3, 1, 1, 1, 6, 3]
def baseStart_208957 : Nat := 118140960795 + 208957 * 2 ^ 59
def prefixEnd_208957 : Nat := 4983230072969 + 3 ^ 40 * 208957 * 2
def baseEnd_208957 : Nat := 47686834276286305989569

theorem tailTrace_208957 : CollatzResearch.WordTrace tailWord_208957 prefixEnd_208957 47686834276286305989569 := by
  unfold tailWord_208957
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621287903991950859521125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5080858602661300573014083 7621287903991950859521125)
  ·
    refine ⟨1428991481998490786160211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7621287903991950859521125 1428991481998490786160211)
    ·
      refine ⟨2143487222997736179240317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428991481998490786160211 2143487222997736179240317)
      ·
        refine ⟨803807708624151067215119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2143487222997736179240317 803807708624151067215119)
        ·
          refine ⟨1205711562936226600822679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803807708624151067215119 1205711562936226600822679)
          ·
            refine ⟨1808567344404339901234019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205711562936226600822679 1808567344404339901234019)
            ·
              refine ⟨2712851016606509851851029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808567344404339901234019 2712851016606509851851029)
              ·
                refine ⟨127164891403430149305517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2712851016606509851851029 127164891403430149305517)
                ·
                  refine ⟨47686834276286305989569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127164891403430149305517 47686834276286305989569)
                  ·
                    rfl

theorem cell21_208957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_208957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_208957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_208957 prefixEnd_208957 := by exact prefixLift 208957
  have htrace : WordTrace (prefixWord ++ tailWord_208957) baseStart_208957 baseEnd_208957 := by
    simpa [prefixWord, tailWord_208957, baseEnd_208957] using wordTrace_append hprefix tailTrace_208957
  have hstable : (prefixWord ++ tailWord_208957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208957).length < 2 ^ (prefixWord ++ tailWord_208957).sum := by decide
  have hdescent : baseEnd_208957 < baseStart_208957 := by decide
  rcases family_descends (prefixWord ++ tailWord_208957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209002 : List Nat := [3, 1, 3, 2, 3, 2, 7]
def baseStart_209002 : Nat := 118140960795 + 209002 * 2 ^ 59
def prefixEnd_209002 : Nat := 4983230072969 + 3 ^ 40 * 209002 * 2
def baseEnd_209002 : Nat := 5299678209930691971053

theorem tailTrace_209002 : CollatzResearch.WordTrace tailWord_209002 prefixEnd_209002 5299678209930691971053 := by
  unfold tailWord_209002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905732297207230886227315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5081952792552615696606173 1905732297207230886227315)
  ·
    refine ⟨2858598445810846329340973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905732297207230886227315 2858598445810846329340973)
    ·
      refine ⟨1071974417179067373502865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2858598445810846329340973 1071974417179067373502865)
      ·
        refine ⟨803980812884300530127149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071974417179067373502865 803980812884300530127149)
        ·
          refine ⟨301492804831612698797681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803980812884300530127149 301492804831612698797681)
          ·
            refine ⟨226119603623709524098261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301492804831612698797681 226119603623709524098261)
            ·
              refine ⟨5299678209930691971053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 226119603623709524098261 5299678209930691971053)
              ·
                rfl

theorem cell21_209002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 7].length) (baseStart_209002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209002 prefixEnd_209002 := by exact prefixLift 209002
  have htrace : WordTrace (prefixWord ++ tailWord_209002) baseStart_209002 baseEnd_209002 := by
    simpa [prefixWord, tailWord_209002, baseEnd_209002] using wordTrace_append hprefix tailTrace_209002
  have hstable : (prefixWord ++ tailWord_209002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209002).length < 2 ^ (prefixWord ++ tailWord_209002).sum := by decide
  have hdescent : baseEnd_209002 < baseStart_209002 := by decide
  rcases family_descends (prefixWord ++ tailWord_209002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209075 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_209075 : Nat := 118140960795 + 209075 * 2 ^ 59
def prefixEnd_209075 : Nat := 4983230072969 + 3 ^ 40 * 209075 * 2
def baseEnd_209075 : Nat := 47713763483944323022661

theorem tailTrace_209075 : CollatzResearch.WordTrace tailWord_209075 prefixEnd_209075 47713763483944323022661 := by
  unfold tailWord_209075
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625591717564457012316679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5083727811709638008211119 7625591717564457012316679)
  ·
    refine ⟨11438387576346685518475019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7625591717564457012316679 11438387576346685518475019)
    ·
      refine ⟨17157581364520028277712529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438387576346685518475019 17157581364520028277712529)
      ·
        refine ⟨12868186023390021208284397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17157581364520028277712529 12868186023390021208284397)
        ·
          refine ⟨4825569758771257953106649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12868186023390021208284397 4825569758771257953106649)
          ·
            refine ⟨3619177319078443464829987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4825569758771257953106649 3619177319078443464829987)
            ·
              refine ⟨5428765978617665197244981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619177319078443464829987 5428765978617665197244981)
              ·
                refine ⟨508946810495406112241717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5428765978617665197244981 508946810495406112241717)
                ·
                  refine ⟨47713763483944323022661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508946810495406112241717 47713763483944323022661)
                  ·
                    rfl

theorem cell21_209075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_209075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209075 prefixEnd_209075 := by exact prefixLift 209075
  have htrace : WordTrace (prefixWord ++ tailWord_209075) baseStart_209075 baseEnd_209075 := by
    simpa [prefixWord, tailWord_209075, baseEnd_209075] using wordTrace_append hprefix tailTrace_209075
  have hstable : (prefixWord ++ tailWord_209075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209075).length < 2 ^ (prefixWord ++ tailWord_209075).sum := by decide
  have hdescent : baseEnd_209075 < baseStart_209075 := by decide
  rcases family_descends (prefixWord ++ tailWord_209075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209092 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_209092 : Nat := 118140960795 + 209092 * 2 ^ 59
def prefixEnd_209092 : Nat := 4983230072969 + 3 ^ 40 * 209092 * 2
def baseEnd_209092 : Nat := 47717643115556071239293

theorem tailTrace_209092 : CollatzResearch.WordTrace tailWord_209092 prefixEnd_209092 47717643115556071239293 := by
  unfold tailWord_209092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813105879251434457842765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5084141172335245943790353 3813105879251434457842765)
  ·
    refine ⟨1429914704719287921691037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3813105879251434457842765 1429914704719287921691037)
    ·
      refine ⟨536218014269732970634139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1429914704719287921691037 536218014269732970634139)
      ·
        refine ⟨804327021404599455951209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536218014269732970634139 804327021404599455951209)
        ·
          refine ⟨603245266053449591963407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804327021404599455951209 603245266053449591963407)
          ·
            refine ⟨904867899080174387945111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603245266053449591963407 904867899080174387945111)
            ·
              refine ⟨1357301848620261581917667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904867899080174387945111 1357301848620261581917667)
              ·
                refine ⟨2035952772930392372876501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357301848620261581917667 2035952772930392372876501)
                ·
                  refine ⟨47717643115556071239293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2035952772930392372876501 47717643115556071239293)
                  ·
                    rfl

theorem cell21_209092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_209092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209092 prefixEnd_209092 := by exact prefixLift 209092
  have htrace : WordTrace (prefixWord ++ tailWord_209092) baseStart_209092 baseEnd_209092 := by
    simpa [prefixWord, tailWord_209092, baseEnd_209092] using wordTrace_append hprefix tailTrace_209092
  have hstable : (prefixWord ++ tailWord_209092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209092).length < 2 ^ (prefixWord ++ tailWord_209092).sum := by decide
  have hdescent : baseEnd_209092 < baseStart_209092 := by decide
  rcases family_descends (prefixWord ++ tailWord_209092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209120 : List Nat := [2, 1, 1, 3, 1, 3, 10]
def baseStart_209120 : Nat := 118140960795 + 209120 * 2 ^ 59
def prefixEnd_209120 : Nat := 4983230072969 + 3 ^ 40 * 209120 * 2
def baseEnd_209120 : Nat := 5302670344114916085841

theorem tailTrace_209120 : CollatzResearch.WordTrace tailWord_209120 prefixEnd_209120 5302670344114916085841 := by
  unfold tailWord_209120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813616501200714848852407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5084822001600953131803209 3813616501200714848852407)
  ·
    refine ⟨5720424751801072273278611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813616501200714848852407 5720424751801072273278611)
    ·
      refine ⟨8580637127701608409917917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720424751801072273278611 8580637127701608409917917)
      ·
        refine ⟨3217738922888103153719219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8580637127701608409917917 3217738922888103153719219)
        ·
          refine ⟨4826608384332154730578829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217738922888103153719219 4826608384332154730578829)
          ·
            refine ⟨1809978144124558023967061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4826608384332154730578829 1809978144124558023967061)
            ·
              refine ⟨5302670344114916085841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1809978144124558023967061 5302670344114916085841)
              ·
                rfl

theorem cell21_209120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 10].length) (baseStart_209120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209120 prefixEnd_209120 := by exact prefixLift 209120
  have htrace : WordTrace (prefixWord ++ tailWord_209120) baseStart_209120 baseEnd_209120 := by
    simpa [prefixWord, tailWord_209120, baseEnd_209120] using wordTrace_append hprefix tailTrace_209120
  have hstable : (prefixWord ++ tailWord_209120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209120).length < 2 ^ (prefixWord ++ tailWord_209120).sum := by decide
  have hdescent : baseEnd_209120 < baseStart_209120 := by decide
  rcases family_descends (prefixWord ++ tailWord_209120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209151 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_209151 : Nat := 118140960795 + 209151 * 2 ^ 59
def prefixEnd_209151 : Nat := 4983230072969 + 3 ^ 40 * 209151 * 2
def baseEnd_209151 : Nat := 47731107719385079755839

theorem tailTrace_209151 : CollatzResearch.WordTrace tailWord_209151 prefixEnd_209151 47731107719385079755839 := by
  unfold tailWord_209151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628363665289121992083307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5085575776859414661388871 7628363665289121992083307)
  ·
    refine ⟨11442545497933682988124961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628363665289121992083307 11442545497933682988124961)
    ·
      refine ⟨8581909123450262241093721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11442545497933682988124961 8581909123450262241093721)
      ·
        refine ⟨6436431842587696680820291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8581909123450262241093721 6436431842587696680820291)
        ·
          refine ⟨9654647763881545021230437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436431842587696680820291 9654647763881545021230437)
          ·
            refine ⟨1810246455727789691480707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9654647763881545021230437 1810246455727789691480707)
            ·
              refine ⟨2715369683591684537221061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810246455727789691480707 2715369683591684537221061)
              ·
                refine ⟨509131815673440850728949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2715369683591684537221061 509131815673440850728949)
                ·
                  refine ⟨47731107719385079755839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509131815673440850728949 47731107719385079755839)
                  ·
                    rfl

theorem cell21_209151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_209151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209151 prefixEnd_209151 := by exact prefixLift 209151
  have htrace : WordTrace (prefixWord ++ tailWord_209151) baseStart_209151 baseEnd_209151 := by
    simpa [prefixWord, tailWord_209151, baseEnd_209151] using wordTrace_append hprefix tailTrace_209151
  have hstable : (prefixWord ++ tailWord_209151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209151).length < 2 ^ (prefixWord ++ tailWord_209151).sum := by decide
  have hdescent : baseEnd_209151 < baseStart_209151 := by decide
  rcases family_descends (prefixWord ++ tailWord_209151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209154 : List Nat := [3, 4, 1, 1, 2, 2, 1, 7]
def baseStart_209154 : Nat := 118140960795 + 209154 * 2 ^ 59
def prefixEnd_209154 : Nat := 4983230072969 + 3 ^ 40 * 209154 * 2
def baseEnd_209154 : Nat := 15910597453419247068611

theorem tailTrace_209154 : CollatzResearch.WordTrace tailWord_209154 prefixEnd_209154 15910597453419247068611 := by
  unfold tailWord_209154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907118271069563376110629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5085648722852169002961677 1907118271069563376110629)
  ·
    refine ⟨357584675825543133020743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1907118271069563376110629 357584675825543133020743)
    ·
      refine ⟨536377013738314699531115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357584675825543133020743 536377013738314699531115)
      ·
        refine ⟨804565520607472049296673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536377013738314699531115 804565520607472049296673)
        ·
          refine ⟨603424140455604036972505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 804565520607472049296673 603424140455604036972505)
          ·
            refine ⟨452568105341703027729379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603424140455604036972505 452568105341703027729379)
            ·
              refine ⟨678852158012554541594069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452568105341703027729379 678852158012554541594069)
              ·
                refine ⟨15910597453419247068611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 678852158012554541594069 15910597453419247068611)
                ·
                  rfl

theorem cell21_209154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_209154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209154 prefixEnd_209154 := by exact prefixLift 209154
  have htrace : WordTrace (prefixWord ++ tailWord_209154) baseStart_209154 baseEnd_209154 := by
    simpa [prefixWord, tailWord_209154, baseEnd_209154] using wordTrace_append hprefix tailTrace_209154
  have hstable : (prefixWord ++ tailWord_209154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209154).length < 2 ^ (prefixWord ++ tailWord_209154).sum := by decide
  have hdescent : baseEnd_209154 < baseStart_209154 := by decide
  rcases family_descends (prefixWord ++ tailWord_209154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209191 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 4]
def baseStart_209191 : Nat := 118140960795 + 209191 * 2 ^ 59
def prefixEnd_209191 : Nat := 4983230072969 + 3 ^ 40 * 209191 * 2
def baseEnd_209191 : Nat := 47740236264353899089091

theorem tailTrace_209191 : CollatzResearch.WordTrace tailWord_209191 prefixEnd_209191 47740236264353899089091 := by
  unfold tailWord_209191
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629822585144208823539427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086548390096139215692951 7629822585144208823539427)
  ·
    refine ⟨11444733877716313235309141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629822585144208823539427 11444733877716313235309141)
    ·
      refine ⟨134117975129488045726279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 11444733877716313235309141 134117975129488045726279)
      ·
        refine ⟨201176962694232068589419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134117975129488045726279 201176962694232068589419)
        ·
          refine ⟨301765444041348102884129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201176962694232068589419 301765444041348102884129)
          ·
            refine ⟨226324083031011077163097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301765444041348102884129 226324083031011077163097)
            ·
              refine ⟨169743062273258307872323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226324083031011077163097 169743062273258307872323)
              ·
                refine ⟨254614593409887461808485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169743062273258307872323 254614593409887461808485)
                ·
                  refine ⟨47740236264353899089091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254614593409887461808485 47740236264353899089091)
                  ·
                    rfl

theorem cell21_209191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4].length) (baseStart_209191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209191 prefixEnd_209191 := by exact prefixLift 209191
  have htrace : WordTrace (prefixWord ++ tailWord_209191) baseStart_209191 baseEnd_209191 := by
    simpa [prefixWord, tailWord_209191, baseEnd_209191] using wordTrace_append hprefix tailTrace_209191
  have hstable : (prefixWord ++ tailWord_209191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209191).length < 2 ^ (prefixWord ++ tailWord_209191).sum := by decide
  have hdescent : baseEnd_209191 < baseStart_209191 := by decide
  rcases family_descends (prefixWord ++ tailWord_209191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209196 : List Nat := [2, 2, 1, 1, 1, 3, 3, 8]
def baseStart_209196 : Nat := 118140960795 + 209196 * 2 ^ 59
def prefixEnd_209196 : Nat := 4983230072969 + 3 ^ 40 * 209196 * 2
def baseEnd_209196 : Nat := 15913792444158333835249

theorem tailTrace_209196 : CollatzResearch.WordTrace tailWord_209196 prefixEnd_209196 15913792444158333835249 := by
  unfold tailWord_209196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815002475063047338735721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5086669966750729784980961 3815002475063047338735721)
  ·
    refine ⟨2861251856297285504051791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3815002475063047338735721 2861251856297285504051791)
    ·
      refine ⟨4291877784445928256077687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2861251856297285504051791 4291877784445928256077687)
      ·
        refine ⟨6437816676668892384116531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291877784445928256077687 6437816676668892384116531)
        ·
          refine ⟨9656725015003338576174797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6437816676668892384116531 9656725015003338576174797)
          ·
            refine ⟨3621271880626251966065549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9656725015003338576174797 3621271880626251966065549)
            ·
              refine ⟨1357976955234844487274581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3621271880626251966065549 1357976955234844487274581)
              ·
                refine ⟨15913792444158333835249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1357976955234844487274581 15913792444158333835249)
                ·
                  rfl

theorem cell21_209196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_209196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209196 prefixEnd_209196 := by exact prefixLift 209196
  have htrace : WordTrace (prefixWord ++ tailWord_209196) baseStart_209196 baseEnd_209196 := by
    simpa [prefixWord, tailWord_209196, baseEnd_209196] using wordTrace_append hprefix tailTrace_209196
  have hstable : (prefixWord ++ tailWord_209196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209196).length < 2 ^ (prefixWord ++ tailWord_209196).sum := by decide
  have hdescent : baseEnd_209196 < baseStart_209196 := by decide
  rcases family_descends (prefixWord ++ tailWord_209196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209199 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 4]
def baseStart_209199 : Nat := 118140960795 + 209199 * 2 ^ 59
def prefixEnd_209199 : Nat := 4983230072969 + 3 ^ 40 * 209199 * 2
def baseEnd_209199 : Nat := 47742061973347662955741

theorem tailTrace_209199 : CollatzResearch.WordTrace tailWord_209199 prefixEnd_209199 47742061973347662955741 := by
  unfold tailWord_209199
  simp only [CollatzResearch.WordTrace]
  refine ⟨7630114369115226189830651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086742912743484126553767 7630114369115226189830651)
  ·
    refine ⟨11445171553672839284745977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7630114369115226189830651 11445171553672839284745977)
    ·
      refine ⟨8583878665254629463559483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11445171553672839284745977 8583878665254629463559483)
      ·
        refine ⟨12875817997881944195339225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583878665254629463559483 12875817997881944195339225)
        ·
          refine ⟨9656863498411458146504419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12875817997881944195339225 9656863498411458146504419)
          ·
            refine ⟨14485295247617187219756629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9656863498411458146504419 14485295247617187219756629)
            ·
              refine ⟨169749553683013912731523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 14485295247617187219756629 169749553683013912731523)
              ·
                refine ⟨254624330524520869097285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169749553683013912731523 254624330524520869097285)
                ·
                  refine ⟨47742061973347662955741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254624330524520869097285 47742061973347662955741)
                  ·
                    rfl

theorem cell21_209199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4].length) (baseStart_209199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209199 prefixEnd_209199 := by exact prefixLift 209199
  have htrace : WordTrace (prefixWord ++ tailWord_209199) baseStart_209199 baseEnd_209199 := by
    simpa [prefixWord, tailWord_209199, baseEnd_209199] using wordTrace_append hprefix tailTrace_209199
  have hstable : (prefixWord ++ tailWord_209199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209199).length < 2 ^ (prefixWord ++ tailWord_209199).sum := by decide
  have hdescent : baseEnd_209199 < baseStart_209199 := by decide
  rcases family_descends (prefixWord ++ tailWord_209199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209303 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_209303 : Nat := 118140960795 + 209303 * 2 ^ 59
def prefixEnd_209303 : Nat := 4983230072969 + 3 ^ 40 * 209303 * 2
def baseEnd_209303 : Nat := 47765796190266593222195

theorem tailTrace_209303 : CollatzResearch.WordTrace tailWord_209303 prefixEnd_209303 47765796190266593222195 := by
  unfold tailWord_209303
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633907560738451951616563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5089271707158967967744375 7633907560738451951616563)
  ·
    refine ⟨11450861341107677927424845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633907560738451951616563 11450861341107677927424845)
    ·
      refine ⟨4294073002915379222784317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11450861341107677927424845 4294073002915379222784317)
      ·
        refine ⟨1610277376093267208544119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4294073002915379222784317 1610277376093267208544119)
        ·
          refine ⟨2415416064139900812816179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610277376093267208544119 2415416064139900812816179)
          ·
            refine ⟨3623124096209851219224269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415416064139900812816179 3623124096209851219224269)
            ·
              refine ⟨1358671536078694207209101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3623124096209851219224269 1358671536078694207209101)
              ·
                refine ⟨509501826029510327703413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358671536078694207209101 509501826029510327703413)
                ·
                  refine ⟨47765796190266593222195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509501826029510327703413 47765796190266593222195)
                  ·
                    rfl

theorem cell21_209303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_209303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209303 prefixEnd_209303 := by exact prefixLift 209303
  have htrace : WordTrace (prefixWord ++ tailWord_209303) baseStart_209303 baseEnd_209303 := by
    simpa [prefixWord, tailWord_209303, baseEnd_209303] using wordTrace_append hprefix tailTrace_209303
  have hstable : (prefixWord ++ tailWord_209303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209303).length < 2 ^ (prefixWord ++ tailWord_209303).sum := by decide
  have hdescent : baseEnd_209303 < baseStart_209303 := by decide
  rcases family_descends (prefixWord ++ tailWord_209303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209337 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 3]
def baseStart_209337 : Nat := 118140960795 + 209337 * 2 ^ 59
def prefixEnd_209337 : Nat := 4983230072969 + 3 ^ 40 * 209337 * 2
def baseEnd_209337 : Nat := 47773555453490089655459

theorem tailTrace_209337 : CollatzResearch.WordTrace tailWord_209337 prefixEnd_209337 47773555453490089655459 := by
  unfold tailWord_209337
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635147642615275758354265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5090098428410183838902843 7635147642615275758354265)
  ·
    refine ⟨5726360731961456818765699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7635147642615275758354265 5726360731961456818765699)
    ·
      refine ⟨8589541097942185228148549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726360731961456818765699 8589541097942185228148549)
      ·
        refine ⟨1610538955864159730277853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8589541097942185228148549 1610538955864159730277853)
        ·
          refine ⟨603952108449059898854195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1610538955864159730277853 603952108449059898854195)
          ·
            refine ⟨905928162673589848281293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603952108449059898854195 905928162673589848281293)
            ·
              refine ⟨339723061002596193105485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905928162673589848281293 339723061002596193105485)
              ·
                refine ⟨127396147875973572414557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339723061002596193105485 127396147875973572414557)
                ·
                  refine ⟨47773555453490089655459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127396147875973572414557 47773555453490089655459)
                  ·
                    rfl

theorem cell21_209337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_209337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209337 prefixEnd_209337 := by exact prefixLift 209337
  have htrace : WordTrace (prefixWord ++ tailWord_209337) baseStart_209337 baseEnd_209337 := by
    simpa [prefixWord, tailWord_209337, baseEnd_209337] using wordTrace_append hprefix tailTrace_209337
  have hstable : (prefixWord ++ tailWord_209337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209337).length < 2 ^ (prefixWord ++ tailWord_209337).sum := by decide
  have hdescent : baseEnd_209337 < baseStart_209337 := by decide
  rcases family_descends (prefixWord ++ tailWord_209337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209365 : List Nat := [1, 3, 2, 3, 1, 3, 2, 6]
def baseStart_209365 : Nat := 118140960795 + 209365 * 2 ^ 59
def prefixEnd_209365 : Nat := 4983230072969 + 3 ^ 40 * 209365 * 2
def baseEnd_209365 : Nat := 15926648478322754396245

theorem tailTrace_209365 : CollatzResearch.WordTrace tailWord_209365 prefixEnd_209365 15926648478322754396245 := by
  unfold tailWord_209365
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636168886513836540373549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5090779257675891026915699 7636168886513836540373549)
  ·
    refine ⟨2863563332442688702640081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7636168886513836540373549 2863563332442688702640081)
    ·
      refine ⟨2147672499332016526980061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2863563332442688702640081 2147672499332016526980061)
      ·
        refine ⟨805377187249506197617523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2147672499332016526980061 805377187249506197617523)
        ·
          refine ⟨1208065780874259296426285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805377187249506197617523 1208065780874259296426285)
          ·
            refine ⟨453024667827847236159857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1208065780874259296426285 453024667827847236159857)
            ·
              refine ⟨339768500870885427119893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453024667827847236159857 339768500870885427119893)
              ·
                refine ⟨15926648478322754396245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 339768500870885427119893 15926648478322754396245)
                ·
                  rfl

theorem cell21_209365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_209365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209365 prefixEnd_209365 := by exact prefixLift 209365
  have htrace : WordTrace (prefixWord ++ tailWord_209365) baseStart_209365 baseEnd_209365 := by
    simpa [prefixWord, tailWord_209365, baseEnd_209365] using wordTrace_append hprefix tailTrace_209365
  have hstable : (prefixWord ++ tailWord_209365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209365).length < 2 ^ (prefixWord ++ tailWord_209365).sum := by decide
  have hdescent : baseEnd_209365 < baseStart_209365 := by decide
  rcases family_descends (prefixWord ++ tailWord_209365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209413 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 3]
def baseStart_209413 : Nat := 118140960795 + 209413 * 2 ^ 59
def prefixEnd_209413 : Nat := 4983230072969 + 3 ^ 40 * 209413 * 2
def baseEnd_209413 : Nat := 47790899688930846388637

theorem tailTrace_209413 : CollatzResearch.WordTrace tailWord_209413 prefixEnd_209413 47790899688930846388637 := by
  unfold tailWord_209413
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637919590339940738120893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5091946393559960492080595 7637919590339940738120893)
  ·
    refine ⟨2864219846377477776795335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7637919590339940738120893 2864219846377477776795335)
    ·
      refine ⟨4296329769566216665193003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2864219846377477776795335 4296329769566216665193003)
      ·
        refine ⟨6444494654349324997789505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296329769566216665193003 6444494654349324997789505)
        ·
          refine ⟨4833370990761993748342129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6444494654349324997789505 4833370990761993748342129)
          ·
            refine ⟨3625028243071495311256597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833370990761993748342129 3625028243071495311256597)
            ·
              refine ⟨169923198893976342715153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3625028243071495311256597 169923198893976342715153)
              ·
                refine ⟨127442399170482257036365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169923198893976342715153 127442399170482257036365)
                ·
                  refine ⟨47790899688930846388637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127442399170482257036365 47790899688930846388637)
                  ·
                    rfl

theorem cell21_209413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_209413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209413 prefixEnd_209413 := by exact prefixLift 209413
  have htrace : WordTrace (prefixWord ++ tailWord_209413) baseStart_209413 baseEnd_209413 := by
    simpa [prefixWord, tailWord_209413, baseEnd_209413] using wordTrace_append hprefix tailTrace_209413
  have hstable : (prefixWord ++ tailWord_209413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209413).length < 2 ^ (prefixWord ++ tailWord_209413).sum := by decide
  have hdescent : baseEnd_209413 < baseStart_209413 := by decide
  rcases family_descends (prefixWord ++ tailWord_209413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209441 : List Nat := [1, 2, 3, 2, 2, 1, 5, 5]
def baseStart_209441 : Nat := 118140960795 + 209441 * 2 ^ 59
def prefixEnd_209441 : Nat := 4983230072969 + 3 ^ 40 * 209441 * 2
def baseEnd_209441 : Nat := 15932429890136339973971

theorem tailTrace_209441 : CollatzResearch.WordTrace tailWord_209441 prefixEnd_209441 15932429890136339973971 := by
  unfold tailWord_209441
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638940834238501520140177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5092627222825667680093451 7638940834238501520140177)
  ·
    refine ⟨5729205625678876140105133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638940834238501520140177 5729205625678876140105133)
    ·
      refine ⟨2148452109629578552539425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5729205625678876140105133 2148452109629578552539425)
      ·
        refine ⟨1611339082222183914404569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148452109629578552539425 1611339082222183914404569)
        ·
          refine ⟨1208504311666637935803427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1611339082222183914404569 1208504311666637935803427)
          ·
            refine ⟨1812756467499956903705141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208504311666637935803427 1812756467499956903705141)
            ·
              refine ⟨169945918828120959722357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1812756467499956903705141 169945918828120959722357)
              ·
                refine ⟨15932429890136339973971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169945918828120959722357 15932429890136339973971)
                ·
                  rfl

theorem cell21_209441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 5].length) (baseStart_209441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209441 prefixEnd_209441 := by exact prefixLift 209441
  have htrace : WordTrace (prefixWord ++ tailWord_209441) baseStart_209441 baseEnd_209441 := by
    simpa [prefixWord, tailWord_209441, baseEnd_209441] using wordTrace_append hprefix tailTrace_209441
  have hstable : (prefixWord ++ tailWord_209441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209441).length < 2 ^ (prefixWord ++ tailWord_209441).sum := by decide
  have hdescent : baseEnd_209441 < baseStart_209441 := by decide
  rcases family_descends (prefixWord ++ tailWord_209441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209447 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 3]
def baseStart_209447 : Nat := 118140960795 + 209447 * 2 ^ 59
def prefixEnd_209447 : Nat := 4983230072969 + 3 ^ 40 * 209447 * 2
def baseEnd_209447 : Nat := 47798658952154342821901

theorem tailTrace_209447 : CollatzResearch.WordTrace tailWord_209447 prefixEnd_209447 47798658952154342821901 := by
  unfold tailWord_209447
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639159672216764544858595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5092773114811176363239063 7639159672216764544858595)
  ·
    refine ⟨11458739508325146817287893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7639159672216764544858595 11458739508325146817287893)
    ·
      refine ⟨268564207226370628530185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11458739508325146817287893 268564207226370628530185)
      ·
        refine ⟨201423155419777971397639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268564207226370628530185 201423155419777971397639)
        ·
          refine ⟨302134733129666957096459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201423155419777971397639 302134733129666957096459)
          ·
            refine ⟨453202099694500435644689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302134733129666957096459 453202099694500435644689)
            ·
              refine ⟨339901574770875326733517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453202099694500435644689 339901574770875326733517)
              ·
                refine ⟨127463090539078247525069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339901574770875326733517 127463090539078247525069)
                ·
                  refine ⟨47798658952154342821901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127463090539078247525069 47798658952154342821901)
                  ·
                    rfl

theorem cell21_209447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 3].length) (baseStart_209447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209447 prefixEnd_209447 := by exact prefixLift 209447
  have htrace : WordTrace (prefixWord ++ tailWord_209447) baseStart_209447 baseEnd_209447 := by
    simpa [prefixWord, tailWord_209447, baseEnd_209447] using wordTrace_append hprefix tailTrace_209447
  have hstable : (prefixWord ++ tailWord_209447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209447).length < 2 ^ (prefixWord ++ tailWord_209447).sum := by decide
  have hdescent : baseEnd_209447 < baseStart_209447 := by decide
  rcases family_descends (prefixWord ++ tailWord_209447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209472 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_209472 : Nat := 118140960795 + 209472 * 2 ^ 59
def prefixEnd_209472 : Nat := 4983230072969 + 3 ^ 40 * 209472 * 2
def baseEnd_209472 : Nat := 47804364292759854905183

theorem tailTrace_209472 : CollatzResearch.WordTrace tailWord_209472 prefixEnd_209472 47804364292759854905183 := by
  unfold tailWord_209472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820035748563096907259335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5093380998084129209679113 3820035748563096907259335)
  ·
    refine ⟨5730053622844645360889003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3820035748563096907259335 5730053622844645360889003)
    ·
      refine ⟨8595080434266968041333505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730053622844645360889003 8595080434266968041333505)
      ·
        refine ⟨6446310325700226031000129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8595080434266968041333505 6446310325700226031000129)
        ·
          refine ⟨4834732744275169523250097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446310325700226031000129 4834732744275169523250097)
          ·
            refine ⟨3626049558206377142437573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4834732744275169523250097 3626049558206377142437573)
            ·
              refine ⟨679884292163695714207045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3626049558206377142437573 679884292163695714207045)
              ·
                refine ⟨127478304780692946413821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679884292163695714207045 127478304780692946413821)
                ·
                  refine ⟨47804364292759854905183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127478304780692946413821 47804364292759854905183)
                  ·
                    rfl

theorem cell21_209472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_209472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209472 prefixEnd_209472 := by exact prefixLift 209472
  have htrace : WordTrace (prefixWord ++ tailWord_209472) baseStart_209472 baseEnd_209472 := by
    simpa [prefixWord, tailWord_209472, baseEnd_209472] using wordTrace_append hprefix tailTrace_209472
  have hstable : (prefixWord ++ tailWord_209472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209472).length < 2 ^ (prefixWord ++ tailWord_209472).sum := by decide
  have hdescent : baseEnd_209472 < baseStart_209472 := by decide
  rcases family_descends (prefixWord ++ tailWord_209472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209486 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_209486 : Nat := 118140960795 + 209486 * 2 ^ 59
def prefixEnd_209486 : Nat := 4983230072969 + 3 ^ 40 * 209486 * 2
def baseEnd_209486 : Nat := 47807559283498941671821

theorem tailTrace_209486 : CollatzResearch.WordTrace tailWord_209486 prefixEnd_209486 47807559283498941671821 := by
  unfold tailWord_209486
  simp only [CollatzResearch.WordTrace]
  refine ⟨955072764884434275691039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5093721412716982803685541 955072764884434275691039)
  ·
    refine ⟨1432609147326651413536559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955072764884434275691039 1432609147326651413536559)
    ·
      refine ⟨2148913720989977120304839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432609147326651413536559 2148913720989977120304839)
      ·
        refine ⟨3223370581484965680457259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148913720989977120304839 3223370581484965680457259)
        ·
          refine ⟨4835055872227448520685889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223370581484965680457259 4835055872227448520685889)
          ·
            refine ⟨3626291904170586390514417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835055872227448520685889 3626291904170586390514417)
            ·
              refine ⟨2719718928127939792885813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626291904170586390514417 2719718928127939792885813)
              ·
                refine ⟨254973649511994355583045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2719718928127939792885813 254973649511994355583045)
                ·
                  refine ⟨47807559283498941671821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254973649511994355583045 47807559283498941671821)
                  ·
                    rfl

theorem cell21_209486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_209486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209486 prefixEnd_209486 := by exact prefixLift 209486
  have htrace : WordTrace (prefixWord ++ tailWord_209486) baseStart_209486 baseEnd_209486 := by
    simpa [prefixWord, tailWord_209486, baseEnd_209486] using wordTrace_append hprefix tailTrace_209486
  have hstable : (prefixWord ++ tailWord_209486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209486).length < 2 ^ (prefixWord ++ tailWord_209486).sum := by decide
  have hdescent : baseEnd_209486 < baseStart_209486 := by decide
  rcases family_descends (prefixWord ++ tailWord_209486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209517 : List Nat := [1, 5, 1, 1, 3, 3, 7]
def baseStart_209517 : Nat := 118140960795 + 209517 * 2 ^ 59
def prefixEnd_209517 : Nat := 4983230072969 + 3 ^ 40 * 209517 * 2
def baseEnd_209517 : Nat := 5312737100649975183899

theorem tailTrace_209517 : CollatzResearch.WordTrace tailWord_209517 prefixEnd_209517 5312737100649975183899 := by
  unfold tailWord_209517
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641712781963166499906805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5094475187975444333271203 7641712781963166499906805)
  ·
    refine ⟨716410573309046859366263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7641712781963166499906805 716410573309046859366263)
    ·
      refine ⟨1074615859963570289049395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716410573309046859366263 1074615859963570289049395)
      ·
        refine ⟨1611923789945355433574093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074615859963570289049395 1611923789945355433574093)
        ·
          refine ⟨604471421229508287590285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1611923789945355433574093 604471421229508287590285)
          ·
            refine ⟨226676782961065607846357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604471421229508287590285 226676782961065607846357)
            ·
              refine ⟨5312737100649975183899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 226676782961065607846357 5312737100649975183899)
              ·
                rfl

theorem cell21_209517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 7].length) (baseStart_209517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209517 prefixEnd_209517 := by exact prefixLift 209517
  have htrace : WordTrace (prefixWord ++ tailWord_209517) baseStart_209517 baseEnd_209517 := by
    simpa [prefixWord, tailWord_209517, baseEnd_209517] using wordTrace_append hprefix tailTrace_209517
  have hstable : (prefixWord ++ tailWord_209517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209517).length < 2 ^ (prefixWord ++ tailWord_209517).sum := by decide
  have hdescent : baseEnd_209517 < baseStart_209517 := by decide
  rcases family_descends (prefixWord ++ tailWord_209517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209582 : List Nat := [4, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_209582 : Nat := 118140960795 + 209582 * 2 ^ 59
def prefixEnd_209582 : Nat := 4983230072969 + 3 ^ 40 * 209582 * 2
def baseEnd_209582 : Nat := 47829467791424108071625

theorem tailTrace_209582 : CollatzResearch.WordTrace tailWord_209582 prefixEnd_209582 47829467791424108071625 := by
  unfold tailWord_209582
  simp only [CollatzResearch.WordTrace]
  refine ⟨955510440840960325127875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5096055684485121734015333 955510440840960325127875)
  ·
    refine ⟨1433265661261440487691813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955510440840960325127875 1433265661261440487691813)
    ·
      refine ⟨268737311486520091442215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1433265661261440487691813 268737311486520091442215)
      ·
        refine ⟨403105967229780137163323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268737311486520091442215 403105967229780137163323)
        ·
          refine ⟨604658950844670205744985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403105967229780137163323 604658950844670205744985)
          ·
            refine ⟨453494213133502654308739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604658950844670205744985 453494213133502654308739)
            ·
              refine ⟨680241319700253981463109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453494213133502654308739 680241319700253981463109)
              ·
                refine ⟨127545247443797621524333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680241319700253981463109 127545247443797621524333)
                ·
                  refine ⟨47829467791424108071625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127545247443797621524333 47829467791424108071625)
                  ·
                    rfl

theorem cell21_209582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_209582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209582 prefixEnd_209582 := by exact prefixLift 209582
  have htrace : WordTrace (prefixWord ++ tailWord_209582) baseStart_209582 baseEnd_209582 := by
    simpa [prefixWord, tailWord_209582, baseEnd_209582] using wordTrace_append hprefix tailTrace_209582
  have hstable : (prefixWord ++ tailWord_209582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209582).length < 2 ^ (prefixWord ++ tailWord_209582).sum := by decide
  have hdescent : baseEnd_209582 < baseStart_209582 := by decide
  rcases family_descends (prefixWord ++ tailWord_209582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209624 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_209624 : Nat := 118140960795 + 209624 * 2 ^ 59
def prefixEnd_209624 : Nat := 4983230072969 + 3 ^ 40 * 209624 * 2
def baseEnd_209624 : Nat := 47839052763641368371539

theorem tailTrace_209624 : CollatzResearch.WordTrace tailWord_209624 prefixEnd_209624 47839052763641368371539 := by
  unfold tailWord_209624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822807696287761887025963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5097076928383682516034617 3822807696287761887025963)
  ·
    refine ⟨5734211544431642830538945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3822807696287761887025963 5734211544431642830538945)
    ·
      refine ⟨4300658658323732122904209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5734211544431642830538945 4300658658323732122904209)
      ·
        refine ⟨3225493993742799092178157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4300658658323732122904209 3225493993742799092178157)
        ·
          refine ⟨1209560247653549659566809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3225493993742799092178157 1209560247653549659566809)
          ·
            refine ⟨907170185740162244675107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209560247653549659566809 907170185740162244675107)
            ·
              refine ⟨1360755278610243367012661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907170185740162244675107 1360755278610243367012661)
              ·
                refine ⟨127570807369710315657437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360755278610243367012661 127570807369710315657437)
                ·
                  refine ⟨47839052763641368371539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127570807369710315657437 47839052763641368371539)
                  ·
                    rfl

theorem cell21_209624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_209624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209624 prefixEnd_209624 := by exact prefixLift 209624
  have htrace : WordTrace (prefixWord ++ tailWord_209624) baseStart_209624 baseEnd_209624 := by
    simpa [prefixWord, tailWord_209624, baseEnd_209624] using wordTrace_append hprefix tailTrace_209624
  have hstable : (prefixWord ++ tailWord_209624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209624).length < 2 ^ (prefixWord ++ tailWord_209624).sum := by decide
  have hdescent : baseEnd_209624 < baseStart_209624 := by decide
  rcases family_descends (prefixWord ++ tailWord_209624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209697 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_209697 : Nat := 118140960795 + 209697 * 2 ^ 59
def prefixEnd_209697 : Nat := 4983230072969 + 3 ^ 40 * 209697 * 2
def baseEnd_209697 : Nat := 47855712358209463654723

theorem tailTrace_209697 : CollatzResearch.WordTrace tailWord_209697 prefixEnd_209697 47855712358209463654723 := by
  unfold tailWord_209697
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648277921311057241459345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5098851947540704827639563 7648277921311057241459345)
  ·
    refine ⟨5736208440983292931094509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7648277921311057241459345 5736208440983292931094509)
    ·
      refine ⟨2151078165368734849160441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5736208440983292931094509 2151078165368734849160441)
      ·
        refine ⟨1613308624026551136870331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151078165368734849160441 1613308624026551136870331)
        ·
          refine ⟨2419962936039826705305497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613308624026551136870331 2419962936039826705305497)
          ·
            refine ⟨1814972202029870028979123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419962936039826705305497 1814972202029870028979123)
            ·
              refine ⟨2722458303044805043468685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814972202029870028979123 2722458303044805043468685)
              ·
                refine ⟨1020921863641801891300757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2722458303044805043468685 1020921863641801891300757)
                ·
                  refine ⟨47855712358209463654723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1020921863641801891300757 47855712358209463654723)
                  ·
                    rfl

theorem cell21_209697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_209697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209697 prefixEnd_209697 := by exact prefixLift 209697
  have htrace : WordTrace (prefixWord ++ tailWord_209697) baseStart_209697 baseEnd_209697 := by
    simpa [prefixWord, tailWord_209697, baseEnd_209697] using wordTrace_append hprefix tailTrace_209697
  have hstable : (prefixWord ++ tailWord_209697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209697).length < 2 ^ (prefixWord ++ tailWord_209697).sum := by decide
  have hdescent : baseEnd_209697 < baseStart_209697 := by decide
  rcases family_descends (prefixWord ++ tailWord_209697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209706 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_209706 : Nat := 118140960795 + 209706 * 2 ^ 59
def prefixEnd_209706 : Nat := 4983230072969 + 3 ^ 40 * 209706 * 2
def baseEnd_209706 : Nat := 47857766280827448004705

theorem tailTrace_209706 : CollatzResearch.WordTrace tailWord_209706 prefixEnd_209706 47857766280827448004705 := by
  unfold tailWord_209706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912151544569612944634243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5099070785518967852357981 1912151544569612944634243)
  ·
    refine ⟨2868227316854419416951365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1912151544569612944634243 2868227316854419416951365)
    ·
      refine ⟨537792621910203640678381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2868227316854419416951365 537792621910203640678381)
      ·
        refine ⟨201672233216326365254393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537792621910203640678381 201672233216326365254393)
        ·
          refine ⟨151254174912244773940795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201672233216326365254393 151254174912244773940795)
          ·
            refine ⟨226881262368367160911193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151254174912244773940795 226881262368367160911193)
            ·
              refine ⟨170160946776275370683395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226881262368367160911193 170160946776275370683395)
              ·
                refine ⟨255241420164413056025093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170160946776275370683395 255241420164413056025093)
                ·
                  refine ⟨47857766280827448004705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255241420164413056025093 47857766280827448004705)
                  ·
                    rfl

theorem cell21_209706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_209706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209706 prefixEnd_209706 := by exact prefixLift 209706
  have htrace : WordTrace (prefixWord ++ tailWord_209706) baseStart_209706 baseEnd_209706 := by
    simpa [prefixWord, tailWord_209706, baseEnd_209706] using wordTrace_append hprefix tailTrace_209706
  have hstable : (prefixWord ++ tailWord_209706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209706).length < 2 ^ (prefixWord ++ tailWord_209706).sum := by decide
  have hdescent : baseEnd_209706 < baseStart_209706 := by decide
  rcases family_descends (prefixWord ++ tailWord_209706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209714 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_209714 : Nat := 118140960795 + 209714 * 2 ^ 59
def prefixEnd_209714 : Nat := 4983230072969 + 3 ^ 40 * 209714 * 2
def baseEnd_209714 : Nat := 47859591989821211871355

theorem tailTrace_209714 : CollatzResearch.WordTrace tailWord_209714 prefixEnd_209714 47859591989821211871355 := by
  unfold tailWord_209714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912224490562367286207049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5099265308166312763218797 1912224490562367286207049)
  ·
    refine ⟨1434168367921775464655287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1912224490562367286207049 1434168367921775464655287)
    ·
      refine ⟨2151252551882663196982931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434168367921775464655287 2151252551882663196982931)
      ·
        refine ⟨3226878827823994795474397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151252551882663196982931 3226878827823994795474397)
        ·
          refine ⟨1210079560433998048302899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3226878827823994795474397 1210079560433998048302899)
          ·
            refine ⟨1815119340650997072454349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210079560433998048302899 1815119340650997072454349)
            ·
              refine ⟨680669752744123902170381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1815119340650997072454349 680669752744123902170381)
              ·
                refine ⟨255251157279046463313893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680669752744123902170381 255251157279046463313893)
                ·
                  refine ⟨47859591989821211871355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255251157279046463313893 47859591989821211871355)
                  ·
                    rfl

theorem cell21_209714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_209714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209714 prefixEnd_209714 := by exact prefixLift 209714
  have htrace : WordTrace (prefixWord ++ tailWord_209714) baseStart_209714 baseEnd_209714 := by
    simpa [prefixWord, tailWord_209714, baseEnd_209714] using wordTrace_append hprefix tailTrace_209714
  have hstable : (prefixWord ++ tailWord_209714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209714).length < 2 ^ (prefixWord ++ tailWord_209714).sum := by decide
  have hdescent : baseEnd_209714 < baseStart_209714 := by decide
  rcases family_descends (prefixWord ++ tailWord_209714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209762 : List Nat := [3, 3, 2, 1, 3, 2, 1, 6]
def baseStart_209762 : Nat := 118140960795 + 209762 * 2 ^ 59
def prefixEnd_209762 : Nat := 4983230072969 + 3 ^ 40 * 209762 * 2
def baseEnd_209762 : Nat := 15956848747927931690419

theorem tailTrace_209762 : CollatzResearch.WordTrace tailWord_209762 prefixEnd_209762 15956848747927931690419 := by
  unfold tailWord_209762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912662166518893335643885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5100432444050382228383693 1912662166518893335643885)
  ·
    refine ⟨717248312444585000866457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1912662166518893335643885 717248312444585000866457)
    ·
      refine ⟨537936234333438750649843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717248312444585000866457 537936234333438750649843)
      ·
        refine ⟨806904351500158125974765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537936234333438750649843 806904351500158125974765)
        ·
          refine ⟨302589131812559297240537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 806904351500158125974765 302589131812559297240537)
          ·
            refine ⟨226941848859419472930403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302589131812559297240537 226941848859419472930403)
            ·
              refine ⟨340412773289129209395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226941848859419472930403 340412773289129209395605)
              ·
                refine ⟨15956848747927931690419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340412773289129209395605 15956848747927931690419)
                ·
                  rfl

theorem cell21_209762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_209762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209762 prefixEnd_209762 := by exact prefixLift 209762
  have htrace : WordTrace (prefixWord ++ tailWord_209762) baseStart_209762 baseEnd_209762 := by
    simpa [prefixWord, tailWord_209762, baseEnd_209762] using wordTrace_append hprefix tailTrace_209762
  have hstable : (prefixWord ++ tailWord_209762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209762).length < 2 ^ (prefixWord ++ tailWord_209762).sum := by decide
  have hdescent : baseEnd_209762 < baseStart_209762 := by decide
  rcases family_descends (prefixWord ++ tailWord_209762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209773 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_209773 : Nat := 118140960795 + 209773 * 2 ^ 59
def prefixEnd_209773 : Nat := 4983230072969 + 3 ^ 40 * 209773 * 2
def baseEnd_209773 : Nat := 47873056593650220387901

theorem tailTrace_209773 : CollatzResearch.WordTrace tailWord_209773 prefixEnd_209773 47873056593650220387901 := by
  unfold tailWord_209773
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651049869035722221225973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5100699912690481480817315 7651049869035722221225973)
  ·
    refine ⟨717285925222098958239935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7651049869035722221225973 717285925222098958239935)
    ·
      refine ⟨1075928887833148437359903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717285925222098958239935 1075928887833148437359903)
      ·
        refine ⟨1613893331749722656039855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075928887833148437359903 1613893331749722656039855)
        ·
          refine ⟨2420839997624583984059783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613893331749722656039855 2420839997624583984059783)
          ·
            refine ⟨3631259996436875976089675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420839997624583984059783 3631259996436875976089675)
            ·
              refine ⟨5446889994655313964134513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631259996436875976089675 5446889994655313964134513)
              ·
                refine ⟨4085167495991485473100885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5446889994655313964134513 4085167495991485473100885)
                ·
                  refine ⟨47873056593650220387901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4085167495991485473100885 47873056593650220387901)
                  ·
                    rfl

theorem cell21_209773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_209773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209773 prefixEnd_209773 := by exact prefixLift 209773
  have htrace : WordTrace (prefixWord ++ tailWord_209773) baseStart_209773 baseEnd_209773 := by
    simpa [prefixWord, tailWord_209773, baseEnd_209773] using wordTrace_append hprefix tailTrace_209773
  have hstable : (prefixWord ++ tailWord_209773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209773).length < 2 ^ (prefixWord ++ tailWord_209773).sum := by decide
  have hdescent : baseEnd_209773 < baseStart_209773 := by decide
  rcases family_descends (prefixWord ++ tailWord_209773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209787 : List Nat := [1, 1, 1, 1, 1, 5, 2, 9]
def baseStart_209787 : Nat := 118140960795 + 209787 * 2 ^ 59
def prefixEnd_209787 : Nat := 4983230072969 + 3 ^ 40 * 209787 * 2
def baseEnd_209787 : Nat := 15958750528129769051513

theorem tailTrace_209787 : CollatzResearch.WordTrace tailWord_209787 prefixEnd_209787 15958750528129769051513 := by
  unfold tailWord_209787
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651560490985002612235615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5101040327323335074823743 7651560490985002612235615)
  ·
    refine ⟨11477340736477503918353423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7651560490985002612235615 11477340736477503918353423)
    ·
      refine ⟨17216011104716255877530135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11477340736477503918353423 17216011104716255877530135)
      ·
        refine ⟨25824016657074383816295203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17216011104716255877530135 25824016657074383816295203)
        ·
          refine ⟨38736024985611575724442805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25824016657074383816295203 38736024985611575724442805)
          ·
            refine ⟨3631502342401085224166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38736024985611575724442805 3631502342401085224166513)
            ·
              refine ⟨2723626756800813918124885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631502342401085224166513 2723626756800813918124885)
              ·
                refine ⟨15958750528129769051513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2723626756800813918124885 15958750528129769051513)
                ·
                  rfl

theorem cell21_209787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_209787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209787 prefixEnd_209787 := by exact prefixLift 209787
  have htrace : WordTrace (prefixWord ++ tailWord_209787) baseStart_209787 baseEnd_209787 := by
    simpa [prefixWord, tailWord_209787, baseEnd_209787] using wordTrace_append hprefix tailTrace_209787
  have hstable : (prefixWord ++ tailWord_209787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209787).length < 2 ^ (prefixWord ++ tailWord_209787).sum := by decide
  have hdescent : baseEnd_209787 < baseStart_209787 := by decide
  rcases family_descends (prefixWord ++ tailWord_209787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209849 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_209849 : Nat := 118140960795 + 209849 * 2 ^ 59
def prefixEnd_209849 : Nat := 4983230072969 + 3 ^ 40 * 209849 * 2
def baseEnd_209849 : Nat := 47890400829090977121079

theorem tailTrace_209849 : CollatzResearch.WordTrace tailWord_209849 prefixEnd_209849 47890400829090977121079 := by
  unfold tailWord_209849
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653821816760387200992601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5102547877840258133995067 7653821816760387200992601)
  ·
    refine ⟨5740366362570290400744451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7653821816760387200992601 5740366362570290400744451)
    ·
      refine ⟨8610549543855435601116677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740366362570290400744451 8610549543855435601116677)
      ·
        refine ⟨1614478039472894175209377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8610549543855435601116677 1614478039472894175209377)
        ·
          refine ⟨1210858529604670631407033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614478039472894175209377 1210858529604670631407033)
          ·
            refine ⟨908143897203502973555275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210858529604670631407033 908143897203502973555275)
            ·
              refine ⟨1362215845805254460332913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908143897203502973555275 1362215845805254460332913)
              ·
                refine ⟨1021661884353940845249685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362215845805254460332913 1021661884353940845249685)
                ·
                  refine ⟨47890400829090977121079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1021661884353940845249685 47890400829090977121079)
                  ·
                    rfl

theorem cell21_209849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_209849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209849 prefixEnd_209849 := by exact prefixLift 209849
  have htrace : WordTrace (prefixWord ++ tailWord_209849) baseStart_209849 baseEnd_209849 := by
    simpa [prefixWord, tailWord_209849, baseEnd_209849] using wordTrace_append hprefix tailTrace_209849
  have hstable : (prefixWord ++ tailWord_209849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209849).length < 2 ^ (prefixWord ++ tailWord_209849).sum := by decide
  have hdescent : baseEnd_209849 < baseStart_209849 := by decide
  rcases family_descends (prefixWord ++ tailWord_209849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209863 : List Nat := [1, 1, 4, 1, 1, 2, 11]
def baseStart_209863 : Nat := 118140960795 + 209863 * 2 ^ 59
def prefixEnd_209863 : Nat := 4983230072969 + 3 ^ 40 * 209863 * 2
def baseEnd_209863 : Nat := 5321510646647784876413

theorem tailTrace_209863 : CollatzResearch.WordTrace tailWord_209863 prefixEnd_209863 5321510646647784876413 := by
  unfold tailWord_209863
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654332438709667592002243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5102888292473111728001495 7654332438709667592002243)
  ·
    refine ⟨11481498658064501388003365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7654332438709667592002243 11481498658064501388003365)
    ·
      refine ⟨2152780998387094010250631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11481498658064501388003365 2152780998387094010250631)
      ·
        refine ⟨3229171497580641015375947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152780998387094010250631 3229171497580641015375947)
        ·
          refine ⟨4843757246370961523063921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229171497580641015375947 4843757246370961523063921)
          ·
            refine ⟨3632817934778221142297941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843757246370961523063921 3632817934778221142297941)
            ·
              refine ⟨5321510646647784876413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3632817934778221142297941 5321510646647784876413)
              ·
                rfl

theorem cell21_209863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 11].length) (baseStart_209863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209863 prefixEnd_209863 := by exact prefixLift 209863
  have htrace : WordTrace (prefixWord ++ tailWord_209863) baseStart_209863 baseEnd_209863 := by
    simpa [prefixWord, tailWord_209863, baseEnd_209863] using wordTrace_append hprefix tailTrace_209863
  have hstable : (prefixWord ++ tailWord_209863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209863).length < 2 ^ (prefixWord ++ tailWord_209863).sum := by decide
  have hdescent : baseEnd_209863 < baseStart_209863 := by decide
  rcases family_descends (prefixWord ++ tailWord_209863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209880 : List Nat := [2, 1, 2, 2, 2, 4, 2, 6]
def baseStart_209880 : Nat := 118140960795 + 209880 * 2 ^ 59
def prefixEnd_209880 : Nat := 4983230072969 + 3 ^ 40 * 209880 * 2
def baseEnd_209880 : Nat := 15965825150480604034783

theorem tailTrace_209880 : CollatzResearch.WordTrace tailWord_209880 prefixEnd_209880 15965825150480604034783 := by
  unfold tailWord_209880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827476239824039747685547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5103301653098719663580729 3827476239824039747685547)
  ·
    refine ⟨5741214359736059621528321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3827476239824039747685547 5741214359736059621528321)
    ·
      refine ⟨4305910769802044716146241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5741214359736059621528321 4305910769802044716146241)
      ·
        refine ⟨3229433077351533537109681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4305910769802044716146241 3229433077351533537109681)
        ·
          refine ⟨2422074808013650152832261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3229433077351533537109681 2422074808013650152832261)
          ·
            refine ⟨454139026502559403656049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2422074808013650152832261 454139026502559403656049)
            ·
              refine ⟨340604269876919552742037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454139026502559403656049 340604269876919552742037)
              ·
                refine ⟨15965825150480604034783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340604269876919552742037 15965825150480604034783)
                ·
                  rfl

theorem cell21_209880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_209880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209880 prefixEnd_209880 := by exact prefixLift 209880
  have htrace : WordTrace (prefixWord ++ tailWord_209880) baseStart_209880 baseEnd_209880 := by
    simpa [prefixWord, tailWord_209880, baseEnd_209880] using wordTrace_append hprefix tailTrace_209880
  have hstable : (prefixWord ++ tailWord_209880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209880).length < 2 ^ (prefixWord ++ tailWord_209880).sum := by decide
  have hdescent : baseEnd_209880 < baseStart_209880 := by decide
  rcases family_descends (prefixWord ++ tailWord_209880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209928 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_209928 : Nat := 118140960795 + 209928 * 2 ^ 59
def prefixEnd_209928 : Nat := 4983230072969 + 3 ^ 40 * 209928 * 2
def baseEnd_209928 : Nat := 47908429705404395304251

theorem tailTrace_209928 : CollatzResearch.WordTrace tailWord_209928 prefixEnd_209928 47908429705404395304251 := by
  unfold tailWord_209928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828351591737091846559219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5104468788982789128745625 3828351591737091846559219)
  ·
    refine ⟨5742527387605637769838829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3828351591737091846559219 5742527387605637769838829)
    ·
      refine ⟨2153447770352114163689561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5742527387605637769838829 2153447770352114163689561)
      ·
        refine ⟨1615085827764085622767171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153447770352114163689561 1615085827764085622767171)
        ·
          refine ⟨2422628741646128434150757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615085827764085622767171 2422628741646128434150757)
          ·
            refine ⟨454242889058649081403267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2422628741646128434150757 454242889058649081403267)
            ·
              refine ⟨681364333587973622104901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454242889058649081403267 681364333587973622104901)
              ·
                refine ⟨127755812547745054144669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681364333587973622104901 127755812547745054144669)
                ·
                  refine ⟨47908429705404395304251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127755812547745054144669 47908429705404395304251)
                  ·
                    rfl

theorem cell21_209928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_209928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209928 prefixEnd_209928 := by exact prefixLift 209928
  have htrace : WordTrace (prefixWord ++ tailWord_209928) baseStart_209928 baseEnd_209928 := by
    simpa [prefixWord, tailWord_209928, baseEnd_209928] using wordTrace_append hprefix tailTrace_209928
  have hstable : (prefixWord ++ tailWord_209928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209928).length < 2 ^ (prefixWord ++ tailWord_209928).sum := by decide
  have hdescent : baseEnd_209928 < baseStart_209928 := by decide
  rcases family_descends (prefixWord ++ tailWord_209928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209970 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_209970 : Nat := 118140960795 + 209970 * 2 ^ 59
def prefixEnd_209970 : Nat := 4983230072969 + 3 ^ 40 * 209970 * 2
def baseEnd_209970 : Nat := 47918014677621655604165

theorem tailTrace_209970 : CollatzResearch.WordTrace tailWord_209970 prefixEnd_209970 47918014677621655604165 := by
  unfold tailWord_209970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914558762330506216536841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5105490032881349910764909 1914558762330506216536841)
  ·
    refine ⟨1435919071747879662402631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1914558762330506216536841 1435919071747879662402631)
    ·
      refine ⟨2153878607621819493603947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435919071747879662402631 2153878607621819493603947)
      ·
        refine ⟨3230817911432729240405921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153878607621819493603947 3230817911432729240405921)
        ·
          refine ⟨2423113433574546930304441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3230817911432729240405921 2423113433574546930304441)
          ·
            refine ⟨1817335075180910197728331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423113433574546930304441 1817335075180910197728331)
            ·
              refine ⟨2726002612771365296592497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817335075180910197728331 2726002612771365296592497)
              ·
                refine ⟨2044501959578523972444373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726002612771365296592497 2044501959578523972444373)
                ·
                  refine ⟨47918014677621655604165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2044501959578523972444373 47918014677621655604165)
                  ·
                    rfl

theorem cell21_209970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_209970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209970 prefixEnd_209970 := by exact prefixLift 209970
  have htrace : WordTrace (prefixWord ++ tailWord_209970) baseStart_209970 baseEnd_209970 := by
    simpa [prefixWord, tailWord_209970, baseEnd_209970] using wordTrace_append hprefix tailTrace_209970
  have hstable : (prefixWord ++ tailWord_209970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209970).length < 2 ^ (prefixWord ++ tailWord_209970).sum := by decide
  have hdescent : baseEnd_209970 < baseStart_209970 := by decide
  rcases family_descends (prefixWord ++ tailWord_209970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209987 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 3]
def baseStart_209987 : Nat := 118140960795 + 209987 * 2 ^ 59
def prefixEnd_209987 : Nat := 4983230072969 + 3 ^ 40 * 209987 * 2
def baseEnd_209987 : Nat := 47921894309233403820797

theorem tailTrace_209987 : CollatzResearch.WordTrace tailWord_209987 prefixEnd_209987 47921894309233403820797 := by
  unfold tailWord_209987
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658855090260436769516215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105903393506957846344143 7658855090260436769516215)
  ·
    refine ⟨11488282635390655154274323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658855090260436769516215 11488282635390655154274323)
    ·
      refine ⟨17232423953085982731411485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488282635390655154274323 17232423953085982731411485)
      ·
        refine ⟨6462158982407243524279307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17232423953085982731411485 6462158982407243524279307)
        ·
          refine ⟨9693238473610865286418961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462158982407243524279307 9693238473610865286418961)
          ·
            refine ⟨7269928855208148964814221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693238473610865286418961 7269928855208148964814221)
            ·
              refine ⟨2726223320703055861805333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7269928855208148964814221 2726223320703055861805333)
              ·
                refine ⟨127791718157955743522125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2726223320703055861805333 127791718157955743522125)
                ·
                  refine ⟨47921894309233403820797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127791718157955743522125 47921894309233403820797)
                  ·
                    rfl

theorem cell21_209987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 3].length) (baseStart_209987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_209987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_209987 prefixEnd_209987 := by exact prefixLift 209987
  have htrace : WordTrace (prefixWord ++ tailWord_209987) baseStart_209987 baseEnd_209987 := by
    simpa [prefixWord, tailWord_209987, baseEnd_209987] using wordTrace_append hprefix tailTrace_209987
  have hstable : (prefixWord ++ tailWord_209987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209987).length < 2 ^ (prefixWord ++ tailWord_209987).sum := by decide
  have hdescent : baseEnd_209987 < baseStart_209987 := by decide
  rcases family_descends (prefixWord ++ tailWord_209987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210001 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_210001 : Nat := 118140960795 + 210001 * 2 ^ 59
def prefixEnd_210001 : Nat := 4983230072969 + 3 ^ 40 * 210001 * 2
def baseEnd_210001 : Nat := 47925089299972490587435

theorem tailTrace_210001 : CollatzResearch.WordTrace tailWord_210001 prefixEnd_210001 47925089299972490587435 := by
  unfold tailWord_210001
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659365712209717160525857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106243808139811440350571 7659365712209717160525857)
  ·
    refine ⟨5744524284157287870394393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7659365712209717160525857 5744524284157287870394393)
    ·
      refine ⟨4308393213117965902795795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5744524284157287870394393 4308393213117965902795795)
      ·
        refine ⟨6462589819676948854193693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308393213117965902795795 6462589819676948854193693)
        ·
          refine ⟨2423471182378855820322635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6462589819676948854193693 2423471182378855820322635)
          ·
            refine ⟨3635206773568283730483953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423471182378855820322635 3635206773568283730483953)
            ·
              refine ⟨2726405080176212797862965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635206773568283730483953 2726405080176212797862965)
              ·
                refine ⟨255600476266519949799653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2726405080176212797862965 255600476266519949799653)
                ·
                  refine ⟨47925089299972490587435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255600476266519949799653 47925089299972490587435)
                  ·
                    rfl

theorem cell21_210001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_210001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210001 prefixEnd_210001 := by exact prefixLift 210001
  have htrace : WordTrace (prefixWord ++ tailWord_210001) baseStart_210001 baseEnd_210001 := by
    simpa [prefixWord, tailWord_210001, baseEnd_210001] using wordTrace_append hprefix tailTrace_210001
  have hstable : (prefixWord ++ tailWord_210001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210001).length < 2 ^ (prefixWord ++ tailWord_210001).sum := by decide
  have hdescent : baseEnd_210001 < baseStart_210001 := by decide
  rcases family_descends (prefixWord ++ tailWord_210001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210015 : List Nat := [1, 1, 2, 3, 1, 1, 5, 7]
def baseStart_210015 : Nat := 118140960795 + 210015 * 2 ^ 59
def prefixEnd_210015 : Nat := 4983230072969 + 3 ^ 40 * 210015 * 2
def baseEnd_210015 : Nat := 15976094763570525784691

theorem tailTrace_210015 : CollatzResearch.WordTrace tailWord_210015 prefixEnd_210015 15976094763570525784691 := by
  unfold tailWord_210015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659876334158997551535499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106584222772665034356999 7659876334158997551535499)
  ·
    refine ⟨11489814501238496327303249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659876334158997551535499 11489814501238496327303249)
    ·
      refine ⟨8617360875928872245477437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11489814501238496327303249 8617360875928872245477437)
      ·
        refine ⟨3231510328473327092054039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8617360875928872245477437 3231510328473327092054039)
        ·
          refine ⟨4847265492709990638081059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231510328473327092054039 4847265492709990638081059)
          ·
            refine ⟨7270898239064985957121589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847265492709990638081059 7270898239064985957121589)
            ·
              refine ⟨681646709912342433480149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7270898239064985957121589 681646709912342433480149)
              ·
                refine ⟨15976094763570525784691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 681646709912342433480149 15976094763570525784691)
                ·
                  rfl

theorem cell21_210015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_210015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210015 prefixEnd_210015 := by exact prefixLift 210015
  have htrace : WordTrace (prefixWord ++ tailWord_210015) baseStart_210015 baseEnd_210015 := by
    simpa [prefixWord, tailWord_210015, baseEnd_210015] using wordTrace_append hprefix tailTrace_210015
  have hstable : (prefixWord ++ tailWord_210015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210015).length < 2 ^ (prefixWord ++ tailWord_210015).sum := by decide
  have hdescent : baseEnd_210015 < baseStart_210015 := by decide
  rcases family_descends (prefixWord ++ tailWord_210015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210018 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_210018 : Nat := 118140960795 + 210018 * 2 ^ 59
def prefixEnd_210018 : Nat := 4983230072969 + 3 ^ 40 * 210018 * 2
def baseEnd_210018 : Nat := 47928968931584238804067

theorem tailTrace_210018 : CollatzResearch.WordTrace tailWord_210018 prefixEnd_210018 47928968931584238804067 := by
  unfold tailWord_210018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914996438287032265973677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5106657168765419375929805 1914996438287032265973677)
  ·
    refine ⟨718123664357637099740129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1914996438287032265973677 718123664357637099740129)
    ·
      refine ⟨538592748268227824805097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 718123664357637099740129 538592748268227824805097)
      ·
        refine ⟨403944561201170868603823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538592748268227824805097 403944561201170868603823)
        ·
          refine ⟨605916841801756302905735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403944561201170868603823 605916841801756302905735)
          ·
            refine ⟨908875262702634454358603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605916841801756302905735 908875262702634454358603)
            ·
              refine ⟨1363312894053951681537905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908875262702634454358603 1363312894053951681537905)
              ·
                refine ⟨1022484670540463761153429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363312894053951681537905 1022484670540463761153429)
                ·
                  refine ⟨47928968931584238804067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1022484670540463761153429 47928968931584238804067)
                  ·
                    rfl

theorem cell21_210018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_210018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210018 prefixEnd_210018 := by exact prefixLift 210018
  have htrace : WordTrace (prefixWord ++ tailWord_210018) baseStart_210018 baseEnd_210018 := by
    simpa [prefixWord, tailWord_210018, baseEnd_210018] using wordTrace_append hprefix tailTrace_210018
  have hstable : (prefixWord ++ tailWord_210018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210018).length < 2 ^ (prefixWord ++ tailWord_210018).sum := by decide
  have hdescent : baseEnd_210018 < baseStart_210018 := by decide
  rcases family_descends (prefixWord ++ tailWord_210018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210097 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 3]
def baseStart_210097 : Nat := 118140960795 + 210097 * 2 ^ 59
def prefixEnd_210097 : Nat := 4983230072969 + 3 ^ 40 * 210097 * 2
def baseEnd_210097 : Nat := 47946997807897656987239

theorem tailTrace_210097 : CollatzResearch.WordTrace tailWord_210097 prefixEnd_210097 47946997807897656987239 := by
  unfold tailWord_210097
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662867119861925556020545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5108578079907950370680363 7662867119861925556020545)
  ·
    refine ⟨5747150339896444167015409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7662867119861925556020545 5747150339896444167015409)
    ·
      refine ⟨4310362754922333125261557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5747150339896444167015409 4310362754922333125261557)
      ·
        refine ⟨404096508273968730493271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4310362754922333125261557 404096508273968730493271)
        ·
          refine ⟨606144762410953095739907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404096508273968730493271 606144762410953095739907)
          ·
            refine ⟨909217143616429643609861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606144762410953095739907 909217143616429643609861)
            ·
              refine ⟨170478214428080558176849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 909217143616429643609861 170478214428080558176849)
              ·
                refine ⟨127858660821060418632637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170478214428080558176849 127858660821060418632637)
                ·
                  refine ⟨47946997807897656987239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127858660821060418632637 47946997807897656987239)
                  ·
                    rfl

theorem cell21_210097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_210097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210097 prefixEnd_210097 := by exact prefixLift 210097
  have htrace : WordTrace (prefixWord ++ tailWord_210097) baseStart_210097 baseEnd_210097 := by
    simpa [prefixWord, tailWord_210097, baseEnd_210097] using wordTrace_append hprefix tailTrace_210097
  have hstable : (prefixWord ++ tailWord_210097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210097).length < 2 ^ (prefixWord ++ tailWord_210097).sum := by decide
  have hdescent : baseEnd_210097 < baseStart_210097 := by decide
  rcases family_descends (prefixWord ++ tailWord_210097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210108 : List Nat := [2, 2, 2, 3, 2, 1, 3, 6]
def baseStart_210108 : Nat := 118140960795 + 210108 * 2 ^ 59
def prefixEnd_210108 : Nat := 4983230072969 + 3 ^ 40 * 210108 * 2
def baseEnd_210108 : Nat := 15983169385921360767961

theorem tailTrace_210108 : CollatzResearch.WordTrace tailWord_210108 prefixEnd_210108 15983169385921360767961 := by
  unfold tailWord_210108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831634161411037217335489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5108845548548049623113985 3831634161411037217335489)
  ·
    refine ⟨2873725621058277913001617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3831634161411037217335489 2873725621058277913001617)
    ·
      refine ⟨2155294215793708434751213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2873725621058277913001617 2155294215793708434751213)
      ·
        refine ⟨808235330922640663031705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2155294215793708434751213 808235330922640663031705)
        ·
          refine ⟨606176498191980497273779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808235330922640663031705 606176498191980497273779)
          ·
            refine ⟨909264747287970745910669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606176498191980497273779 909264747287970745910669)
            ·
              refine ⟨340974280232989029716501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909264747287970745910669 340974280232989029716501)
              ·
                refine ⟨15983169385921360767961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340974280232989029716501 15983169385921360767961)
                ·
                  rfl

theorem cell21_210108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_210108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210108 prefixEnd_210108 := by exact prefixLift 210108
  have htrace : WordTrace (prefixWord ++ tailWord_210108) baseStart_210108 baseEnd_210108 := by
    simpa [prefixWord, tailWord_210108, baseEnd_210108] using wordTrace_append hprefix tailTrace_210108
  have hstable : (prefixWord ++ tailWord_210108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210108).length < 2 ^ (prefixWord ++ tailWord_210108).sum := by decide
  have hdescent : baseEnd_210108 < baseStart_210108 := by decide
  rcases family_descends (prefixWord ++ tailWord_210108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210122 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_210122 : Nat := 118140960795 + 210122 * 2 ^ 59
def prefixEnd_210122 : Nat := 4983230072969 + 3 ^ 40 * 210122 * 2
def baseEnd_210122 : Nat := 47952703148503169070521

theorem tailTrace_210122 : CollatzResearch.WordTrace tailWord_210122 prefixEnd_210122 47952703148503169070521 := by
  unfold tailWord_210122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915944736192838706420155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5109185963180903217120413 1915944736192838706420155)
  ·
    refine ⟨2873917104289258059630233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915944736192838706420155 2873917104289258059630233)
    ·
      refine ⟨2155437828216943544722675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2873917104289258059630233 2155437828216943544722675)
      ·
        refine ⟨3233156742325415317084013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2155437828216943544722675 3233156742325415317084013)
        ·
          refine ⟨1212433778372030743906505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3233156742325415317084013 1212433778372030743906505)
          ·
            refine ⟨909325333779023057929879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212433778372030743906505 909325333779023057929879)
            ·
              refine ⟨1363988000668534586894819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909325333779023057929879 1363988000668534586894819)
              ·
                refine ⟨2045982001002801880342229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363988000668534586894819 2045982001002801880342229)
                ·
                  refine ⟨47952703148503169070521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2045982001002801880342229 47952703148503169070521)
                  ·
                    rfl

theorem cell21_210122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_210122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210122 prefixEnd_210122 := by exact prefixLift 210122
  have htrace : WordTrace (prefixWord ++ tailWord_210122) baseStart_210122 baseEnd_210122 := by
    simpa [prefixWord, tailWord_210122, baseEnd_210122] using wordTrace_append hprefix tailTrace_210122
  have hstable : (prefixWord ++ tailWord_210122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210122).length < 2 ^ (prefixWord ++ tailWord_210122).sum := by decide
  have hdescent : baseEnd_210122 < baseStart_210122 := by decide
  rcases family_descends (prefixWord ++ tailWord_210122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210170 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_210170 : Nat := 118140960795 + 210170 * 2 ^ 59
def prefixEnd_210170 : Nat := 4983230072969 + 3 ^ 40 * 210170 * 2
def baseEnd_210170 : Nat := 47963657402465752270423

theorem tailTrace_210170 : CollatzResearch.WordTrace tailWord_210170 prefixEnd_210170 47963657402465752270423 := by
  unfold tailWord_210170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916382412149364755856991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5110353099064972682285309 1916382412149364755856991)
  ·
    refine ⟨2874573618224047133785487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1916382412149364755856991 2874573618224047133785487)
    ·
      refine ⟨4311860427336070700678231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874573618224047133785487 4311860427336070700678231)
      ·
        refine ⟨6467790641004106051017347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311860427336070700678231 6467790641004106051017347)
        ·
          refine ⟨9701685961506159076526021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467790641004106051017347 9701685961506159076526021)
          ·
            refine ⟨1819066117782404826848629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9701685961506159076526021 1819066117782404826848629)
            ·
              refine ⟨170537448542100452517059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1819066117782404826848629 170537448542100452517059)
              ·
                refine ⟨255806172813150678775589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170537448542100452517059 255806172813150678775589)
                ·
                  refine ⟨47963657402465752270423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255806172813150678775589 47963657402465752270423)
                  ·
                    rfl

theorem cell21_210170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_210170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210170 prefixEnd_210170 := by exact prefixLift 210170
  have htrace : WordTrace (prefixWord ++ tailWord_210170) baseStart_210170 baseEnd_210170 := by
    simpa [prefixWord, tailWord_210170, baseEnd_210170] using wordTrace_append hprefix tailTrace_210170
  have hstable : (prefixWord ++ tailWord_210170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210170).length < 2 ^ (prefixWord ++ tailWord_210170).sum := by decide
  have hdescent : baseEnd_210170 < baseStart_210170 := by decide
  rcases family_descends (prefixWord ++ tailWord_210170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210184 : List Nat := [2, 1, 3, 2, 4, 1, 1, 7]
def baseStart_210184 : Nat := 118140960795 + 210184 * 2 ^ 59
def prefixEnd_210184 : Nat := 4983230072969 + 3 ^ 40 * 210184 * 2
def baseEnd_210184 : Nat := 15988950797734946345687

theorem tailTrace_210184 : CollatzResearch.WordTrace tailWord_210184 prefixEnd_210184 15988950797734946345687 := by
  unfold tailWord_210184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833020135273369707218803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5110693513697826276291737 3833020135273369707218803)
  ·
    refine ⟨5749530202910054560828205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3833020135273369707218803 5749530202910054560828205)
    ·
      refine ⟨2156073826091270460310577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5749530202910054560828205 2156073826091270460310577)
      ·
        refine ⟨1617055369568452845232933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156073826091270460310577 1617055369568452845232933)
        ·
          refine ⟨303197881794084908481175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1617055369568452845232933 303197881794084908481175)
          ·
            refine ⟨454796822691127362721763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303197881794084908481175 454796822691127362721763)
            ·
              refine ⟨682195234036691044082645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454796822691127362721763 682195234036691044082645)
              ·
                refine ⟨15988950797734946345687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 682195234036691044082645 15988950797734946345687)
                ·
                  rfl

theorem cell21_210184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_210184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210184 prefixEnd_210184 := by exact prefixLift 210184
  have htrace : WordTrace (prefixWord ++ tailWord_210184) baseStart_210184 baseEnd_210184 := by
    simpa [prefixWord, tailWord_210184, baseEnd_210184] using wordTrace_append hprefix tailTrace_210184
  have hstable : (prefixWord ++ tailWord_210184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210184).length < 2 ^ (prefixWord ++ tailWord_210184).sum := by decide
  have hdescent : baseEnd_210184 < baseStart_210184 := by decide
  rcases family_descends (prefixWord ++ tailWord_210184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210308 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_210308 : Nat := 118140960795 + 210308 * 2 ^ 59
def prefixEnd_210308 : Nat := 4983230072969 + 3 ^ 40 * 210308 * 2
def baseEnd_210308 : Nat := 47995150882608178970141

theorem tailTrace_210308 : CollatzResearch.WordTrace tailWord_210308 prefixEnd_210308 47995150882608178970141 := by
  unfold tailWord_210308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835281461048754295975789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5113708614731672394634385 3835281461048754295975789)
  ·
    refine ⟨1438230547893282860990921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3835281461048754295975789 1438230547893282860990921)
    ·
      refine ⟨1078672910919962145743191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1438230547893282860990921 1078672910919962145743191)
      ·
        refine ⟨1618009366379943218614787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078672910919962145743191 1618009366379943218614787)
        ·
          refine ⟨2427014049569914827922181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618009366379943218614787 2427014049569914827922181)
          ·
            refine ⟨455065134294359030235409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2427014049569914827922181 455065134294359030235409)
            ·
              refine ⟨341298850720769272676557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455065134294359030235409 341298850720769272676557)
              ·
                refine ⟨127987069020288477253709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341298850720769272676557 127987069020288477253709)
                ·
                  refine ⟨47995150882608178970141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127987069020288477253709 47995150882608178970141)
                  ·
                    rfl

theorem cell21_210308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_210308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210308 prefixEnd_210308 := by exact prefixLift 210308
  have htrace : WordTrace (prefixWord ++ tailWord_210308) baseStart_210308 baseEnd_210308 := by
    simpa [prefixWord, tailWord_210308, baseEnd_210308] using wordTrace_append hprefix tailTrace_210308
  have hstable : (prefixWord ++ tailWord_210308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210308).length < 2 ^ (prefixWord ++ tailWord_210308).sum := by decide
  have hdescent : baseEnd_210308 < baseStart_210308 := by decide
  rcases family_descends (prefixWord ++ tailWord_210308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210440 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_210440 : Nat := 118140960795 + 210440 * 2 ^ 59
def prefixEnd_210440 : Nat := 4983230072969 + 3 ^ 40 * 210440 * 2
def baseEnd_210440 : Nat := 48025275081005282769871

theorem tailTrace_210440 : CollatzResearch.WordTrace tailWord_210440 prefixEnd_210440 48025275081005282769871 := by
  unfold tailWord_210440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837688678809647567878387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5116918238412863423837849 3837688678809647567878387)
  ·
    refine ⟨5756533018214471351817581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3837688678809647567878387 5756533018214471351817581)
    ·
      refine ⟨2158699881830426756931593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5756533018214471351817581 2158699881830426756931593)
      ·
        refine ⟨1619024911372820067698695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158699881830426756931593 1619024911372820067698695)
        ·
          refine ⟨2428537367059230101548043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619024911372820067698695 2428537367059230101548043)
          ·
            refine ⟨3642806050588845152322065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428537367059230101548043 3642806050588845152322065)
            ·
              refine ⟨2732104537941633864241549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642806050588845152322065 2732104537941633864241549)
              ·
                refine ⟨1024539201728112699090581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2732104537941633864241549 1024539201728112699090581)
                ·
                  refine ⟨48025275081005282769871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1024539201728112699090581 48025275081005282769871)
                  ·
                    rfl

theorem cell21_210440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_210440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210440 prefixEnd_210440 := by exact prefixLift 210440
  have htrace : WordTrace (prefixWord ++ tailWord_210440) baseStart_210440 baseEnd_210440 := by
    simpa [prefixWord, tailWord_210440, baseEnd_210440] using wordTrace_append hprefix tailTrace_210440
  have hstable : (prefixWord ++ tailWord_210440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210440).length < 2 ^ (prefixWord ++ tailWord_210440).sum := by decide
  have hdescent : baseEnd_210440 < baseStart_210440 := by decide
  rcases family_descends (prefixWord ++ tailWord_210440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210536 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_210536 : Nat := 118140960795 + 210536 * 2 ^ 59
def prefixEnd_210536 : Nat := 4983230072969 + 3 ^ 40 * 210536 * 2
def baseEnd_210536 : Nat := 48047183588930449169675

theorem tailTrace_210536 : CollatzResearch.WordTrace tailWord_210536 prefixEnd_210536 48047183588930449169675 := by
  unfold tailWord_210536
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839439382635751765625731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5119252510181002354167641 3839439382635751765625731)
  ·
    refine ⟨5759159073953627648438597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3839439382635751765625731 5759159073953627648438597)
    ·
      refine ⟨1079842326366305184082237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5759159073953627648438597 1079842326366305184082237)
      ·
        refine ⟨404940872387364444030839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1079842326366305184082237 404940872387364444030839)
        ·
          refine ⟨607411308581046666046259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404940872387364444030839 607411308581046666046259)
          ·
            refine ⟨911116962871569999069389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607411308581046666046259 911116962871569999069389)
            ·
              refine ⟨341668861076838749651021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911116962871569999069389 341668861076838749651021)
              ·
                refine ⟨128125822903814531119133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341668861076838749651021 128125822903814531119133)
                ·
                  refine ⟨48047183588930449169675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128125822903814531119133 48047183588930449169675)
                  ·
                    rfl

theorem cell21_210536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_210536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210536 prefixEnd_210536 := by exact prefixLift 210536
  have htrace : WordTrace (prefixWord ++ tailWord_210536) baseStart_210536 baseEnd_210536 := by
    simpa [prefixWord, tailWord_210536, baseEnd_210536] using wordTrace_append hprefix tailTrace_210536
  have hstable : (prefixWord ++ tailWord_210536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210536).length < 2 ^ (prefixWord ++ tailWord_210536).sum := by decide
  have hdescent : baseEnd_210536 < baseStart_210536 := by decide
  rcases family_descends (prefixWord ++ tailWord_210536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210564 : List Nat := [2, 3, 2, 1, 4, 1, 2, 6]
def baseStart_210564 : Nat := 118140960795 + 210564 * 2 ^ 59
def prefixEnd_210564 : Nat := 4983230072969 + 3 ^ 40 * 210564 * 2
def baseEnd_210564 : Nat := 16017857856802874234317

theorem tailTrace_210564 : CollatzResearch.WordTrace tailWord_210564 prefixEnd_210564 16017857856802874234317 := by
  unfold tailWord_210564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839950004585032156635373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5119933339446709542180497 3839950004585032156635373)
  ·
    refine ⟨1439981251719387058738265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3839950004585032156635373 1439981251719387058738265)
    ·
      refine ⟨1079985938789540294053699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1439981251719387058738265 1079985938789540294053699)
      ·
        refine ⟨1619978908184310441080549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079985938789540294053699 1619978908184310441080549)
        ·
          refine ⟨303746045284558207702603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1619978908184310441080549 303746045284558207702603)
          ·
            refine ⟨455619067926837311553905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303746045284558207702603 455619067926837311553905)
            ·
              refine ⟨341714300945127983665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455619067926837311553905 341714300945127983665429)
              ·
                refine ⟨16017857856802874234317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341714300945127983665429 16017857856802874234317)
                ·
                  rfl

theorem cell21_210564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_210564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210564 prefixEnd_210564 := by exact prefixLift 210564
  have htrace : WordTrace (prefixWord ++ tailWord_210564) baseStart_210564 baseEnd_210564 := by
    simpa [prefixWord, tailWord_210564, baseEnd_210564] using wordTrace_append hprefix tailTrace_210564
  have hstable : (prefixWord ++ tailWord_210564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210564).length < 2 ^ (prefixWord ++ tailWord_210564).sum := by decide
  have hdescent : baseEnd_210564 < baseStart_210564 := by decide
  rcases family_descends (prefixWord ++ tailWord_210564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210646 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_210646 : Nat := 118140960795 + 210646 * 2 ^ 59
def prefixEnd_210646 : Nat := 4983230072969 + 3 ^ 40 * 210646 * 2
def baseEnd_210646 : Nat := 48072287087594702336117

theorem tailTrace_210646 : CollatzResearch.WordTrace tailWord_210646 prefixEnd_210646 48072287087594702336117 := by
  unfold tailWord_210646
  simp only [CollatzResearch.WordTrace]
  refine ⟨480180674679562019859737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5121927196581994878503861 480180674679562019859737)
  ·
    refine ⟨360135506009671514894803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 480180674679562019859737 360135506009671514894803)
    ·
      refine ⟨540203259014507272342205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360135506009671514894803 540203259014507272342205)
      ·
        refine ⟨202576222130440227128327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540203259014507272342205 202576222130440227128327)
        ·
          refine ⟨303864333195660340692491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202576222130440227128327 303864333195660340692491)
          ·
            refine ⟨455796499793490511038737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303864333195660340692491 455796499793490511038737)
            ·
              refine ⟨341847374845117883279053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455796499793490511038737 341847374845117883279053)
              ·
                refine ⟨128192765566919206229645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341847374845117883279053 128192765566919206229645)
                ·
                  refine ⟨48072287087594702336117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128192765566919206229645 48072287087594702336117)
                  ·
                    rfl

theorem cell21_210646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_210646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210646 prefixEnd_210646 := by exact prefixLift 210646
  have htrace : WordTrace (prefixWord ++ tailWord_210646) baseStart_210646 baseEnd_210646 := by
    simpa [prefixWord, tailWord_210646, baseEnd_210646] using wordTrace_append hprefix tailTrace_210646
  have hstable : (prefixWord ++ tailWord_210646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210646).length < 2 ^ (prefixWord ++ tailWord_210646).sum := by decide
  have hdescent : baseEnd_210646 < baseStart_210646 := by decide
  rcases family_descends (prefixWord ++ tailWord_210646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210682 : List Nat := [3, 1, 1, 1, 1, 3, 1, 10]
def baseStart_210682 : Nat := 118140960795 + 210682 * 2 ^ 59
def prefixEnd_210682 : Nat := 4983230072969 + 3 ^ 40 * 210682 * 2
def baseEnd_210682 : Nat := 16026834259355546578681

theorem tailTrace_210682 : CollatzResearch.WordTrace tailWord_210682 prefixEnd_210682 16026834259355546578681 := by
  unfold tailWord_210682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921050955685642616516575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5122802548495046977377533 1921050955685642616516575)
  ·
    refine ⟨2881576433528463924774863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921050955685642616516575 2881576433528463924774863)
    ·
      refine ⟨4322364650292695887162295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2881576433528463924774863 4322364650292695887162295)
      ·
        refine ⟨6483546975439043830743443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4322364650292695887162295 6483546975439043830743443)
        ·
          refine ⟨9725320463158565746115165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483546975439043830743443 9725320463158565746115165)
          ·
            refine ⟨3646995173684462154793187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9725320463158565746115165 3646995173684462154793187)
            ·
              refine ⟨5470492760526693232189781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646995173684462154793187 5470492760526693232189781)
              ·
                refine ⟨16026834259355546578681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5470492760526693232189781 16026834259355546578681)
                ·
                  rfl

theorem cell21_210682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_210682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210682 prefixEnd_210682 := by exact prefixLift 210682
  have htrace : WordTrace (prefixWord ++ tailWord_210682) baseStart_210682 baseEnd_210682 := by
    simpa [prefixWord, tailWord_210682, baseEnd_210682] using wordTrace_append hprefix tailTrace_210682
  have hstable : (prefixWord ++ tailWord_210682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210682).length < 2 ^ (prefixWord ++ tailWord_210682).sum := by decide
  have hdescent : baseEnd_210682 < baseStart_210682 := by decide
  rcases family_descends (prefixWord ++ tailWord_210682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210699 : List Nat := [1, 1, 1, 1, 5, 1, 6, 5]
def baseStart_210699 : Nat := 118140960795 + 210699 * 2 ^ 59
def prefixEnd_210699 : Nat := 4983230072969 + 3 ^ 40 * 210699 * 2
def baseEnd_210699 : Nat := 16028127469892795984225

theorem tailTrace_210699 : CollatzResearch.WordTrace tailWord_210699 prefixEnd_210699 16028127469892795984225 := by
  unfold tailWord_210699
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684823863680982369435151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5123215909120654912956767 7684823863680982369435151)
  ·
    refine ⟨11527235795521473554152727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684823863680982369435151 11527235795521473554152727)
    ·
      refine ⟨17290853693282210331229091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527235795521473554152727 17290853693282210331229091)
      ·
        refine ⟨25936280539923315496843637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17290853693282210331229091 25936280539923315496843637)
        ·
          refine ⟨2431526300617810827829091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25936280539923315496843637 2431526300617810827829091)
          ·
            refine ⟨3647289450926716241743637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431526300617810827829091 3647289450926716241743637)
            ·
              refine ⟨170966693012189823831733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3647289450926716241743637 170966693012189823831733)
              ·
                refine ⟨16028127469892795984225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170966693012189823831733 16028127469892795984225)
                ·
                  rfl

theorem cell21_210699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 5].length) (baseStart_210699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210699 prefixEnd_210699 := by exact prefixLift 210699
  have htrace : WordTrace (prefixWord ++ tailWord_210699) baseStart_210699 baseEnd_210699 := by
    simpa [prefixWord, tailWord_210699, baseEnd_210699] using wordTrace_append hprefix tailTrace_210699
  have hstable : (prefixWord ++ tailWord_210699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210699).length < 2 ^ (prefixWord ++ tailWord_210699).sum := by decide
  have hdescent : baseEnd_210699 < baseStart_210699 := by decide
  rcases family_descends (prefixWord ++ tailWord_210699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210775 : List Nat := [1, 1, 3, 2, 6, 8]
def baseStart_210775 : Nat := 118140960795 + 210775 * 2 ^ 59
def prefixEnd_210775 : Nat := 4983230072969 + 3 ^ 40 * 210775 * 2
def baseEnd_210775 : Nat := 1781545431300709062439

theorem tailTrace_210775 : CollatzResearch.WordTrace tailWord_210775 prefixEnd_210775 1781545431300709062439 := by
  unfold tailWord_210775
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687595811405647349201779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5125063874270431566134519 7687595811405647349201779)
  ·
    refine ⟨11531393717108471023802669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7687595811405647349201779 11531393717108471023802669)
    ·
      refine ⟨4324272643915676633926001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11531393717108471023802669 4324272643915676633926001)
      ·
        refine ⟨3243204482936757475444501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324272643915676633926001 3243204482936757475444501)
        ·
          refine ⟨152025210137660506661461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3243204482936757475444501 152025210137660506661461)
          ·
            refine ⟨1781545431300709062439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 152025210137660506661461 1781545431300709062439)
            ·
              rfl

theorem cell21_210775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 8].length) (baseStart_210775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210775 prefixEnd_210775 := by exact prefixLift 210775
  have htrace : WordTrace (prefixWord ++ tailWord_210775) baseStart_210775 baseEnd_210775 := by
    simpa [prefixWord, tailWord_210775, baseEnd_210775] using wordTrace_append hprefix tailTrace_210775
  have hstable : (prefixWord ++ tailWord_210775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210775).length < 2 ^ (prefixWord ++ tailWord_210775).sum := by decide
  have hdescent : baseEnd_210775 < baseStart_210775 := by decide
  rcases family_descends (prefixWord ++ tailWord_210775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210789 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_210789 : Nat := 118140960795 + 210789 * 2 ^ 59
def prefixEnd_210789 : Nat := 4983230072969 + 3 ^ 40 * 210789 * 2
def baseEnd_210789 : Nat := 48104921635858231452491

theorem tailTrace_210789 : CollatzResearch.WordTrace tailWord_210789 prefixEnd_210789 48104921635858231452491 := by
  unfold tailWord_210789
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688106433354927740211421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5125404288903285160140947 7688106433354927740211421)
  ·
    refine ⟨2883039912508097902579283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7688106433354927740211421 2883039912508097902579283)
    ·
      refine ⟨4324559868762146853868925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883039912508097902579283 4324559868762146853868925)
      ·
        refine ⟨1621709950785805070200847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4324559868762146853868925 1621709950785805070200847)
        ·
          refine ⟨2432564926178707605301271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621709950785805070200847 2432564926178707605301271)
          ·
            refine ⟨3648847389268061407951907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432564926178707605301271 3648847389268061407951907)
            ·
              refine ⟨5473271083902092111927861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648847389268061407951907 5473271083902092111927861)
              ·
                refine ⟨513119164115821135493237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5473271083902092111927861 513119164115821135493237)
                ·
                  refine ⟨48104921635858231452491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 513119164115821135493237 48104921635858231452491)
                  ·
                    rfl

theorem cell21_210789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_210789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210789 prefixEnd_210789 := by exact prefixLift 210789
  have htrace : WordTrace (prefixWord ++ tailWord_210789) baseStart_210789 baseEnd_210789 := by
    simpa [prefixWord, tailWord_210789, baseEnd_210789] using wordTrace_append hprefix tailTrace_210789
  have hstable : (prefixWord ++ tailWord_210789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210789).length < 2 ^ (prefixWord ++ tailWord_210789).sum := by decide
  have hdescent : baseEnd_210789 < baseStart_210789 := by decide
  rcases family_descends (prefixWord ++ tailWord_210789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210803 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_210803 : Nat := 118140960795 + 210803 * 2 ^ 59
def prefixEnd_210803 : Nat := 4983230072969 + 3 ^ 40 * 210803 * 2
def baseEnd_210803 : Nat := 48108116626597318219129

theorem tailTrace_210803 : CollatzResearch.WordTrace tailWord_210803 prefixEnd_210803 48108116626597318219129 := by
  unfold tailWord_210803
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688617055304208131221063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5125744703536138754147375 7688617055304208131221063)
  ·
    refine ⟨11532925582956312196831595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7688617055304208131221063 11532925582956312196831595)
    ·
      refine ⟨17299388374434468295247393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11532925582956312196831595 17299388374434468295247393)
      ·
        refine ⟨12974541280825851221435545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17299388374434468295247393 12974541280825851221435545)
        ·
          refine ⟨9730905960619388416076659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12974541280825851221435545 9730905960619388416076659)
          ·
            refine ⟨14596358940929082624114989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9730905960619388416076659 14596358940929082624114989)
            ·
              refine ⟨5473634602848405984043121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14596358940929082624114989 5473634602848405984043121)
              ·
                refine ⟨4105225952136304488032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5473634602848405984043121 4105225952136304488032341)
                ·
                  refine ⟨48108116626597318219129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4105225952136304488032341 48108116626597318219129)
                  ·
                    rfl

theorem cell21_210803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_210803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210803 prefixEnd_210803 := by exact prefixLift 210803
  have htrace : WordTrace (prefixWord ++ tailWord_210803) baseStart_210803 baseEnd_210803 := by
    simpa [prefixWord, tailWord_210803, baseEnd_210803] using wordTrace_append hprefix tailTrace_210803
  have hstable : (prefixWord ++ tailWord_210803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210803).length < 2 ^ (prefixWord ++ tailWord_210803).sum := by decide
  have hdescent : baseEnd_210803 < baseStart_210803 := by decide
  rcases family_descends (prefixWord ++ tailWord_210803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210879 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_210879 : Nat := 118140960795 + 210879 * 2 ^ 59
def prefixEnd_210879 : Nat := 4983230072969 + 3 ^ 40 * 210879 * 2
def baseEnd_210879 : Nat := 48125460862038074952307

theorem tailTrace_210879 : CollatzResearch.WordTrace tailWord_210879 prefixEnd_210879 48125460862038074952307 := by
  unfold tailWord_210879
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691389003028873110987691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5127592668685915407325127 7691389003028873110987691)
  ·
    refine ⟨11537083504543309666481537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7691389003028873110987691 11537083504543309666481537)
    ·
      refine ⟨8652812628407482249861153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11537083504543309666481537 8652812628407482249861153)
      ·
        refine ⟨6489609471305611687395865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8652812628407482249861153 6489609471305611687395865)
        ·
          refine ⟨4867207103479208765546899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6489609471305611687395865 4867207103479208765546899)
          ·
            refine ⟨7300810655218813148320349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867207103479208765546899 7300810655218813148320349)
            ·
              refine ⟨2737803995707054930620131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7300810655218813148320349 2737803995707054930620131)
              ·
                refine ⟨4106705993560582395930197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737803995707054930620131 4106705993560582395930197)
                ·
                  refine ⟨48125460862038074952307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4106705993560582395930197 48125460862038074952307)
                  ·
                    rfl

theorem cell21_210879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_210879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210879 prefixEnd_210879 := by exact prefixLift 210879
  have htrace : WordTrace (prefixWord ++ tailWord_210879) baseStart_210879 baseEnd_210879 := by
    simpa [prefixWord, tailWord_210879, baseEnd_210879] using wordTrace_append hprefix tailTrace_210879
  have hstable : (prefixWord ++ tailWord_210879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210879).length < 2 ^ (prefixWord ++ tailWord_210879).sum := by decide
  have hdescent : baseEnd_210879 < baseStart_210879 := by decide
  rcases family_descends (prefixWord ++ tailWord_210879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210913 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 4]
def baseStart_210913 : Nat := 118140960795 + 210913 * 2 ^ 59
def prefixEnd_210913 : Nat := 4983230072969 + 3 ^ 40 * 210913 * 2
def baseEnd_210913 : Nat := 48133220125261571385571

theorem tailTrace_210913 : CollatzResearch.WordTrace tailWord_210913 prefixEnd_210913 48133220125261571385571 := by
  unfold tailWord_210913
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692629084905696917725393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5128419389937131278483595 7692629084905696917725393)
  ·
    refine ⟨5769471813679272688294045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7692629084905696917725393 5769471813679272688294045)
    ·
      refine ⟨2163551930129727258110267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5769471813679272688294045 2163551930129727258110267)
      ·
        refine ⟨3245327895194590887165401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163551930129727258110267 3245327895194590887165401)
        ·
          refine ⟨2433995921395943165374051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3245327895194590887165401 2433995921395943165374051)
          ·
            refine ⟨3650993882093914748061077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433995921395943165374051 3650993882093914748061077)
            ·
              refine ⟨171140338223152253815363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3650993882093914748061077 171140338223152253815363)
              ·
                refine ⟨256710507334728380723045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171140338223152253815363 256710507334728380723045)
                ·
                  refine ⟨48133220125261571385571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256710507334728380723045 48133220125261571385571)
                  ·
                    rfl

theorem cell21_210913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_210913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_210913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_210913 prefixEnd_210913 := by exact prefixLift 210913
  have htrace : WordTrace (prefixWord ++ tailWord_210913) baseStart_210913 baseEnd_210913 := by
    simpa [prefixWord, tailWord_210913, baseEnd_210913] using wordTrace_append hprefix tailTrace_210913
  have hstable : (prefixWord ++ tailWord_210913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210913).length < 2 ^ (prefixWord ++ tailWord_210913).sum := by decide
  have hdescent : baseEnd_210913 < baseStart_210913 := by decide
  rcases family_descends (prefixWord ++ tailWord_210913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211017 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_211017 : Nat := 118140960795 + 211017 * 2 ^ 59
def prefixEnd_211017 : Nat := 4983230072969 + 3 ^ 40 * 211017 * 2
def baseEnd_211017 : Nat := 48156954342180501652025

theorem tailTrace_211017 : CollatzResearch.WordTrace tailWord_211017 prefixEnd_211017 48156954342180501652025 := by
  unfold tailWord_211017
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696422276528922679511305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5130948184352615119674203 7696422276528922679511305)
  ·
    refine ⟨5772316707396692009633479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7696422276528922679511305 5772316707396692009633479)
    ·
      refine ⟨8658475061095038014450219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772316707396692009633479 8658475061095038014450219)
      ·
        refine ⟨12987712591642557021675329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658475061095038014450219 12987712591642557021675329)
        ·
          refine ⟨9740784443731917766256497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12987712591642557021675329 9740784443731917766256497)
          ·
            refine ⟨7305588332798938324692373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740784443731917766256497 7305588332798938324692373)
            ·
              refine ⟨342449453099950233969955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7305588332798938324692373 342449453099950233969955)
              ·
                refine ⟨513674179649925350954933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342449453099950233969955 513674179649925350954933)
                ·
                  refine ⟨48156954342180501652025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 513674179649925350954933 48156954342180501652025)
                  ·
                    rfl

theorem cell21_211017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_211017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211017 prefixEnd_211017 := by exact prefixLift 211017
  have htrace : WordTrace (prefixWord ++ tailWord_211017) baseStart_211017 baseEnd_211017 := by
    simpa [prefixWord, tailWord_211017, baseEnd_211017] using wordTrace_append hprefix tailTrace_211017
  have hstable : (prefixWord ++ tailWord_211017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211017).length < 2 ^ (prefixWord ++ tailWord_211017).sum := by decide
  have hdescent : baseEnd_211017 < baseStart_211017 := by decide
  rcases family_descends (prefixWord ++ tailWord_211017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211037 : List Nat := [1, 4, 4, 1, 1, 3, 2, 5]
def baseStart_211037 : Nat := 118140960795 + 211037 * 2 ^ 59
def prefixEnd_211037 : Nat := 4983230072969 + 3 ^ 40 * 211037 * 2
def baseEnd_211037 : Nat := 16053839538221637106217

theorem tailTrace_211037 : CollatzResearch.WordTrace tailWord_211037 prefixEnd_211037 16053839538221637106217 := by
  unfold tailWord_211037
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697151736456466095239365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5131434490970977396826243 7697151736456466095239365)
  ·
    refine ⟨1443215950585587392857381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7697151736456466095239365 1443215950585587392857381)
    ·
      refine ⟨270602990734797636160759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1443215950585587392857381 270602990734797636160759)
      ·
        refine ⟨405904486102196454241139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270602990734797636160759 405904486102196454241139)
        ·
          refine ⟨608856729153294681361709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405904486102196454241139 608856729153294681361709)
          ·
            refine ⟨228321273432485505510641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608856729153294681361709 228321273432485505510641)
            ·
              refine ⟨171240955074364129132981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228321273432485505510641 171240955074364129132981)
              ·
                refine ⟨16053839538221637106217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171240955074364129132981 16053839538221637106217)
                ·
                  rfl

theorem cell21_211037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 5].length) (baseStart_211037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211037 prefixEnd_211037 := by exact prefixLift 211037
  have htrace : WordTrace (prefixWord ++ tailWord_211037) baseStart_211037 baseEnd_211037 := by
    simpa [prefixWord, tailWord_211037, baseEnd_211037] using wordTrace_append hprefix tailTrace_211037
  have hstable : (prefixWord ++ tailWord_211037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211037).length < 2 ^ (prefixWord ++ tailWord_211037).sum := by decide
  have hdescent : baseEnd_211037 < baseStart_211037 := by decide
  rcases family_descends (prefixWord ++ tailWord_211037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211082 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_211082 : Nat := 118140960795 + 211082 * 2 ^ 59
def prefixEnd_211082 : Nat := 4983230072969 + 3 ^ 40 * 211082 * 2
def baseEnd_211082 : Nat := 48171788227754833068559

theorem tailTrace_211082 : CollatzResearch.WordTrace tailWord_211082 prefixEnd_211082 48171788227754833068559 := by
  unfold tailWord_211082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924698255323359695156875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5132528680862292520418333 1924698255323359695156875)
  ·
    refine ⟨2887047382985039542735313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1924698255323359695156875 2887047382985039542735313)
    ·
      refine ⟨2165285537238779657051485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2887047382985039542735313 2165285537238779657051485)
      ·
        refine ⟨811982076464542371394307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2165285537238779657051485 811982076464542371394307)
        ·
          refine ⟨1217973114696813557091461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811982076464542371394307 1217973114696813557091461)
          ·
            refine ⟨228369959005652541954649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1217973114696813557091461 228369959005652541954649)
            ·
              refine ⟨171277469254239406465987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228369959005652541954649 171277469254239406465987)
              ·
                refine ⟨256916203881359109698981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171277469254239406465987 256916203881359109698981)
                ·
                  refine ⟨48171788227754833068559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256916203881359109698981 48171788227754833068559)
                  ·
                    rfl

theorem cell21_211082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_211082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211082 prefixEnd_211082 := by exact prefixLift 211082
  have htrace : WordTrace (prefixWord ++ tailWord_211082) baseStart_211082 baseEnd_211082 := by
    simpa [prefixWord, tailWord_211082, baseEnd_211082] using wordTrace_append hprefix tailTrace_211082
  have hstable : (prefixWord ++ tailWord_211082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211082).length < 2 ^ (prefixWord ++ tailWord_211082).sum := by decide
  have hdescent : baseEnd_211082 < baseStart_211082 := by decide
  rcases family_descends (prefixWord ++ tailWord_211082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211127 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 3]
def baseStart_211127 : Nat := 118140960795 + 211127 * 2 ^ 59
def prefixEnd_211127 : Nat := 4983230072969 + 3 ^ 40 * 211127 * 2
def baseEnd_211127 : Nat := 48182057840844754818467

theorem tailTrace_211127 : CollatzResearch.WordTrace tailWord_211127 prefixEnd_211127 48182057840844754818467 := by
  unfold tailWord_211127
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700434306130411466015635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5133622870753607644010423 7700434306130411466015635)
  ·
    refine ⟨11550651459195617199023453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7700434306130411466015635 11550651459195617199023453)
    ·
      refine ⟨4331494297198356449633795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11550651459195617199023453 4331494297198356449633795)
      ·
        refine ⟨6497241445797534674450693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4331494297198356449633795 6497241445797534674450693)
        ·
          refine ⟨1218232771087037751459505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6497241445797534674450693 1218232771087037751459505)
          ·
            refine ⟨913674578315278313594629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218232771087037751459505 913674578315278313594629)
            ·
              refine ⟨171313983434114683798993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 913674578315278313594629 171313983434114683798993)
              ·
                refine ⟨128485487575586012849245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171313983434114683798993 128485487575586012849245)
                ·
                  refine ⟨48182057840844754818467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128485487575586012849245 48182057840844754818467)
                  ·
                    rfl

theorem cell21_211127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 3].length) (baseStart_211127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211127 prefixEnd_211127 := by exact prefixLift 211127
  have htrace : WordTrace (prefixWord ++ tailWord_211127) baseStart_211127 baseEnd_211127 := by
    simpa [prefixWord, tailWord_211127, baseEnd_211127] using wordTrace_append hprefix tailTrace_211127
  have hstable : (prefixWord ++ tailWord_211127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211127).length < 2 ^ (prefixWord ++ tailWord_211127).sum := by decide
  have hdescent : baseEnd_211127 < baseStart_211127 := by decide
  rcases family_descends (prefixWord ++ tailWord_211127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211186 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_211186 : Nat := 118140960795 + 211186 * 2 ^ 59
def prefixEnd_211186 : Nat := 4983230072969 + 3 ^ 40 * 211186 * 2
def baseEnd_211186 : Nat := 48195522444673763335013

theorem tailTrace_211186 : CollatzResearch.WordTrace tailWord_211186 prefixEnd_211186 48195522444673763335013 := by
  unfold tailWord_211186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925646553229166135603353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5135057475277776361608941 1925646553229166135603353)
  ·
    refine ⟨1444234914921874601702515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1925646553229166135603353 1444234914921874601702515)
    ·
      refine ⟨2166352372382811902553773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444234914921874601702515 2166352372382811902553773)
      ·
        refine ⟨812382139643554463457665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2166352372382811902553773 812382139643554463457665)
        ·
          refine ⟨609286604732665847593249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812382139643554463457665 609286604732665847593249)
          ·
            refine ⟨456964953549499385694937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609286604732665847593249 456964953549499385694937)
            ·
              refine ⟨342723715162124539271203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456964953549499385694937 342723715162124539271203)
              ·
                refine ⟨514085572743186808906805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342723715162124539271203 514085572743186808906805)
                ·
                  refine ⟨48195522444673763335013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 514085572743186808906805 48195522444673763335013)
                  ·
                    rfl

theorem cell21_211186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_211186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211186 prefixEnd_211186 := by exact prefixLift 211186
  have htrace : WordTrace (prefixWord ++ tailWord_211186) baseStart_211186 baseEnd_211186 := by
    simpa [prefixWord, tailWord_211186, baseEnd_211186] using wordTrace_append hprefix tailTrace_211186
  have hstable : (prefixWord ++ tailWord_211186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211186).length < 2 ^ (prefixWord ++ tailWord_211186).sum := by decide
  have hdescent : baseEnd_211186 < baseStart_211186 := by decide
  rcases family_descends (prefixWord ++ tailWord_211186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211214 : List Nat := [4, 1, 1, 2, 1, 2, 3, 7]
def baseStart_211214 : Nat := 118140960795 + 211214 * 2 ^ 59
def prefixEnd_211214 : Nat := 4983230072969 + 3 ^ 40 * 211214 * 2
def baseEnd_211214 : Nat := 16067304142050645622763

theorem tailTrace_211214 : CollatzResearch.WordTrace tailWord_211214 prefixEnd_211214 16067304142050645622763 := by
  unfold tailWord_211214
  simp only [CollatzResearch.WordTrace]
  refine ⟨962950932101903165554087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5135738304543483549621797 962950932101903165554087)
  ·
    refine ⟨1444426398152854748331131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962950932101903165554087 1444426398152854748331131)
    ·
      refine ⟨2166639597229282122496697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444426398152854748331131 2166639597229282122496697)
      ·
        refine ⟨1624979697921961591872523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2166639597229282122496697 1624979697921961591872523)
        ·
          refine ⟨2437469546882942387808785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624979697921961591872523 2437469546882942387808785)
          ·
            refine ⟨1828102160162206790856589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2437469546882942387808785 1828102160162206790856589)
            ·
              refine ⟨685538310060827546571221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828102160162206790856589 685538310060827546571221)
              ·
                refine ⟨16067304142050645622763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 685538310060827546571221 16067304142050645622763)
                ·
                  rfl

theorem cell21_211214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_211214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211214 prefixEnd_211214 := by exact prefixLift 211214
  have htrace : WordTrace (prefixWord ++ tailWord_211214) baseStart_211214 baseEnd_211214 := by
    simpa [prefixWord, tailWord_211214, baseEnd_211214] using wordTrace_append hprefix tailTrace_211214
  have hstable : (prefixWord ++ tailWord_211214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211214).length < 2 ^ (prefixWord ++ tailWord_211214).sum := by decide
  have hdescent : baseEnd_211214 < baseStart_211214 := by decide
  rcases family_descends (prefixWord ++ tailWord_211214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211296 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_211296 : Nat := 118140960795 + 211296 * 2 ^ 59
def prefixEnd_211296 : Nat := 4983230072969 + 3 ^ 40 * 211296 * 2
def baseEnd_211296 : Nat := 48220625943338016501455

theorem tailTrace_211296 : CollatzResearch.WordTrace tailWord_211296 prefixEnd_211296 48220625943338016501455 := by
  unfold tailWord_211296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853299121259076664458871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5137732161678768885945161 3853299121259076664458871)
  ·
    refine ⟨5779948681888614996688307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3853299121259076664458871 5779948681888614996688307)
    ·
      refine ⟨8669923022832922495032461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779948681888614996688307 8669923022832922495032461)
      ·
        refine ⟨3251221133562345935637173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8669923022832922495032461 3251221133562345935637173)
        ·
          refine ⟨304801981271469931465985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3251221133562345935637173 304801981271469931465985)
          ·
            refine ⟨228601485953602448599489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304801981271469931465985 228601485953602448599489)
            ·
              refine ⟨171451114465201836449617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228601485953602448599489 171451114465201836449617)
              ·
                refine ⟨128588335848901377337213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171451114465201836449617 128588335848901377337213)
                ·
                  refine ⟨48220625943338016501455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128588335848901377337213 48220625943338016501455)
                  ·
                    rfl

theorem cell21_211296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_211296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211296 prefixEnd_211296 := by exact prefixLift 211296
  have htrace : WordTrace (prefixWord ++ tailWord_211296) baseStart_211296 baseEnd_211296 := by
    simpa [prefixWord, tailWord_211296, baseEnd_211296] using wordTrace_append hprefix tailTrace_211296
  have hstable : (prefixWord ++ tailWord_211296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211296).length < 2 ^ (prefixWord ++ tailWord_211296).sum := by decide
  have hdescent : baseEnd_211296 < baseStart_211296 := by decide
  rcases family_descends (prefixWord ++ tailWord_211296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211335 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_211335 : Nat := 118140960795 + 211335 * 2 ^ 59
def prefixEnd_211335 : Nat := 4983230072969 + 3 ^ 40 * 211335 * 2
def baseEnd_211335 : Nat := 48229526274682615351375

theorem tailTrace_211335 : CollatzResearch.WordTrace tailWord_211335 prefixEnd_211335 48229526274682615351375 := by
  unfold tailWord_211335
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708020689376862989587459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5138680459584575326391639 7708020689376862989587459)
  ·
    refine ⟨11562031034065294484381189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7708020689376862989587459 11562031034065294484381189)
    ·
      refine ⟨2167880818887242715821473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11562031034065294484381189 2167880818887242715821473)
      ·
        refine ⟨1625910614165432036866105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167880818887242715821473 1625910614165432036866105)
        ·
          refine ⟨1219432960624074027649579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625910614165432036866105 1219432960624074027649579)
          ·
            refine ⟨1829149440936111041474369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219432960624074027649579 1829149440936111041474369)
            ·
              refine ⟨1371862080702083281105777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829149440936111041474369 1371862080702083281105777)
              ·
                refine ⟨1028896560526562460829333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371862080702083281105777 1028896560526562460829333)
                ·
                  refine ⟨48229526274682615351375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1028896560526562460829333 48229526274682615351375)
                  ·
                    rfl

theorem cell21_211335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_211335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211335 prefixEnd_211335 := by exact prefixLift 211335
  have htrace : WordTrace (prefixWord ++ tailWord_211335) baseStart_211335 baseEnd_211335 := by
    simpa [prefixWord, tailWord_211335, baseEnd_211335] using wordTrace_append hprefix tailTrace_211335
  have hstable : (prefixWord ++ tailWord_211335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211335).length < 2 ^ (prefixWord ++ tailWord_211335).sum := by decide
  have hdescent : baseEnd_211335 < baseStart_211335 := by decide
  rcases family_descends (prefixWord ++ tailWord_211335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211352 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_211352 : Nat := 118140960795 + 211352 * 2 ^ 59
def prefixEnd_211352 : Nat := 4983230072969 + 3 ^ 40 * 211352 * 2
def baseEnd_211352 : Nat := 48233405906294363568007

theorem tailTrace_211352 : CollatzResearch.WordTrace tailWord_211352 prefixEnd_211352 48233405906294363568007 := by
  unfold tailWord_211352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854320365157637446478155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5139093820210183261970873 3854320365157637446478155)
  ·
    refine ⟨5781480547736456169717233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3854320365157637446478155 5781480547736456169717233)
    ·
      refine ⟨4336110410802342127287925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5781480547736456169717233 4336110410802342127287925)
      ·
        refine ⟨406510351012719574433243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4336110410802342127287925 406510351012719574433243)
        ·
          refine ⟨609765526519079361649865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406510351012719574433243 609765526519079361649865)
          ·
            refine ⟨457324144889309521237399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609765526519079361649865 457324144889309521237399)
            ·
              refine ⟨685986217333964281856099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457324144889309521237399 685986217333964281856099)
              ·
                refine ⟨1028979326000946422784149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685986217333964281856099 1028979326000946422784149)
                ·
                  refine ⟨48233405906294363568007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1028979326000946422784149 48233405906294363568007)
                  ·
                    rfl

theorem cell21_211352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_211352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211352 prefixEnd_211352 := by exact prefixLift 211352
  have htrace : WordTrace (prefixWord ++ tailWord_211352) baseStart_211352 baseEnd_211352 := by
    simpa [prefixWord, tailWord_211352, baseEnd_211352] using wordTrace_append hprefix tailTrace_211352
  have hstable : (prefixWord ++ tailWord_211352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211352).length < 2 ^ (prefixWord ++ tailWord_211352).sum := by decide
  have hdescent : baseEnd_211352 < baseStart_211352 := by decide
  rcases family_descends (prefixWord ++ tailWord_211352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211383 : List Nat := [1, 1, 3, 1, 3, 5, 2, 5]
def baseStart_211383 : Nat := 118140960795 + 211383 * 2 ^ 59
def prefixEnd_211383 : Nat := 4983230072969 + 3 ^ 40 * 211383 * 2
def baseEnd_211383 : Nat := 16080160176215066183759

theorem tailTrace_211383 : CollatzResearch.WordTrace tailWord_211383 prefixEnd_211383 16080160176215066183759 := by
  unfold tailWord_211383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709771393202967187334803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139847595468644791556535 7709771393202967187334803)
  ·
    refine ⟨11564657089804450781002205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7709771393202967187334803 11564657089804450781002205)
    ·
      refine ⟨4336746408676669042875827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11564657089804450781002205 4336746408676669042875827)
      ·
        refine ⟨6505119613015003564313741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336746408676669042875827 6505119613015003564313741)
        ·
          refine ⟨2439419854880626336617653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6505119613015003564313741 2439419854880626336617653)
          ·
            refine ⟨228695611395058719057905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2439419854880626336617653 228695611395058719057905)
            ·
              refine ⟨171521708546294039293429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228695611395058719057905 171521708546294039293429)
              ·
                refine ⟨16080160176215066183759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171521708546294039293429 16080160176215066183759)
                ·
                  rfl

theorem cell21_211383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 5].length) (baseStart_211383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211383 prefixEnd_211383 := by exact prefixLift 211383
  have htrace : WordTrace (prefixWord ++ tailWord_211383) baseStart_211383 baseEnd_211383 := by
    simpa [prefixWord, tailWord_211383, baseEnd_211383] using wordTrace_append hprefix tailTrace_211383
  have hstable : (prefixWord ++ tailWord_211383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211383).length < 2 ^ (prefixWord ++ tailWord_211383).sum := by decide
  have hdescent : baseEnd_211383 < baseStart_211383 := by decide
  rcases family_descends (prefixWord ++ tailWord_211383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211476 : List Nat := [2, 4, 3, 1, 1, 3, 1, 6]
def baseStart_211476 : Nat := 118140960795 + 211476 * 2 ^ 59
def prefixEnd_211476 : Nat := 4983230072969 + 3 ^ 40 * 211476 * 2
def baseEnd_211476 : Nat := 16087234798565901167029

theorem tailTrace_211476 : CollatzResearch.WordTrace tailWord_211476 prefixEnd_211476 16087234798565901167029 := by
  unfold tailWord_211476
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856581690933022035235141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5142108921244029380313521 3856581690933022035235141)
  ·
    refine ⟨723109067049941631606589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3856581690933022035235141 723109067049941631606589)
    ·
      refine ⟨271165900143728111852471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 723109067049941631606589 271165900143728111852471)
      ·
        refine ⟨406748850215592167778707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271165900143728111852471 406748850215592167778707)
        ·
          refine ⟨610123275323388251668061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406748850215592167778707 610123275323388251668061)
          ·
            refine ⟨228796228246270594375523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610123275323388251668061 228796228246270594375523)
            ·
              refine ⟨343194342369405891563285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228796228246270594375523 343194342369405891563285)
              ·
                refine ⟨16087234798565901167029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343194342369405891563285 16087234798565901167029)
                ·
                  rfl

theorem cell21_211476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_211476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211476 prefixEnd_211476 := by exact prefixLift 211476
  have htrace : WordTrace (prefixWord ++ tailWord_211476) baseStart_211476 baseEnd_211476 := by
    simpa [prefixWord, tailWord_211476, baseEnd_211476] using wordTrace_append hprefix tailTrace_211476
  have hstable : (prefixWord ++ tailWord_211476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211476).length < 2 ^ (prefixWord ++ tailWord_211476).sum := by decide
  have hdescent : baseEnd_211476 < baseStart_211476 := by decide
  rcases family_descends (prefixWord ++ tailWord_211476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211521 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 4]
def baseStart_211521 : Nat := 118140960795 + 211521 * 2 ^ 59
def prefixEnd_211521 : Nat := 4983230072969 + 3 ^ 40 * 211521 * 2
def baseEnd_211521 : Nat := 48271974008787625250995

theorem tailTrace_211521 : CollatzResearch.WordTrace tailWord_211521 prefixEnd_211521 48271974008787625250995 := by
  unfold tailWord_211521
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714804666703016755858417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5143203111135344503905611 7714804666703016755858417)
  ·
    refine ⟨5786103500027262566893813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7714804666703016755858417 5786103500027262566893813)
    ·
      refine ⟨542447203127555865646295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5786103500027262566893813 542447203127555865646295)
      ·
        refine ⟨813670804691333798469443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542447203127555865646295 813670804691333798469443)
        ·
          refine ⟨1220506207037000697704165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813670804691333798469443 1220506207037000697704165)
          ·
            refine ⟨228844913819437630819531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1220506207037000697704165 228844913819437630819531)
            ·
              refine ⟨343267370729156446229297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228844913819437630819531 343267370729156446229297)
              ·
                refine ⟨257450528046867334671973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343267370729156446229297 257450528046867334671973)
                ·
                  refine ⟨48271974008787625250995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257450528046867334671973 48271974008787625250995)
                  ·
                    rfl

theorem cell21_211521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_211521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211521 prefixEnd_211521 := by exact prefixLift 211521
  have htrace : WordTrace (prefixWord ++ tailWord_211521) baseStart_211521 baseEnd_211521 := by
    simpa [prefixWord, tailWord_211521, baseEnd_211521] using wordTrace_append hprefix tailTrace_211521
  have hstable : (prefixWord ++ tailWord_211521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211521).length < 2 ^ (prefixWord ++ tailWord_211521).sum := by decide
  have hdescent : baseEnd_211521 < baseStart_211521 := by decide
  rcases family_descends (prefixWord ++ tailWord_211521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211524 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_211524 : Nat := 118140960795 + 211524 * 2 ^ 59
def prefixEnd_211524 : Nat := 4983230072969 + 3 ^ 40 * 211524 * 2
def baseEnd_211524 : Nat := 48272658649660286700989

theorem tailTrace_211524 : CollatzResearch.WordTrace tailWord_211524 prefixEnd_211524 48272658649660286700989 := by
  unfold tailWord_211524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857457042846074134108813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5143276057128098845478417 3857457042846074134108813)
  ·
    refine ⟨1446546391067277800290805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3857457042846074134108813 1446546391067277800290805)
    ·
      refine ⟨135613724162557293777263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1446546391067277800290805 135613724162557293777263)
      ·
        refine ⟨203420586243835940665895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135613724162557293777263 203420586243835940665895)
        ·
          refine ⟨305130879365753910998843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203420586243835940665895 305130879365753910998843)
          ·
            refine ⟨457696319048630866498265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305130879365753910998843 457696319048630866498265)
            ·
              refine ⟨343272239286473149873699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457696319048630866498265 343272239286473149873699)
              ·
                refine ⟨514908358929709724810549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343272239286473149873699 514908358929709724810549)
                ·
                  refine ⟨48272658649660286700989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 514908358929709724810549 48272658649660286700989)
                  ·
                    rfl

theorem cell21_211524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_211524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211524 prefixEnd_211524 := by exact prefixLift 211524
  have htrace : WordTrace (prefixWord ++ tailWord_211524) baseStart_211524 baseEnd_211524 := by
    simpa [prefixWord, tailWord_211524, baseEnd_211524] using wordTrace_append hprefix tailTrace_211524
  have hstable : (prefixWord ++ tailWord_211524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211524).length < 2 ^ (prefixWord ++ tailWord_211524).sum := by decide
  have hdescent : baseEnd_211524 < baseStart_211524 := by decide
  rcases family_descends (prefixWord ++ tailWord_211524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211577 : List Nat := [1, 2, 1, 3, 3, 2, 9]
def baseStart_211577 : Nat := 118140960795 + 211577 * 2 ^ 59
def prefixEnd_211577 : Nat := 4983230072969 + 3 ^ 40 * 211577 * 2
def baseEnd_211577 : Nat := 5364972663527108035283

theorem tailTrace_211577 : CollatzResearch.WordTrace tailWord_211577 prefixEnd_211577 5364972663527108035283 := by
  unfold tailWord_211577
  simp only [CollatzResearch.WordTrace]
  refine ⟨7716847154500138319896985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5144564769666758879931323 7716847154500138319896985)
  ·
    refine ⟨5787635365875103739922739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7716847154500138319896985 5787635365875103739922739)
    ·
      refine ⟨8681453048812655609884109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787635365875103739922739 8681453048812655609884109)
      ·
        refine ⟨3255544893304745853706541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8681453048812655609884109 3255544893304745853706541)
        ·
          refine ⟨1220829334989279695139953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3255544893304745853706541 1220829334989279695139953)
          ·
            refine ⟨915622001241959771354965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220829334989279695139953 915622001241959771354965)
            ·
              refine ⟨5364972663527108035283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 915622001241959771354965 5364972663527108035283)
              ·
                rfl

theorem cell21_211577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 9].length) (baseStart_211577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211577 prefixEnd_211577 := by exact prefixLift 211577
  have htrace : WordTrace (prefixWord ++ tailWord_211577) baseStart_211577 baseEnd_211577 := by
    simpa [prefixWord, tailWord_211577, baseEnd_211577] using wordTrace_append hprefix tailTrace_211577
  have hstable : (prefixWord ++ tailWord_211577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211577).length < 2 ^ (prefixWord ++ tailWord_211577).sum := by decide
  have hdescent : baseEnd_211577 < baseStart_211577 := by decide
  rcases family_descends (prefixWord ++ tailWord_211577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211608 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_211608 : Nat := 118140960795 + 211608 * 2 ^ 59
def prefixEnd_211608 : Nat := 4983230072969 + 3 ^ 40 * 211608 * 2
def baseEnd_211608 : Nat := 48291828594094807300817

theorem tailTrace_211608 : CollatzResearch.WordTrace tailWord_211608 prefixEnd_211608 48291828594094807300817 := by
  unfold tailWord_211608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858988908693915307137739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5145318544925220409516985 3858988908693915307137739)
  ·
    refine ⟨5788483363040872960706609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3858988908693915307137739 5788483363040872960706609)
    ·
      refine ⟨4341362522280654720529957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5788483363040872960706609 4341362522280654720529957)
      ·
        refine ⟨814005472927622760099367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4341362522280654720529957 814005472927622760099367)
        ·
          refine ⟨1221008209391434140149051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814005472927622760099367 1221008209391434140149051)
          ·
            refine ⟨1831512314087151210223577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221008209391434140149051 1831512314087151210223577)
            ·
              refine ⟨1373634235565363407667683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831512314087151210223577 1373634235565363407667683)
              ·
                refine ⟨2060451353348045111501525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373634235565363407667683 2060451353348045111501525)
                ·
                  refine ⟨48291828594094807300817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2060451353348045111501525 48291828594094807300817)
                  ·
                    rfl

theorem cell21_211608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_211608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211608 prefixEnd_211608 := by exact prefixLift 211608
  have htrace : WordTrace (prefixWord ++ tailWord_211608) baseStart_211608 baseEnd_211608 := by
    simpa [prefixWord, tailWord_211608, baseEnd_211608] using wordTrace_append hprefix tailTrace_211608
  have hstable : (prefixWord ++ tailWord_211608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211608).length < 2 ^ (prefixWord ++ tailWord_211608).sum := by decide
  have hdescent : baseEnd_211608 < baseStart_211608 := by decide
  rcases family_descends (prefixWord ++ tailWord_211608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211735 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 3]
def baseStart_211735 : Nat := 118140960795 + 211735 * 2 ^ 59
def prefixEnd_211735 : Nat := 4983230072969 + 3 ^ 40 * 211735 * 2
def baseEnd_211735 : Nat := 48320811724370808683891

theorem tailTrace_211735 : CollatzResearch.WordTrace tailWord_211735 prefixEnd_211735 48320811724370808683891 := by
  unfold tailWord_211735
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722609887927731304148659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5148406591951820869432439 7722609887927731304148659)
  ·
    refine ⟨11583914831891596956222989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722609887927731304148659 11583914831891596956222989)
    ·
      refine ⟨4343968061959348858583621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11583914831891596956222989 4343968061959348858583621)
      ·
        refine ⟨814494011617377910984429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4343968061959348858583621 814494011617377910984429)
        ·
          refine ⟨305435254356516716619161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814494011617377910984429 305435254356516716619161)
          ·
            refine ⟨229076440767387537464371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305435254356516716619161 229076440767387537464371)
            ·
              refine ⟨343614661151081306196557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229076440767387537464371 343614661151081306196557)
              ·
                refine ⟨128855497931655489823709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343614661151081306196557 128855497931655489823709)
                ·
                  refine ⟨48320811724370808683891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128855497931655489823709 48320811724370808683891)
                  ·
                    rfl

theorem cell21_211735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3].length) (baseStart_211735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211735 prefixEnd_211735 := by exact prefixLift 211735
  have htrace : WordTrace (prefixWord ++ tailWord_211735) baseStart_211735 baseEnd_211735 := by
    simpa [prefixWord, tailWord_211735, baseEnd_211735] using wordTrace_append hprefix tailTrace_211735
  have hstable : (prefixWord ++ tailWord_211735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211735).length < 2 ^ (prefixWord ++ tailWord_211735).sum := by decide
  have hdescent : baseEnd_211735 < baseStart_211735 := by decide
  rcases family_descends (prefixWord ++ tailWord_211735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211746 : List Nat := [3, 3, 1, 1, 2, 4, 7]
def baseStart_211746 : Nat := 118140960795 + 211746 * 2 ^ 59
def prefixEnd_211746 : Nat := 4983230072969 + 3 ^ 40 * 211746 * 2
def baseEnd_211746 : Nat := 5369258008248581555615

theorem tailTrace_211746 : CollatzResearch.WordTrace tailWord_211746 prefixEnd_211746 5369258008248581555615 := by
  unfold tailWord_211746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930752772721970045699773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5148674060591920121866061 1930752772721970045699773)
  ·
    refine ⟨724032289770738767137415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1930752772721970045699773 724032289770738767137415)
    ·
      refine ⟨1086048434656108150706123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724032289770738767137415 1086048434656108150706123)
      ·
        refine ⟨1629072651984162226059185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086048434656108150706123 1629072651984162226059185)
        ·
          refine ⟨1221804488988121669544389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629072651984162226059185 1221804488988121669544389)
          ·
            refine ⟨229088341685272813039573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1221804488988121669544389 229088341685272813039573)
            ·
              refine ⟨5369258008248581555615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229088341685272813039573 5369258008248581555615)
              ·
                rfl

theorem cell21_211746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 7].length) (baseStart_211746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211746 prefixEnd_211746 := by exact prefixLift 211746
  have htrace : WordTrace (prefixWord ++ tailWord_211746) baseStart_211746 baseEnd_211746 := by
    simpa [prefixWord, tailWord_211746, baseEnd_211746] using wordTrace_append hprefix tailTrace_211746
  have hstable : (prefixWord ++ tailWord_211746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211746).length < 2 ^ (prefixWord ++ tailWord_211746).sum := by decide
  have hdescent : baseEnd_211746 < baseStart_211746 := by decide
  rcases family_descends (prefixWord ++ tailWord_211746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211811 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 3]
def baseStart_211811 : Nat := 118140960795 + 211811 * 2 ^ 59
def prefixEnd_211811 : Nat := 4983230072969 + 3 ^ 40 * 211811 * 2
def baseEnd_211811 : Nat := 48338155959811565417069

theorem tailTrace_211811 : CollatzResearch.WordTrace tailWord_211811 prefixEnd_211811 48338155959811565417069 := by
  unfold tailWord_211811
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725381835652396283915287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5150254557101597522610191 7725381835652396283915287)
  ·
    refine ⟨11588072753478594425872931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725381835652396283915287 11588072753478594425872931)
    ·
      refine ⟨17382109130217891638809397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588072753478594425872931 17382109130217891638809397)
      ·
        refine ⟨1629572730957927341138381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17382109130217891638809397 1629572730957927341138381)
        ·
          refine ⟨611089774109222752926893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1629572730957927341138381 611089774109222752926893)
          ·
            refine ⟨229158665290958532347585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611089774109222752926893 229158665290958532347585)
            ·
              refine ⟨171868998968218899260689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229158665290958532347585 171868998968218899260689)
              ·
                refine ⟨128901749226164174445517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171868998968218899260689 128901749226164174445517)
                ·
                  refine ⟨48338155959811565417069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128901749226164174445517 48338155959811565417069)
                  ·
                    rfl

theorem cell21_211811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 3].length) (baseStart_211811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211811 prefixEnd_211811 := by exact prefixLift 211811
  have htrace : WordTrace (prefixWord ++ tailWord_211811) baseStart_211811 baseEnd_211811 := by
    simpa [prefixWord, tailWord_211811, baseEnd_211811] using wordTrace_append hprefix tailTrace_211811
  have hstable : (prefixWord ++ tailWord_211811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211811).length < 2 ^ (prefixWord ++ tailWord_211811).sum := by decide
  have hdescent : baseEnd_211811 < baseStart_211811 := by decide
  rcases family_descends (prefixWord ++ tailWord_211811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211929 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 5]
def baseStart_211929 : Nat := 118140960795 + 211929 * 2 ^ 59
def prefixEnd_211929 : Nat := 4983230072969 + 3 ^ 40 * 211929 * 2
def baseEnd_211929 : Nat := 48365085167469582450161

theorem tailTrace_211929 : CollatzResearch.WordTrace tailWord_211929 prefixEnd_211929 48365085167469582450161 := by
  unfold tailWord_211929
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729685649224902436710841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5153123766149934957807227 7729685649224902436710841)
  ·
    refine ⟨5797264236918676827533131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7729685649224902436710841 5797264236918676827533131)
    ·
      refine ⟨8695896355378015241299697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5797264236918676827533131 8695896355378015241299697)
      ·
        refine ⟨6521922266533511430974773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8695896355378015241299697 6521922266533511430974773)
        ·
          refine ⟨611430212487516696653885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6521922266533511430974773 611430212487516696653885)
          ·
            refine ⟨229286329682818761245207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611430212487516696653885 229286329682818761245207)
            ·
              refine ⟨343929494524228141867811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229286329682818761245207 343929494524228141867811)
              ·
                refine ⟨515894241786342212801717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343929494524228141867811 515894241786342212801717)
                ·
                  refine ⟨48365085167469582450161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 515894241786342212801717 48365085167469582450161)
                  ·
                    rfl

theorem cell21_211929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_211929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_211929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_211929 prefixEnd_211929 := by exact prefixLift 211929
  have htrace : WordTrace (prefixWord ++ tailWord_211929) baseStart_211929 baseEnd_211929 := by
    simpa [prefixWord, tailWord_211929, baseEnd_211929] using wordTrace_append hprefix tailTrace_211929
  have hstable : (prefixWord ++ tailWord_211929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211929).length < 2 ^ (prefixWord ++ tailWord_211929).sum := by decide
  have hdescent : baseEnd_211929 < baseStart_211929 := by decide
  rcases family_descends (prefixWord ++ tailWord_211929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212022 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_212022 : Nat := 118140960795 + 212022 * 2 ^ 59
def prefixEnd_212022 : Nat := 4983230072969 + 3 ^ 40 * 212022 * 2
def baseEnd_212022 : Nat := 48386309034522087399971

theorem tailTrace_212022 : CollatzResearch.WordTrace tailWord_212022 prefixEnd_212022 48386309034522087399971 := by
  unfold tailWord_212022
  simp only [CollatzResearch.WordTrace]
  refine ⟨483317352367998707490395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5155385091925319546564213 483317352367998707490395)
  ·
    refine ⟨724976028551998061235593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 483317352367998707490395 724976028551998061235593)
    ·
      refine ⟨543732021413998545926695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 724976028551998061235593 543732021413998545926695)
      ·
        refine ⟨815598032120997818890043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543732021413998545926695 815598032120997818890043)
        ·
          refine ⟨1223397048181496728335065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815598032120997818890043 1223397048181496728335065)
          ·
            refine ⟨917547786136122546251299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223397048181496728335065 917547786136122546251299)
            ·
              refine ⟨1376321679204183819376949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917547786136122546251299 1376321679204183819376949)
              ·
                refine ⟨129030157425392233066589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376321679204183819376949 129030157425392233066589)
                ·
                  refine ⟨48386309034522087399971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129030157425392233066589 48386309034522087399971)
                  ·
                    rfl

theorem cell21_212022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_212022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212022 prefixEnd_212022 := by exact prefixLift 212022
  have htrace : WordTrace (prefixWord ++ tailWord_212022) baseStart_212022 baseEnd_212022 := by
    simpa [prefixWord, tailWord_212022, baseEnd_212022] using wordTrace_append hprefix tailTrace_212022
  have hstable : (prefixWord ++ tailWord_212022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212022).length < 2 ^ (prefixWord ++ tailWord_212022).sum := by decide
  have hdescent : baseEnd_212022 < baseStart_212022 := by decide
  rcases family_descends (prefixWord ++ tailWord_212022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212126 : List Nat := [4, 3, 1, 1, 2, 1, 2, 7]
def baseStart_212126 : Nat := 118140960795 + 212126 * 2 ^ 59
def prefixEnd_212126 : Nat := 4983230072969 + 3 ^ 40 * 212126 * 2
def baseEnd_212126 : Nat := 16136681083813672555475

theorem tailTrace_212126 : CollatzResearch.WordTrace tailWord_212126 prefixEnd_212126 16136681083813672555475 := by
  unfold tailWord_212126
  simp only [CollatzResearch.WordTrace]
  refine ⟨967108853688900635204029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5157913886340803387754821 967108853688900635204029)
  ·
    refine ⟨362665820133337738201511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 967108853688900635204029 362665820133337738201511)
    ·
      refine ⟨543998730200006607302267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362665820133337738201511 543998730200006607302267)
      ·
        refine ⟨815998095300009910953401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543998730200006607302267 815998095300009910953401)
        ·
          refine ⟨611998571475007433215051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815998095300009910953401 611998571475007433215051)
          ·
            refine ⟨917997857212511149822577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611998571475007433215051 917997857212511149822577)
            ·
              refine ⟨688498392909383362366933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917997857212511149822577 688498392909383362366933)
              ·
                refine ⟨16136681083813672555475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 688498392909383362366933 16136681083813672555475)
                ·
                  rfl

theorem cell21_212126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_212126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212126 prefixEnd_212126 := by exact prefixLift 212126
  have htrace : WordTrace (prefixWord ++ tailWord_212126) baseStart_212126 baseEnd_212126 := by
    simpa [prefixWord, tailWord_212126, baseEnd_212126] using wordTrace_append hprefix tailTrace_212126
  have hstable : (prefixWord ++ tailWord_212126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212126).length < 2 ^ (prefixWord ++ tailWord_212126).sum := by decide
  have hdescent : baseEnd_212126 < baseStart_212126 := by decide
  rcases family_descends (prefixWord ++ tailWord_212126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212250 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_212250 : Nat := 118140960795 + 212250 * 2 ^ 59
def prefixEnd_212250 : Nat := 4983230072969 + 3 ^ 40 * 212250 * 2
def baseEnd_212250 : Nat := 48438341740844357599505

theorem tailTrace_212250 : CollatzResearch.WordTrace tailWord_212250 prefixEnd_212250 48438341740844357599505 := by
  unfold tailWord_212250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935348370265493564786551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5160928987374649506097469 1935348370265493564786551)
  ·
    refine ⟨2903022555398240347179827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935348370265493564786551 2903022555398240347179827)
    ·
      refine ⟨4354533833097360520769741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903022555398240347179827 4354533833097360520769741)
      ·
        refine ⟨1632950187411510195288653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4354533833097360520769741 1632950187411510195288653)
        ·
          refine ⟨612356320279316323233245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1632950187411510195288653 612356320279316323233245)
          ·
            refine ⟨229633620104743621212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612356320279316323233245 229633620104743621212467)
            ·
              refine ⟨344450430157115431818701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229633620104743621212467 344450430157115431818701)
              ·
                refine ⟨129168911308918286932013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344450430157115431818701 129168911308918286932013)
                ·
                  refine ⟨48438341740844357599505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129168911308918286932013 48438341740844357599505)
                  ·
                    rfl

theorem cell21_212250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_212250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212250 prefixEnd_212250 := by exact prefixLift 212250
  have htrace : WordTrace (prefixWord ++ tailWord_212250) baseStart_212250 baseEnd_212250 := by
    simpa [prefixWord, tailWord_212250, baseEnd_212250] using wordTrace_append hprefix tailTrace_212250
  have hstable : (prefixWord ++ tailWord_212250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212250).length < 2 ^ (prefixWord ++ tailWord_212250).sum := by decide
  have hdescent : baseEnd_212250 < baseStart_212250 := by decide
  rcases family_descends (prefixWord ++ tailWord_212250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212261 : List Nat := [1, 3, 1, 2, 4, 3, 7]
def baseStart_212261 : Nat := 118140960795 + 212261 * 2 ^ 59
def prefixEnd_212261 : Nat := 4983230072969 + 3 ^ 40 * 212261 * 2
def baseEnd_212261 : Nat := 5382316898967864768461

theorem tailTrace_212261 : CollatzResearch.WordTrace tailWord_212261 prefixEnd_212261 5382316898967864768461 := by
  unfold tailWord_212261
  simp only [CollatzResearch.WordTrace]
  refine ⟨7741794684022123137796637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5161196456014748758531091 7741794684022123137796637)
  ·
    refine ⟨2903173006508296176673739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7741794684022123137796637 2903173006508296176673739)
    ·
      refine ⟨4354759509762444265010609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903173006508296176673739 4354759509762444265010609)
      ·
        refine ⟨3266069632321833198757957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354759509762444265010609 3266069632321833198757957)
        ·
          refine ⟨612388056060343724767117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3266069632321833198757957 612388056060343724767117)
          ·
            refine ⟨229645521022628896787669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612388056060343724767117 229645521022628896787669)
            ·
              refine ⟨5382316898967864768461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229645521022628896787669 5382316898967864768461)
              ·
                rfl

theorem cell21_212261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 7].length) (baseStart_212261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212261 prefixEnd_212261 := by exact prefixLift 212261
  have htrace : WordTrace (prefixWord ++ tailWord_212261) baseStart_212261 baseEnd_212261 := by
    simpa [prefixWord, tailWord_212261, baseEnd_212261] using wordTrace_append hprefix tailTrace_212261
  have hstable : (prefixWord ++ tailWord_212261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212261).length < 2 ^ (prefixWord ++ tailWord_212261).sum := by decide
  have hdescent : baseEnd_212261 < baseStart_212261 := by decide
  rcases family_descends (prefixWord ++ tailWord_212261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212281 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 4]
def baseStart_212281 : Nat := 118140960795 + 212281 * 2 ^ 59
def prefixEnd_212281 : Nat := 4983230072969 + 3 ^ 40 * 212281 * 2
def baseEnd_212281 : Nat := 48445416363195192582775

theorem tailTrace_212281 : CollatzResearch.WordTrace tailWord_212281 prefixEnd_212281 48445416363195192582775 := by
  unfold tailWord_212281
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742524143949666553524697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5161682762633111035683131 7742524143949666553524697)
  ·
    refine ⟨5806893107962249915143523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7742524143949666553524697 5806893107962249915143523)
    ·
      refine ⟨8710339661943374872715285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806893107962249915143523 8710339661943374872715285)
      ·
        refine ⟨408297171653595697158529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8710339661943374872715285 408297171653595697158529)
        ·
          refine ⟨306222878740196772868897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408297171653595697158529 306222878740196772868897)
          ·
            refine ⟨229667159055147579651673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306222878740196772868897 229667159055147579651673)
            ·
              refine ⟨172250369291360684738755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229667159055147579651673 172250369291360684738755)
              ·
                refine ⟨258375553937041027108133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172250369291360684738755 258375553937041027108133)
                ·
                  refine ⟨48445416363195192582775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258375553937041027108133 48445416363195192582775)
                  ·
                    rfl

theorem cell21_212281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_212281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212281 prefixEnd_212281 := by exact prefixLift 212281
  have htrace : WordTrace (prefixWord ++ tailWord_212281) baseStart_212281 baseEnd_212281 := by
    simpa [prefixWord, tailWord_212281, baseEnd_212281] using wordTrace_append hprefix tailTrace_212281
  have hstable : (prefixWord ++ tailWord_212281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212281).length < 2 ^ (prefixWord ++ tailWord_212281).sum := by decide
  have hdescent : baseEnd_212281 < baseStart_212281 := by decide
  rcases family_descends (prefixWord ++ tailWord_212281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212320 : List Nat := [2, 1, 1, 3, 4, 10]
def baseStart_212320 : Nat := 118140960795 + 212320 * 2 ^ 59
def prefixEnd_212320 : Nat := 4983230072969 + 3 ^ 40 * 212320 * 2
def baseEnd_212320 : Nat := 1794604322019992275285

theorem tailTrace_212320 : CollatzResearch.WordTrace tailWord_212320 prefixEnd_212320 1794604322019992275285 := by
  unfold tailWord_212320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871973295404188107097207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5162631060538917476129609 3871973295404188107097207)
  ·
    refine ⟨5807959943106282160645811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871973295404188107097207 5807959943106282160645811)
    ·
      refine ⟨8711939914659423240968717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807959943106282160645811 8711939914659423240968717)
      ·
        refine ⟨3266977467997283715363269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8711939914659423240968717 3266977467997283715363269)
        ·
          refine ⟨612558275249490696630613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3266977467997283715363269 612558275249490696630613)
          ·
            refine ⟨1794604322019992275285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 612558275249490696630613 1794604322019992275285)
            ·
              rfl

theorem cell21_212320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 10].length) (baseStart_212320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212320 prefixEnd_212320 := by exact prefixLift 212320
  have htrace : WordTrace (prefixWord ++ tailWord_212320) baseStart_212320 baseEnd_212320 := by
    simpa [prefixWord, tailWord_212320, baseEnd_212320] using wordTrace_append hprefix tailTrace_212320
  have hstable : (prefixWord ++ tailWord_212320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212320).length < 2 ^ (prefixWord ++ tailWord_212320).sum := by decide
  have hdescent : baseEnd_212320 < baseStart_212320 := by decide
  rcases family_descends (prefixWord ++ tailWord_212320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212323 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_212323 : Nat := 118140960795 + 212323 * 2 ^ 59
def prefixEnd_212323 : Nat := 4983230072969 + 3 ^ 40 * 212323 * 2
def baseEnd_212323 : Nat := 48455001335412452882689

theorem tailTrace_212323 : CollatzResearch.WordTrace tailWord_212323 prefixEnd_212323 48455001335412452882689 := by
  unfold tailWord_212323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744056009797507726553623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5162704006531671817702415 7744056009797507726553623)
  ·
    refine ⟨11616084014696261589830435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7744056009797507726553623 11616084014696261589830435)
    ·
      refine ⟨17424126022044392384745653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11616084014696261589830435 17424126022044392384745653)
      ·
        refine ⟨1633511814566661786069905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17424126022044392384745653 1633511814566661786069905)
        ·
          refine ⟨1225133860924996339552429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633511814566661786069905 1225133860924996339552429)
          ·
            refine ⟨459425197846873627332161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225133860924996339552429 459425197846873627332161)
            ·
              refine ⟨344568898385155220499121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459425197846873627332161 344568898385155220499121)
              ·
                refine ⟨258426673788866415374341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344568898385155220499121 258426673788866415374341)
                ·
                  refine ⟨48455001335412452882689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258426673788866415374341 48455001335412452882689)
                  ·
                    rfl

theorem cell21_212323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_212323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212323 prefixEnd_212323 := by exact prefixLift 212323
  have htrace : WordTrace (prefixWord ++ tailWord_212323) baseStart_212323 baseEnd_212323 := by
    simpa [prefixWord, tailWord_212323, baseEnd_212323] using wordTrace_append hprefix tailTrace_212323
  have hstable : (prefixWord ++ tailWord_212323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212323).length < 2 ^ (prefixWord ++ tailWord_212323).sum := by decide
  have hdescent : baseEnd_212323 < baseStart_212323 := by decide
  rcases family_descends (prefixWord ++ tailWord_212323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212472 : List Nat := [2, 1, 2, 1, 1, 5, 2, 7]
def baseStart_212472 : Nat := 118140960795 + 212472 * 2 ^ 59
def prefixEnd_212472 : Nat := 4983230072969 + 3 ^ 40 * 212472 * 2
def baseEnd_212472 : Nat := 16163001721807101633017

theorem tailTrace_212472 : CollatzResearch.WordTrace tailWord_212472 prefixEnd_212472 16163001721807101633017 := by
  unfold tailWord_212472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874745243128853086863835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5166326990838470782485113 3874745243128853086863835)
  ·
    refine ⟨5812117864693279630295753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874745243128853086863835 5812117864693279630295753)
    ·
      refine ⟨4359088398519959722721815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5812117864693279630295753 4359088398519959722721815)
      ·
        refine ⟨6538632597779939584082723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359088398519959722721815 6538632597779939584082723)
        ·
          refine ⟨9807948896669909376124085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538632597779939584082723 9807948896669909376124085)
          ·
            refine ⟨919495209062804004011633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9807948896669909376124085 919495209062804004011633)
            ·
              refine ⟨689621406797103003008725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919495209062804004011633 689621406797103003008725)
              ·
                refine ⟨16163001721807101633017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 689621406797103003008725 16163001721807101633017)
                ·
                  rfl

theorem cell21_212472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_212472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212472 prefixEnd_212472 := by exact prefixLift 212472
  have htrace : WordTrace (prefixWord ++ tailWord_212472) baseStart_212472 baseEnd_212472 := by
    simpa [prefixWord, tailWord_212472, baseEnd_212472] using wordTrace_append hprefix tailTrace_212472
  have hstable : (prefixWord ++ tailWord_212472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212472).length < 2 ^ (prefixWord ++ tailWord_212472).sum := by decide
  have hdescent : baseEnd_212472 < baseStart_212472 := by decide
  rcases family_descends (prefixWord ++ tailWord_212472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212517 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_212517 : Nat := 118140960795 + 212517 * 2 ^ 59
def prefixEnd_212517 : Nat := 4983230072969 + 3 ^ 40 * 212517 * 2
def baseEnd_212517 : Nat := 48499274778511226648959

theorem tailTrace_212517 : CollatzResearch.WordTrace tailWord_212517 prefixEnd_212517 48499274778511226648959 := by
  unfold tailWord_212517
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751131771094678859115805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5167421180729785906077203 7751131771094678859115805)
  ·
    refine ⟨2906674414160504572168427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7751131771094678859115805 2906674414160504572168427)
    ·
      refine ⟨4360011621240756858252641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2906674414160504572168427 4360011621240756858252641)
      ·
        refine ⟨3270008715930567643689481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4360011621240756858252641 3270008715930567643689481)
        ·
          refine ⟨2452506536947925732767111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3270008715930567643689481 2452506536947925732767111)
          ·
            refine ⟨3678759805421888599150667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452506536947925732767111 3678759805421888599150667)
            ·
              refine ⟨5518139708132832898726001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678759805421888599150667 5518139708132832898726001)
              ·
                refine ⟨4138604781099624674044501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518139708132832898726001 4138604781099624674044501)
                ·
                  refine ⟨48499274778511226648959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4138604781099624674044501 48499274778511226648959)
                  ·
                    rfl

theorem cell21_212517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_212517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212517 prefixEnd_212517 := by exact prefixLift 212517
  have htrace : WordTrace (prefixWord ++ tailWord_212517) baseStart_212517 baseEnd_212517 := by
    simpa [prefixWord, tailWord_212517, baseEnd_212517] using wordTrace_append hprefix tailTrace_212517
  have hstable : (prefixWord ++ tailWord_212517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212517).length < 2 ^ (prefixWord ++ tailWord_212517).sum := by decide
  have hdescent : baseEnd_212517 < baseStart_212517 := by decide
  rcases family_descends (prefixWord ++ tailWord_212517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212537 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 3]
def baseStart_212537 : Nat := 118140960795 + 212537 * 2 ^ 59
def prefixEnd_212537 : Nat := 4983230072969 + 3 ^ 40 * 212537 * 2
def baseEnd_212537 : Nat := 48503839050995636315585

theorem tailTrace_212537 : CollatzResearch.WordTrace tailWord_212537 prefixEnd_212537 48503839050995636315585 := by
  unfold tailWord_212537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751861231022222274843865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5167907487348148183229243 7751861231022222274843865)
  ·
    refine ⟨5813895923266666706132899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7751861231022222274843865 5813895923266666706132899)
    ·
      refine ⟨8720843884900000059199349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813895923266666706132899 8720843884900000059199349)
      ·
        refine ⟨817579114209375005549939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8720843884900000059199349 817579114209375005549939)
        ·
          refine ⟨1226368671314062508324909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817579114209375005549939 1226368671314062508324909)
          ·
            refine ⟨459888251742773440621841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1226368671314062508324909 459888251742773440621841)
            ·
              refine ⟨344916188807080080466381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459888251742773440621841 344916188807080080466381)
              ·
                refine ⟨129343570802655030174893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344916188807080080466381 129343570802655030174893)
                ·
                  refine ⟨48503839050995636315585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129343570802655030174893 48503839050995636315585)
                  ·
                    rfl

theorem cell21_212537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 3].length) (baseStart_212537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212537 prefixEnd_212537 := by exact prefixLift 212537
  have htrace : WordTrace (prefixWord ++ tailWord_212537) baseStart_212537 baseEnd_212537 := by
    simpa [prefixWord, tailWord_212537, baseEnd_212537] using wordTrace_append hprefix tailTrace_212537
  have hstable : (prefixWord ++ tailWord_212537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212537).length < 2 ^ (prefixWord ++ tailWord_212537).sum := by decide
  have hdescent : baseEnd_212537 < baseStart_212537 := by decide
  rcases family_descends (prefixWord ++ tailWord_212537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212579 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_212579 : Nat := 118140960795 + 212579 * 2 ^ 59
def prefixEnd_212579 : Nat := 4983230072969 + 3 ^ 40 * 212579 * 2
def baseEnd_212579 : Nat := 48513424023212896615499

theorem tailTrace_212579 : CollatzResearch.WordTrace tailWord_212579 prefixEnd_212579 48513424023212896615499 := by
  unfold tailWord_212579
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753393096870063447872791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5168928731246708965248527 7753393096870063447872791)
  ·
    refine ⟨11630089645305095171809187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7753393096870063447872791 11630089645305095171809187)
    ·
      refine ⟨17445134467957642757713781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11630089645305095171809187 17445134467957642757713781)
      ·
        refine ⟨1635481356371029008535667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17445134467957642757713781 1635481356371029008535667)
        ·
          refine ⟨2453222034556543512803501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635481356371029008535667 2453222034556543512803501)
          ·
            refine ⟨919958262958703817301313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2453222034556543512803501 919958262958703817301313)
            ·
              refine ⟨689968697219027862975985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919958262958703817301313 689968697219027862975985)
              ·
                refine ⟨517476522914270897231989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689968697219027862975985 517476522914270897231989)
                ·
                  refine ⟨48513424023212896615499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517476522914270897231989 48513424023212896615499)
                  ·
                    rfl

theorem cell21_212579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_212579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212579 prefixEnd_212579 := by exact prefixLift 212579
  have htrace : WordTrace (prefixWord ++ tailWord_212579) baseStart_212579 baseEnd_212579 := by
    simpa [prefixWord, tailWord_212579, baseEnd_212579] using wordTrace_append hprefix tailTrace_212579
  have hstable : (prefixWord ++ tailWord_212579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212579).length < 2 ^ (prefixWord ++ tailWord_212579).sum := by decide
  have hdescent : baseEnd_212579 < baseStart_212579 := by decide
  rcases family_descends (prefixWord ++ tailWord_212579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212613 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 3]
def baseStart_212613 : Nat := 118140960795 + 212613 * 2 ^ 59
def prefixEnd_212613 : Nat := 4983230072969 + 3 ^ 40 * 212613 * 2
def baseEnd_212613 : Nat := 48521183286436393048763

theorem tailTrace_212613 : CollatzResearch.WordTrace tailWord_212613 prefixEnd_212613 48521183286436393048763 := by
  unfold tailWord_212613
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754633178746887254610493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5169755452497924836406995 7754633178746887254610493)
  ·
    refine ⟨2907987442030082720478935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7754633178746887254610493 2907987442030082720478935)
    ·
      refine ⟨4361981163045124080718403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907987442030082720478935 4361981163045124080718403)
      ·
        refine ⟨6542971744567686121077605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361981163045124080718403 6542971744567686121077605)
        ·
          refine ⟨1226807202106441147702051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6542971744567686121077605 1226807202106441147702051)
          ·
            refine ⟨1840210803159661721553077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226807202106441147702051 1840210803159661721553077)
            ·
              refine ⟨172519762796218286395601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1840210803159661721553077 172519762796218286395601)
              ·
                refine ⟨129389822097163714796701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172519762796218286395601 129389822097163714796701)
                ·
                  refine ⟨48521183286436393048763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129389822097163714796701 48521183286436393048763)
                  ·
                    rfl

theorem cell21_212613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_212613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212613 prefixEnd_212613 := by exact prefixLift 212613
  have htrace : WordTrace (prefixWord ++ tailWord_212613) baseStart_212613 baseEnd_212613 := by
    simpa [prefixWord, tailWord_212613, baseEnd_212613] using wordTrace_append hprefix tailTrace_212613
  have hstable : (prefixWord ++ tailWord_212613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212613).length < 2 ^ (prefixWord ++ tailWord_212613).sum := by decide
  have hdescent : baseEnd_212613 < baseStart_212613 := by decide
  rcases family_descends (prefixWord ++ tailWord_212613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212672 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_212672 : Nat := 118140960795 + 212672 * 2 ^ 59
def prefixEnd_212672 : Nat := 4983230072969 + 3 ^ 40 * 212672 * 2
def baseEnd_212672 : Nat := 48534647890265401565309

theorem tailTrace_212672 : CollatzResearch.WordTrace tailWord_212672 prefixEnd_212672 48534647890265401565309 := by
  unfold tailWord_212672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878392542766570165504135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5171190057022093554005513 3878392542766570165504135)
  ·
    refine ⟨5817588814149855248256203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3878392542766570165504135 5817588814149855248256203)
    ·
      refine ⟨8726383221224782872384305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817588814149855248256203 8726383221224782872384305)
      ·
        refine ⟨6544787415918587154288229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726383221224782872384305 6544787415918587154288229)
        ·
          refine ⟨1227147640484735091429043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6544787415918587154288229 1227147640484735091429043)
          ·
            refine ⟨1840721460727102637143565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227147640484735091429043 1840721460727102637143565)
            ·
              refine ⟨690270547772663488928837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1840721460727102637143565 690270547772663488928837)
              ·
                refine ⟨129425727707374404174157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690270547772663488928837 129425727707374404174157)
                ·
                  refine ⟨48534647890265401565309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129425727707374404174157 48534647890265401565309)
                  ·
                    rfl

theorem cell21_212672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_212672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212672 prefixEnd_212672 := by exact prefixLift 212672
  have htrace : WordTrace (prefixWord ++ tailWord_212672) baseStart_212672 baseEnd_212672 := by
    simpa [prefixWord, tailWord_212672, baseEnd_212672] using wordTrace_append hprefix tailTrace_212672
  have hstable : (prefixWord ++ tailWord_212672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212672).length < 2 ^ (prefixWord ++ tailWord_212672).sum := by decide
  have hdescent : baseEnd_212672 < baseStart_212672 := by decide
  rcases family_descends (prefixWord ++ tailWord_212672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212686 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_212686 : Nat := 118140960795 + 212686 * 2 ^ 59
def prefixEnd_212686 : Nat := 4983230072969 + 3 ^ 40 * 212686 * 2
def baseEnd_212686 : Nat := 48537842881004488331947

theorem tailTrace_212686 : CollatzResearch.WordTrace tailWord_212686 prefixEnd_212686 48537842881004488331947 := by
  unfold tailWord_212686
  simp only [CollatzResearch.WordTrace]
  refine ⟨969661963435302590252239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5171530471654947148011941 969661963435302590252239)
  ·
    refine ⟨1454492945152953885378359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969661963435302590252239 1454492945152953885378359)
    ·
      refine ⟨2181739417729430828067539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454492945152953885378359 2181739417729430828067539)
      ·
        refine ⟨3272609126594146242101309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181739417729430828067539 3272609126594146242101309)
        ·
          refine ⟨1227228422472804840787991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3272609126594146242101309 1227228422472804840787991)
          ·
            refine ⟨1840842633709207261181987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227228422472804840787991 1840842633709207261181987)
            ·
              refine ⟨2761263950563810891772981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840842633709207261181987 2761263950563810891772981)
              ·
                refine ⟨258868495365357271103717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2761263950563810891772981 258868495365357271103717)
                ·
                  refine ⟨48537842881004488331947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258868495365357271103717 48537842881004488331947)
                  ·
                    rfl

theorem cell21_212686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_212686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212686 prefixEnd_212686 := by exact prefixLift 212686
  have htrace : WordTrace (prefixWord ++ tailWord_212686) baseStart_212686 baseEnd_212686 := by
    simpa [prefixWord, tailWord_212686, baseEnd_212686] using wordTrace_append hprefix tailTrace_212686
  have hstable : (prefixWord ++ tailWord_212686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212686).length < 2 ^ (prefixWord ++ tailWord_212686).sum := by decide
  have hdescent : baseEnd_212686 < baseStart_212686 := by decide
  rcases family_descends (prefixWord ++ tailWord_212686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212776 : List Nat := [2, 1, 5, 1, 1, 2, 9]
def baseStart_212776 : Nat := 118140960795 + 212776 * 2 ^ 59
def prefixEnd_212776 : Nat := 4983230072969 + 3 ^ 40 * 212776 * 2
def baseEnd_212776 : Nat := 5395375789687147981307

theorem tailTrace_212776 : CollatzResearch.WordTrace tailWord_212776 prefixEnd_212776 5395375789687147981307 := by
  unfold tailWord_212776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880289138578183046397091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5173718851437577395196121 3880289138578183046397091)
  ·
    refine ⟨5820433707867274569595637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3880289138578183046397091 5820433707867274569595637)
    ·
      refine ⟨545665660112556990899591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5820433707867274569595637 545665660112556990899591)
      ·
        refine ⟨818498490168835486349387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545665660112556990899591 818498490168835486349387)
        ·
          refine ⟨1227747735253253229524081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818498490168835486349387 1227747735253253229524081)
          ·
            refine ⟨920810801439939922143061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227747735253253229524081 920810801439939922143061)
            ·
              refine ⟨5395375789687147981307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 920810801439939922143061 5395375789687147981307)
              ·
                rfl

theorem cell21_212776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 9].length) (baseStart_212776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212776 prefixEnd_212776 := by exact prefixLift 212776
  have htrace : WordTrace (prefixWord ++ tailWord_212776) baseStart_212776 baseEnd_212776 := by
    simpa [prefixWord, tailWord_212776, baseEnd_212776] using wordTrace_append hprefix tailTrace_212776
  have hstable : (prefixWord ++ tailWord_212776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212776).length < 2 ^ (prefixWord ++ tailWord_212776).sum := by decide
  have hdescent : baseEnd_212776 < baseStart_212776 := by decide
  rcases family_descends (prefixWord ++ tailWord_212776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212782 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_212782 : Nat := 118140960795 + 212782 * 2 ^ 59
def prefixEnd_212782 : Nat := 4983230072969 + 3 ^ 40 * 212782 * 2
def baseEnd_212782 : Nat := 48559751388929654731751

theorem tailTrace_212782 : CollatzResearch.WordTrace tailWord_212782 prefixEnd_212782 48559751388929654731751 := by
  unfold tailWord_212782
  simp only [CollatzResearch.WordTrace]
  refine ⟨970099639391828639689075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5173864743423086078341733 970099639391828639689075)
  ·
    refine ⟨1455149459087742959533613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970099639391828639689075 1455149459087742959533613)
    ·
      refine ⟨545681047157903609825105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1455149459087742959533613 545681047157903609825105)
      ·
        refine ⟨409260785368427707368829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545681047157903609825105 409260785368427707368829)
        ·
          refine ⟨153472794513160390263311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409260785368427707368829 153472794513160390263311)
          ·
            refine ⟨230209191769740585394967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153472794513160390263311 230209191769740585394967)
            ·
              refine ⟨345313787654610878092451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230209191769740585394967 345313787654610878092451)
              ·
                refine ⟨517970681481916317138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345313787654610878092451 517970681481916317138677)
                ·
                  refine ⟨48559751388929654731751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517970681481916317138677 48559751388929654731751)
                  ·
                    rfl

theorem cell21_212782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_212782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212782 prefixEnd_212782 := by exact prefixLift 212782
  have htrace : WordTrace (prefixWord ++ tailWord_212782) baseStart_212782 baseEnd_212782 := by
    simpa [prefixWord, tailWord_212782, baseEnd_212782] using wordTrace_append hprefix tailTrace_212782
  have hstable : (prefixWord ++ tailWord_212782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212782).length < 2 ^ (prefixWord ++ tailWord_212782).sum := by decide
  have hdescent : baseEnd_212782 < baseStart_212782 := by decide
  rcases family_descends (prefixWord ++ tailWord_212782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212835 : List Nat := [1, 1, 1, 5, 13]
def baseStart_212835 : Nat := 118140960795 + 212835 * 2 ^ 59
def prefixEnd_212835 : Nat := 4983230072969 + 3 ^ 40 * 212835 * 2
def baseEnd_212835 : Nat := 599652428531028893189

theorem tailTrace_212835 : CollatzResearch.WordTrace tailWord_212835 prefixEnd_212835 599652428531028893189 := by
  unfold tailWord_212835
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762730183942619169191959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5175153455961746112794639 7762730183942619169191959)
  ·
    refine ⟨11644095275913928753787939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762730183942619169191959 11644095275913928753787939)
    ·
      refine ⟨17466142913870893130681909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644095275913928753787939 17466142913870893130681909)
      ·
        refine ⟨1637450898175396231001429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17466142913870893130681909 1637450898175396231001429)
        ·
          refine ⟨599652428531028893189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1637450898175396231001429 599652428531028893189)
          ·
            rfl

theorem cell21_212835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 13].length) (baseStart_212835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212835 prefixEnd_212835 := by exact prefixLift 212835
  have htrace : WordTrace (prefixWord ++ tailWord_212835) baseStart_212835 baseEnd_212835 := by
    simpa [prefixWord, tailWord_212835, baseEnd_212835] using wordTrace_append hprefix tailTrace_212835
  have hstable : (prefixWord ++ tailWord_212835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212835).length < 2 ^ (prefixWord ++ tailWord_212835).sum := by decide
  have hdescent : baseEnd_212835 < baseStart_212835 := by decide
  rcases family_descends (prefixWord ++ tailWord_212835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212900 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_212900 : Nat := 118140960795 + 212900 * 2 ^ 59
def prefixEnd_212900 : Nat := 4983230072969 + 3 ^ 40 * 212900 * 2
def baseEnd_212900 : Nat := 48586680596587671764843

theorem tailTrace_212900 : CollatzResearch.WordTrace tailWord_212900 prefixEnd_212900 48586680596587671764843 := by
  unfold tailWord_212900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882550464353567635154077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5176733952471423513538769 3882550464353567635154077)
  ·
    refine ⟨1455956424132587863182779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3882550464353567635154077 1455956424132587863182779)
    ·
      refine ⟨2183934636198881794774169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455956424132587863182779 2183934636198881794774169)
      ·
        refine ⟨1637950977149161346080627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2183934636198881794774169 1637950977149161346080627)
        ·
          refine ⟨2456926465723742019120941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637950977149161346080627 2456926465723742019120941)
          ·
            refine ⟨921347424646403257170353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2456926465723742019120941 921347424646403257170353)
            ·
              refine ⟨691010568484802442877765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921347424646403257170353 691010568484802442877765)
              ·
                refine ⟨129564481590900458039581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691010568484802442877765 129564481590900458039581)
                ·
                  refine ⟨48586680596587671764843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129564481590900458039581 48586680596587671764843)
                  ·
                    rfl

theorem cell21_212900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_212900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212900 prefixEnd_212900 := by exact prefixLift 212900
  have htrace : WordTrace (prefixWord ++ tailWord_212900) baseStart_212900 baseEnd_212900 := by
    simpa [prefixWord, tailWord_212900, baseEnd_212900] using wordTrace_append hprefix tailTrace_212900
  have hstable : (prefixWord ++ tailWord_212900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212900).length < 2 ^ (prefixWord ++ tailWord_212900).sum := by decide
  have hdescent : baseEnd_212900 < baseStart_212900 := by decide
  rcases family_descends (prefixWord ++ tailWord_212900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212911 : List Nat := [1, 1, 2, 1, 2, 2, 4, 8]
def baseStart_212911 : Nat := 118140960795 + 212911 * 2 ^ 59
def prefixEnd_212911 : Nat := 4983230072969 + 3 ^ 40 * 212911 * 2
def baseEnd_212911 : Nat := 16196396982151365693829

theorem tailTrace_212911 : CollatzResearch.WordTrace tailWord_212911 prefixEnd_212911 16196396982151365693829 := by
  unfold tailWord_212911
  simp only [CollatzResearch.WordTrace]
  refine ⟨7765502131667284148958587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5177001421111522765972391 7765502131667284148958587)
  ·
    refine ⟨11648253197500926223437881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7765502131667284148958587 11648253197500926223437881)
    ·
      refine ⟨8736189898125694667578411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11648253197500926223437881 8736189898125694667578411)
      ·
        refine ⟨13104284847188542001367617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8736189898125694667578411 13104284847188542001367617)
        ·
          refine ⟨9828213635391406501025713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13104284847188542001367617 9828213635391406501025713)
          ·
            refine ⟨7371160226543554875769285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9828213635391406501025713 7371160226543554875769285)
            ·
              refine ⟨1382092542476916539206741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7371160226543554875769285 1382092542476916539206741)
              ·
                refine ⟨16196396982151365693829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1382092542476916539206741 16196396982151365693829)
                ·
                  rfl

theorem cell21_212911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_212911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212911 prefixEnd_212911 := by exact prefixLift 212911
  have htrace : WordTrace (prefixWord ++ tailWord_212911) baseStart_212911 baseEnd_212911 := by
    simpa [prefixWord, tailWord_212911, baseEnd_212911] using wordTrace_append hprefix tailTrace_212911
  have hstable : (prefixWord ++ tailWord_212911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212911).length < 2 ^ (prefixWord ++ tailWord_212911).sum := by decide
  have hdescent : baseEnd_212911 < baseStart_212911 := by decide
  rcases family_descends (prefixWord ++ tailWord_212911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212959 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_212959 : Nat := 118140960795 + 212959 * 2 ^ 59
def prefixEnd_212959 : Nat := 4983230072969 + 3 ^ 40 * 212959 * 2
def baseEnd_212959 : Nat := 48600145200416680281389

theorem tailTrace_212959 : CollatzResearch.WordTrace tailWord_212959 prefixEnd_212959 48600145200416680281389 := by
  unfold tailWord_212959
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767252835493388346705931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5178168556995592231137287 7767252835493388346705931)
  ·
    refine ⟨11650879253240082520058897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767252835493388346705931 11650879253240082520058897)
    ·
      refine ⟨8738159439930061890044173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11650879253240082520058897 8738159439930061890044173)
      ·
        refine ⟨3276809789973773208766565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8738159439930061890044173 3276809789973773208766565)
        ·
          refine ⟨614401835620082476643731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3276809789973773208766565 614401835620082476643731)
          ·
            refine ⟨921602753430123714965597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614401835620082476643731 921602753430123714965597)
            ·
              refine ⟨345601032536296393112099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 921602753430123714965597 345601032536296393112099)
              ·
                refine ⟨518401548804444589668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345601032536296393112099 518401548804444589668149)
                ·
                  refine ⟨48600145200416680281389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518401548804444589668149 48600145200416680281389)
                  ·
                    rfl

theorem cell21_212959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_212959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212959 prefixEnd_212959 := by exact prefixLift 212959
  have htrace : WordTrace (prefixWord ++ tailWord_212959) baseStart_212959 baseEnd_212959 := by
    simpa [prefixWord, tailWord_212959, baseEnd_212959] using wordTrace_append hprefix tailTrace_212959
  have hstable : (prefixWord ++ tailWord_212959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212959).length < 2 ^ (prefixWord ++ tailWord_212959).sum := by decide
  have hdescent : baseEnd_212959 < baseStart_212959 := by decide
  rcases family_descends (prefixWord ++ tailWord_212959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212962 : List Nat := [3, 3, 3, 1, 2, 1, 2, 6]
def baseStart_212962 : Nat := 118140960795 + 212962 * 2 ^ 59
def prefixEnd_212962 : Nat := 4983230072969 + 3 ^ 40 * 212962 * 2
def baseEnd_212962 : Nat := 16200276613763113910461

theorem tailTrace_212962 : CollatzResearch.WordTrace tailWord_212962 prefixEnd_212962 16200276613763113910461 := by
  unfold tailWord_212962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941840563620629964766285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5178241502988346572710093 1941840563620629964766285)
  ·
    refine ⟨728190211357736236787357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1941840563620629964766285 728190211357736236787357)
    ·
      refine ⟨273071329259151088795259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 728190211357736236787357 273071329259151088795259)
      ·
        refine ⟨409606993888726633192889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273071329259151088795259 409606993888726633192889)
        ·
          refine ⟨307205245416544974894667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409606993888726633192889 307205245416544974894667)
          ·
            refine ⟨460807868124817462342001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307205245416544974894667 460807868124817462342001)
            ·
              refine ⟨345605901093613096756501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460807868124817462342001 345605901093613096756501)
              ·
                refine ⟨16200276613763113910461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345605901093613096756501 16200276613763113910461)
                ·
                  rfl

theorem cell21_212962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_212962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212962 prefixEnd_212962 := by exact prefixLift 212962
  have htrace : WordTrace (prefixWord ++ tailWord_212962) baseStart_212962 baseEnd_212962 := by
    simpa [prefixWord, tailWord_212962, baseEnd_212962] using wordTrace_append hprefix tailTrace_212962
  have hstable : (prefixWord ++ tailWord_212962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212962).length < 2 ^ (prefixWord ++ tailWord_212962).sum := by decide
  have hdescent : baseEnd_212962 < baseStart_212962 := by decide
  rcases family_descends (prefixWord ++ tailWord_212962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212987 : List Nat := [1, 1, 1, 1, 1, 3, 6, 7]
def baseStart_212987 : Nat := 118140960795 + 212987 * 2 ^ 59
def prefixEnd_212987 : Nat := 4983230072969 + 3 ^ 40 * 212987 * 2
def baseEnd_212987 : Nat := 16202178393964951271555

theorem tailTrace_212987 : CollatzResearch.WordTrace tailWord_212987 prefixEnd_212987 16202178393964951271555 := by
  unfold tailWord_212987
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768274079391949128725215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5178849386261299419150143 7768274079391949128725215)
  ·
    refine ⟨11652411119087923693087823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7768274079391949128725215 11652411119087923693087823)
    ·
      refine ⟨17478616678631885539631735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11652411119087923693087823 17478616678631885539631735)
      ·
        refine ⟨26217925017947828309447603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478616678631885539631735 26217925017947828309447603)
        ·
          refine ⟨39326887526921742464171405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26217925017947828309447603 39326887526921742464171405)
          ·
            refine ⟨14747582822595653424064277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39326887526921742464171405 14747582822595653424064277)
            ·
              refine ⟨691292944809171254253013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14747582822595653424064277 691292944809171254253013)
              ·
                refine ⟨16202178393964951271555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 691292944809171254253013 16202178393964951271555)
                ·
                  rfl

theorem cell21_212987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_212987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_212987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_212987 prefixEnd_212987 := by exact prefixLift 212987
  have htrace : WordTrace (prefixWord ++ tailWord_212987) baseStart_212987 baseEnd_212987 := by
    simpa [prefixWord, tailWord_212987, baseEnd_212987] using wordTrace_append hprefix tailTrace_212987
  have hstable : (prefixWord ++ tailWord_212987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212987).length < 2 ^ (prefixWord ++ tailWord_212987).sum := by decide
  have hdescent : baseEnd_212987 < baseStart_212987 := by decide
  rcases family_descends (prefixWord ++ tailWord_212987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213021 : List Nat := [1, 4, 2, 2, 2, 3, 1, 6]
def baseStart_213021 : Nat := 118140960795 + 213021 * 2 ^ 59
def prefixEnd_213021 : Nat := 4983230072969 + 3 ^ 40 * 213021 * 2
def baseEnd_213021 : Nat := 16204764815039450082643

theorem tailTrace_213021 : CollatzResearch.WordTrace tailWord_213021 prefixEnd_213021 16204764815039450082643 := by
  unfold tailWord_213021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769514161268772935462917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5179676107512515290308611 7769514161268772935462917)
  ·
    refine ⟨1456783905237894925399297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7769514161268772935462917 1456783905237894925399297)
    ·
      refine ⟨1092587928928421194049473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456783905237894925399297 1092587928928421194049473)
      ·
        refine ⟨819440946696315895537105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1092587928928421194049473 819440946696315895537105)
        ·
          refine ⟨614580710022236921652829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819440946696315895537105 614580710022236921652829)
          ·
            refine ⟨230467766258338845619811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614580710022236921652829 230467766258338845619811)
            ·
              refine ⟨345701649387508268429717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230467766258338845619811 345701649387508268429717)
              ·
                refine ⟨16204764815039450082643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345701649387508268429717 16204764815039450082643)
                ·
                  rfl

theorem cell21_213021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 6].length) (baseStart_213021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213021 prefixEnd_213021 := by exact prefixLift 213021
  have htrace : WordTrace (prefixWord ++ tailWord_213021) baseStart_213021 baseEnd_213021 := by
    simpa [prefixWord, tailWord_213021, baseEnd_213021] using wordTrace_append hprefix tailTrace_213021
  have hstable : (prefixWord ++ tailWord_213021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213021).length < 2 ^ (prefixWord ++ tailWord_213021).sum := by decide
  have hdescent : baseEnd_213021 < baseStart_213021 := by decide
  rcases family_descends (prefixWord ++ tailWord_213021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213052 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_213052 : Nat := 118140960795 + 213052 * 2 ^ 59
def prefixEnd_213052 : Nat := 4983230072969 + 3 ^ 40 * 213052 * 2
def baseEnd_213052 : Nat := 48621369067469185231199

theorem tailTrace_213052 : CollatzResearch.WordTrace tailWord_213052 prefixEnd_213052 48621369067469185231199 := by
  unfold tailWord_213052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885322412078232614920705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5180429882770976819894273 3885322412078232614920705)
  ·
    refine ⟨2913991809058674461190529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3885322412078232614920705 2913991809058674461190529)
    ·
      refine ⟨2185493856794005845892897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2913991809058674461190529 2185493856794005845892897)
      ·
        refine ⟨1639120392595504384419673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2185493856794005845892897 1639120392595504384419673)
        ·
          refine ⟨1229340294446628288314755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1639120392595504384419673 1229340294446628288314755)
          ·
            refine ⟨1844010441669942432472133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229340294446628288314755 1844010441669942432472133)
            ·
              refine ⟨345751957813114206088525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1844010441669942432472133 345751957813114206088525)
              ·
                refine ⟨129656984179917827283197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345751957813114206088525 129656984179917827283197)
                ·
                  refine ⟨48621369067469185231199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129656984179917827283197 48621369067469185231199)
                  ·
                    rfl

theorem cell21_213052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_213052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213052 prefixEnd_213052 := by exact prefixLift 213052
  have htrace : WordTrace (prefixWord ++ tailWord_213052) baseStart_213052 baseEnd_213052 := by
    simpa [prefixWord, tailWord_213052, baseEnd_213052] using wordTrace_append hprefix tailTrace_213052
  have hstable : (prefixWord ++ tailWord_213052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213052).length < 2 ^ (prefixWord ++ tailWord_213052).sum := by decide
  have hdescent : baseEnd_213052 < baseStart_213052 := by decide
  rcases family_descends (prefixWord ++ tailWord_213052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213063 : List Nat := [1, 1, 4, 1, 3, 1, 10]
def baseStart_213063 : Nat := 118140960795 + 213063 * 2 ^ 59
def prefixEnd_213063 : Nat := 4983230072969 + 3 ^ 40 * 213063 * 2
def baseEnd_213063 : Nat := 5402653268592845616427

theorem tailTrace_213063 : CollatzResearch.WordTrace tailWord_213063 prefixEnd_213063 5402653268592845616427 := by
  unfold tailWord_213063
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771046027116614108491843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5180697351411076072327895 7771046027116614108491843)
  ·
    refine ⟨11656569040674921162737765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7771046027116614108491843 11656569040674921162737765)
    ·
      refine ⟨2185606695126547718013331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11656569040674921162737765 2185606695126547718013331)
      ·
        refine ⟨3278410042689821577019997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185606695126547718013331 3278410042689821577019997)
        ·
          refine ⟨1229403766008683091382499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3278410042689821577019997 1229403766008683091382499)
          ·
            refine ⟨1844105649013024637073749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229403766008683091382499 1844105649013024637073749)
            ·
              refine ⟨5402653268592845616427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1844105649013024637073749 5402653268592845616427)
              ·
                rfl

theorem cell21_213063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 10].length) (baseStart_213063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213063 prefixEnd_213063 := by exact prefixLift 213063
  have htrace : WordTrace (prefixWord ++ tailWord_213063) baseStart_213063 baseEnd_213063 := by
    simpa [prefixWord, tailWord_213063, baseEnd_213063] using wordTrace_append hprefix tailTrace_213063
  have hstable : (prefixWord ++ tailWord_213063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213063).length < 2 ^ (prefixWord ++ tailWord_213063).sum := by decide
  have hdescent : baseEnd_213063 < baseStart_213063 := by decide
  rcases family_descends (prefixWord ++ tailWord_213063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213125 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_213125 : Nat := 118140960795 + 213125 * 2 ^ 59
def prefixEnd_213125 : Nat := 4983230072969 + 3 ^ 40 * 213125 * 2
def baseEnd_213125 : Nat := 48638028662037280514383

theorem tailTrace_213125 : CollatzResearch.WordTrace tailWord_213125 prefixEnd_213125 48638028662037280514383 := by
  unfold tailWord_213125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773307352891998697248829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5182204901927999131499219 7773307352891998697248829)
  ·
    refine ⟨2914990257334499511468311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7773307352891998697248829 2914990257334499511468311)
    ·
      refine ⟨4372485386001749267202467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914990257334499511468311 4372485386001749267202467)
      ·
        refine ⟨6558728079002623900803701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372485386001749267202467 6558728079002623900803701)
        ·
          refine ⟨614880757406495990700347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6558728079002623900803701 614880757406495990700347)
          ·
            refine ⟨922321136109743986050521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614880757406495990700347 922321136109743986050521)
            ·
              refine ⟨691740852082307989537891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922321136109743986050521 691740852082307989537891)
              ·
                refine ⟨1037611278123461984306837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691740852082307989537891 1037611278123461984306837)
                ·
                  refine ⟨48638028662037280514383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1037611278123461984306837 48638028662037280514383)
                  ·
                    rfl

theorem cell21_213125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_213125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213125 prefixEnd_213125 := by exact prefixLift 213125
  have htrace : WordTrace (prefixWord ++ tailWord_213125) baseStart_213125 baseEnd_213125 := by
    simpa [prefixWord, tailWord_213125, baseEnd_213125] using wordTrace_append hprefix tailTrace_213125
  have hstable : (prefixWord ++ tailWord_213125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213125).length < 2 ^ (prefixWord ++ tailWord_213125).sum := by decide
  have hdescent : baseEnd_213125 < baseStart_213125 := by decide
  rcases family_descends (prefixWord ++ tailWord_213125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213128 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_213128 : Nat := 118140960795 + 213128 * 2 ^ 59
def prefixEnd_213128 : Nat := 4983230072969 + 3 ^ 40 * 213128 * 2
def baseEnd_213128 : Nat := 48638713302909941964377

theorem tailTrace_213128 : CollatzResearch.WordTrace tailWord_213128 prefixEnd_213128 48638713302909941964377 := by
  unfold tailWord_213128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886708385940565104804019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5182277847920753473072025 3886708385940565104804019)
  ·
    refine ⟨5830062578910847657206029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3886708385940565104804019 5830062578910847657206029)
    ·
      refine ⟨2186273467091567871452261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5830062578910847657206029 2186273467091567871452261)
      ·
        refine ⟨409926275079668975897299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2186273467091567871452261 409926275079668975897299)
        ·
          refine ⟨614889412619503463845949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409926275079668975897299 614889412619503463845949)
          ·
            refine ⟨230583529732313798942231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614889412619503463845949 230583529732313798942231)
            ·
              refine ⟨345875294598470698413347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230583529732313798942231 345875294598470698413347)
              ·
                refine ⟨518812941897706047620021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345875294598470698413347 518812941897706047620021)
                ·
                  refine ⟨48638713302909941964377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518812941897706047620021 48638713302909941964377)
                  ·
                    rfl

theorem cell21_213128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_213128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213128 prefixEnd_213128 := by exact prefixLift 213128
  have htrace : WordTrace (prefixWord ++ tailWord_213128) baseStart_213128 baseEnd_213128 := by
    simpa [prefixWord, tailWord_213128, baseEnd_213128] using wordTrace_append hprefix tailTrace_213128
  have hstable : (prefixWord ++ tailWord_213128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213128).length < 2 ^ (prefixWord ++ tailWord_213128).sum := by decide
  have hdescent : baseEnd_213128 < baseStart_213128 := by decide
  rcases family_descends (prefixWord ++ tailWord_213128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213173 : List Nat := [1, 3, 3, 4, 2, 8]
def baseStart_213173 : Nat := 118140960795 + 213173 * 2 ^ 59
def prefixEnd_213173 : Nat := 4983230072969 + 3 ^ 40 * 213173 * 2
def baseEnd_213173 : Nat := 1801814182074069026455

theorem tailTrace_213173 : CollatzResearch.WordTrace tailWord_213173 prefixEnd_213173 1801814182074069026455 := by
  unfold tailWord_213173
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775058056718102894996173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5183372037812068596664115 7775058056718102894996173)
  ·
    refine ⟨2915646771269288585623565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7775058056718102894996173 2915646771269288585623565)
    ·
      refine ⟨1093367539225983219608837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2915646771269288585623565 1093367539225983219608837)
      ·
        refine ⟨205006413604871853676657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1093367539225983219608837 205006413604871853676657)
        ·
          refine ⟨153754810203653890257493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205006413604871853676657 153754810203653890257493)
          ·
            refine ⟨1801814182074069026455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 153754810203653890257493 1801814182074069026455)
            ·
              rfl

theorem cell21_213173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 8].length) (baseStart_213173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213173 prefixEnd_213173 := by exact prefixLift 213173
  have htrace : WordTrace (prefixWord ++ tailWord_213173) baseStart_213173 baseEnd_213173 := by
    simpa [prefixWord, tailWord_213173, baseEnd_213173] using wordTrace_append hprefix tailTrace_213173
  have hstable : (prefixWord ++ tailWord_213173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213173).length < 2 ^ (prefixWord ++ tailWord_213173).sum := by decide
  have hdescent : baseEnd_213173 < baseStart_213173 := by decide
  rcases family_descends (prefixWord ++ tailWord_213173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213201 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_213201 : Nat := 118140960795 + 213201 * 2 ^ 59
def prefixEnd_213201 : Nat := 4983230072969 + 3 ^ 40 * 213201 * 2
def baseEnd_213201 : Nat := 48655372897478037247561

theorem tailTrace_213201 : CollatzResearch.WordTrace tailWord_213201 prefixEnd_213201 48655372897478037247561 := by
  unfold tailWord_213201
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776079300616663677015457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5184052867077775784676971 7776079300616663677015457)
  ·
    refine ⟨5832059475462497757761593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7776079300616663677015457 5832059475462497757761593)
    ·
      refine ⟨4374044606596873318321195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5832059475462497757761593 4374044606596873318321195)
      ·
        refine ⟨6561066909895309977481793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374044606596873318321195 6561066909895309977481793)
        ·
          refine ⟨4920800182421482483111345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6561066909895309977481793 4920800182421482483111345)
          ·
            refine ⟨3690600136816111862333509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4920800182421482483111345 3690600136816111862333509)
            ·
              refine ⟨691987525653020974187533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3690600136816111862333509 691987525653020974187533)
              ·
                refine ⟨259495322119882865320325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691987525653020974187533 259495322119882865320325)
                ·
                  refine ⟨48655372897478037247561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259495322119882865320325 48655372897478037247561)
                  ·
                    rfl

theorem cell21_213201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_213201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213201 prefixEnd_213201 := by exact prefixLift 213201
  have htrace : WordTrace (prefixWord ++ tailWord_213201) baseStart_213201 baseEnd_213201 := by
    simpa [prefixWord, tailWord_213201, baseEnd_213201] using wordTrace_append hprefix tailTrace_213201
  have hstable : (prefixWord ++ tailWord_213201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213201).length < 2 ^ (prefixWord ++ tailWord_213201).sum := by decide
  have hdescent : baseEnd_213201 < baseStart_213201 := by decide
  rcases family_descends (prefixWord ++ tailWord_213201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213280 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_213280 : Nat := 118140960795 + 213280 * 2 ^ 59
def prefixEnd_213280 : Nat := 4983230072969 + 3 ^ 40 * 213280 * 2
def baseEnd_213280 : Nat := 48673401773791455430733

theorem tailTrace_213280 : CollatzResearch.WordTrace tailWord_213280 prefixEnd_213280 48673401773791455430733 := by
  unfold tailWord_213280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889480333665230084570647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5185973778220306779427529 3889480333665230084570647)
  ·
    refine ⟨5834220500497845126855971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3889480333665230084570647 5834220500497845126855971)
    ·
      refine ⟨8751330750746767690283957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834220500497845126855971 8751330750746767690283957)
      ·
        refine ⟨820437257882509470964121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8751330750746767690283957 820437257882509470964121)
        ·
          refine ⟨615327943411882103223091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820437257882509470964121 615327943411882103223091)
          ·
            refine ⟨922991915117823154834637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615327943411882103223091 922991915117823154834637)
            ·
              refine ⟨346121968169183683062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922991915117823154834637 346121968169183683062989)
              ·
                refine ⟨129795738063443881148621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346121968169183683062989 129795738063443881148621)
                ·
                  refine ⟨48673401773791455430733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129795738063443881148621 48673401773791455430733)
                  ·
                    rfl

theorem cell21_213280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_213280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213280 prefixEnd_213280 := by exact prefixLift 213280
  have htrace : WordTrace (prefixWord ++ tailWord_213280) baseStart_213280 baseEnd_213280 := by
    simpa [prefixWord, tailWord_213280, baseEnd_213280] using wordTrace_append hprefix tailTrace_213280
  have hstable : (prefixWord ++ tailWord_213280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213280).length < 2 ^ (prefixWord ++ tailWord_213280).sum := by decide
  have hdescent : baseEnd_213280 < baseStart_213280 := by decide
  rcases family_descends (prefixWord ++ tailWord_213280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213297 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 3]
def baseStart_213297 : Nat := 118140960795 + 213297 * 2 ^ 59
def prefixEnd_213297 : Nat := 4983230072969 + 3 ^ 40 * 213297 * 2
def baseEnd_213297 : Nat := 48677281405403203647365

theorem tailTrace_213297 : CollatzResearch.WordTrace tailWord_213297 prefixEnd_213297 48677281405403203647365 := by
  unfold tailWord_213297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779580708268872072510145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5186387138845914715006763 7779580708268872072510145)
  ·
    refine ⟨5834685531201654054382609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7779580708268872072510145 5834685531201654054382609)
    ·
      refine ⟨4376014148401240540786957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5834685531201654054382609 4376014148401240540786957)
      ·
        refine ⟨1641005305650465202795109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4376014148401240540786957 1641005305650465202795109)
        ·
          refine ⟨307688494809462225524083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1641005305650465202795109 307688494809462225524083)
          ·
            refine ⟨461532742214193338286125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307688494809462225524083 461532742214193338286125)
            ·
              refine ⟨173074778330322501857297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461532742214193338286125 173074778330322501857297)
              ·
                refine ⟨129806083747741876392973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173074778330322501857297 129806083747741876392973)
                ·
                  refine ⟨48677281405403203647365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129806083747741876392973 48677281405403203647365)
                  ·
                    rfl

theorem cell21_213297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_213297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213297 prefixEnd_213297 := by exact prefixLift 213297
  have htrace : WordTrace (prefixWord ++ tailWord_213297) baseStart_213297 baseEnd_213297 := by
    simpa [prefixWord, tailWord_213297, baseEnd_213297] using wordTrace_append hprefix tailTrace_213297
  have hstable : (prefixWord ++ tailWord_213297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213297).length < 2 ^ (prefixWord ++ tailWord_213297).sum := by decide
  have hdescent : baseEnd_213297 < baseStart_213297 := by decide
  rcases family_descends (prefixWord ++ tailWord_213297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213336 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_213336 : Nat := 118140960795 + 213336 * 2 ^ 59
def prefixEnd_213336 : Nat := 4983230072969 + 3 ^ 40 * 213336 * 2
def baseEnd_213336 : Nat := 48686181736747802497285

theorem tailTrace_213336 : CollatzResearch.WordTrace tailWord_213336 prefixEnd_213336 48686181736747802497285 := by
  unfold tailWord_213336
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890501577563790866589931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5187335436751721155453241 3890501577563790866589931)
  ·
    refine ⟨5835752366345686299884897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3890501577563790866589931 5835752366345686299884897)
    ·
      refine ⟨4376814274759264724913673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5835752366345686299884897 4376814274759264724913673)
      ·
        refine ⟨3282610706069448543685255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4376814274759264724913673 3282610706069448543685255)
        ·
          refine ⟨4923916059104172815527883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282610706069448543685255 4923916059104172815527883)
          ·
            refine ⟨7385874088656259223291825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923916059104172815527883 7385874088656259223291825)
            ·
              refine ⟨5539405566492194417468869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385874088656259223291825 5539405566492194417468869)
              ·
                refine ⟨1038638543717286453275413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5539405566492194417468869 1038638543717286453275413)
                ·
                  refine ⟨48686181736747802497285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1038638543717286453275413 48686181736747802497285)
                  ·
                    rfl

theorem cell21_213336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_213336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213336 prefixEnd_213336 := by exact prefixLift 213336
  have htrace : WordTrace (prefixWord ++ tailWord_213336) baseStart_213336 baseEnd_213336 := by
    simpa [prefixWord, tailWord_213336, baseEnd_213336] using wordTrace_append hprefix tailTrace_213336
  have hstable : (prefixWord ++ tailWord_213336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213336).length < 2 ^ (prefixWord ++ tailWord_213336).sum := by decide
  have hdescent : baseEnd_213336 < baseStart_213336 := by decide
  rcases family_descends (prefixWord ++ tailWord_213336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213342 : List Nat := [4, 4, 2, 1, 10]
def baseStart_213342 : Nat := 118140960795 + 213342 * 2 ^ 59
def prefixEnd_213342 : Nat := 4983230072969 + 3 ^ 40 * 213342 * 2
def baseEnd_213342 : Nat := 601080876771520066633

theorem tailTrace_213342 : CollatzResearch.WordTrace tailWord_213342 prefixEnd_213342 601080876771520066633 := by
  unfold tailWord_213342
  simp only [CollatzResearch.WordTrace]
  refine ⟨972652749138230594737285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5187481328737229838598853 972652749138230594737285)
  ·
    refine ⟨182372390463418236513241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 972652749138230594737285 182372390463418236513241)
    ·
      refine ⟨136779292847563677384931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182372390463418236513241 136779292847563677384931)
      ·
        refine ⟨205168939271345516077397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136779292847563677384931 205168939271345516077397)
        ·
          refine ⟨601080876771520066633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 205168939271345516077397 601080876771520066633)
          ·
            rfl

theorem cell21_213342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 10].length) (baseStart_213342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213342 prefixEnd_213342 := by exact prefixLift 213342
  have htrace : WordTrace (prefixWord ++ tailWord_213342) baseStart_213342 baseEnd_213342 := by
    simpa [prefixWord, tailWord_213342, baseEnd_213342] using wordTrace_append hprefix tailTrace_213342
  have hstable : (prefixWord ++ tailWord_213342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213342).length < 2 ^ (prefixWord ++ tailWord_213342).sum := by decide
  have hdescent : baseEnd_213342 < baseStart_213342 := by decide
  rcases family_descends (prefixWord ++ tailWord_213342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213353 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_213353 : Nat := 118140960795 + 213353 * 2 ^ 59
def prefixEnd_213353 : Nat := 4983230072969 + 3 ^ 40 * 213353 * 2
def baseEnd_213353 : Nat := 48690061368359550713917

theorem tailTrace_213353 : CollatzResearch.WordTrace tailWord_213353 prefixEnd_213353 48690061368359550713917 := by
  unfold tailWord_213353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781623196065993636548713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5187748797377329091032475 7781623196065993636548713)
  ·
    refine ⟨5836217397049495227411535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7781623196065993636548713 5836217397049495227411535)
    ·
      refine ⟨8754326095574242841117303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836217397049495227411535 8754326095574242841117303)
      ·
        refine ⟨13131489143361364261675955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754326095574242841117303 13131489143361364261675955)
        ·
          refine ⟨19697233715042046392513933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13131489143361364261675955 19697233715042046392513933)
          ·
            refine ⟨7386462643140767397192725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19697233715042046392513933 7386462643140767397192725)
            ·
              refine ⟨346240436397223471743409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7386462643140767397192725 346240436397223471743409)
              ·
                refine ⟨259680327297917603807557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346240436397223471743409 259680327297917603807557)
                ·
                  refine ⟨48690061368359550713917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259680327297917603807557 48690061368359550713917)
                  ·
                    rfl

theorem cell21_213353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_213353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213353 prefixEnd_213353 := by exact prefixLift 213353
  have htrace : WordTrace (prefixWord ++ tailWord_213353) baseStart_213353 baseEnd_213353 := by
    simpa [prefixWord, tailWord_213353, baseEnd_213353] using wordTrace_append hprefix tailTrace_213353
  have hstable : (prefixWord ++ tailWord_213353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213353).length < 2 ^ (prefixWord ++ tailWord_213353).sum := by decide
  have hdescent : baseEnd_213353 < baseStart_213353 := by decide
  rcases family_descends (prefixWord ++ tailWord_213353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213356 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_213356 : Nat := 118140960795 + 213356 * 2 ^ 59
def prefixEnd_213356 : Nat := 4983230072969 + 3 ^ 40 * 213356 * 2
def baseEnd_213356 : Nat := 48690746009232212163911

theorem tailTrace_213356 : CollatzResearch.WordTrace tailWord_213356 prefixEnd_213356 48690746009232212163911 := by
  unfold tailWord_213356
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890866307527562574453961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5187821743370083432605281 3890866307527562574453961)
  ·
    refine ⟨2918149730645671930840471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3890866307527562574453961 2918149730645671930840471)
    ·
      refine ⟨4377224595968507896260707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918149730645671930840471 4377224595968507896260707)
      ·
        refine ⟨6565836893952761844391061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377224595968507896260707 6565836893952761844391061)
        ·
          refine ⟨307773604404035711455831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6565836893952761844391061 307773604404035711455831)
          ·
            refine ⟨461660406606053567183747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307773604404035711455831 461660406606053567183747)
            ·
              refine ⟨692490609909080350775621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461660406606053567183747 692490609909080350775621)
              ·
                refine ⟨129841989357952565770429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692490609909080350775621 129841989357952565770429)
                ·
                  refine ⟨48690746009232212163911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129841989357952565770429 48690746009232212163911)
                  ·
                    rfl

theorem cell21_213356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_213356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213356 prefixEnd_213356 := by exact prefixLift 213356
  have htrace : WordTrace (prefixWord ++ tailWord_213356) baseStart_213356 baseEnd_213356 := by
    simpa [prefixWord, tailWord_213356, baseEnd_213356] using wordTrace_append hprefix tailTrace_213356
  have hstable : (prefixWord ++ tailWord_213356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213356).length < 2 ^ (prefixWord ++ tailWord_213356).sum := by decide
  have hdescent : baseEnd_213356 < baseStart_213356 := by decide
  rcases family_descends (prefixWord ++ tailWord_213356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213384 : List Nat := [2, 1, 3, 3, 1, 1, 5, 5]
def baseStart_213384 : Nat := 118140960795 + 213384 * 2 ^ 59
def prefixEnd_213384 : Nat := 4983230072969 + 3 ^ 40 * 213384 * 2
def baseEnd_213384 : Nat := 16232378663570128565729

theorem tailTrace_213384 : CollatzResearch.WordTrace tailWord_213384 prefixEnd_213384 16232378663570128565729 := by
  unfold tailWord_213384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891376929476842965463603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5188502572635790620618137 3891376929476842965463603)
  ·
    refine ⟨5837065394215264448195405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3891376929476842965463603 5837065394215264448195405)
    ·
      refine ⟨2188899522830724168073277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5837065394215264448195405 2188899522830724168073277)
      ·
        refine ⟨820837321061521563027479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2188899522830724168073277 820837321061521563027479)
        ·
          refine ⟨1231255981592282344541219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820837321061521563027479 1231255981592282344541219)
          ·
            refine ⟨1846883972388423516811829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231255981592282344541219 1846883972388423516811829)
            ·
              refine ⟨173145372411414704701109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1846883972388423516811829 173145372411414704701109)
              ·
                refine ⟨16232378663570128565729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173145372411414704701109 16232378663570128565729)
                ·
                  rfl

theorem cell21_213384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_213384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213384 prefixEnd_213384 := by exact prefixLift 213384
  have htrace : WordTrace (prefixWord ++ tailWord_213384) baseStart_213384 baseEnd_213384 := by
    simpa [prefixWord, tailWord_213384, baseEnd_213384] using wordTrace_append hprefix tailTrace_213384
  have hstable : (prefixWord ++ tailWord_213384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213384).length < 2 ^ (prefixWord ++ tailWord_213384).sum := by decide
  have hdescent : baseEnd_213384 < baseStart_213384 := by decide
  rcases family_descends (prefixWord ++ tailWord_213384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213415 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_213415 : Nat := 118140960795 + 213415 * 2 ^ 59
def prefixEnd_213415 : Nat := 4983230072969 + 3 ^ 40 * 213415 * 2
def baseEnd_213415 : Nat := 48704210613061220680457

theorem tailTrace_213415 : CollatzResearch.WordTrace tailWord_213415 prefixEnd_213415 48704210613061220680457 := by
  unfold tailWord_213415
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783884521841378225305699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5189256347894252150203799 7783884521841378225305699)
  ·
    refine ⟨11675826782762067337958549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7783884521841378225305699 11675826782762067337958549)
    ·
      refine ⟨547304380441971906466807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11675826782762067337958549 547304380441971906466807)
      ·
        refine ⟨820956570662957859700211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547304380441971906466807 820956570662957859700211)
        ·
          refine ⟨1231434855994436789550317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820956570662957859700211 1231434855994436789550317)
          ·
            refine ⟨461788070997913796081369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1231434855994436789550317 461788070997913796081369)
            ·
              refine ⟨346341053248435347061027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461788070997913796081369 346341053248435347061027)
              ·
                refine ⟨519511579872653020591541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346341053248435347061027 519511579872653020591541)
                ·
                  refine ⟨48704210613061220680457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 519511579872653020591541 48704210613061220680457)
                  ·
                    rfl

theorem cell21_213415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_213415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213415 prefixEnd_213415 := by exact prefixLift 213415
  have htrace : WordTrace (prefixWord ++ tailWord_213415) baseStart_213415 baseEnd_213415 := by
    simpa [prefixWord, tailWord_213415, baseEnd_213415] using wordTrace_append hprefix tailTrace_213415
  have hstable : (prefixWord ++ tailWord_213415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213415).length < 2 ^ (prefixWord ++ tailWord_213415).sum := by decide
  have hdescent : baseEnd_213415 < baseStart_213415 := by decide
  rcases family_descends (prefixWord ++ tailWord_213415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213457 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_213457 : Nat := 118140960795 + 213457 * 2 ^ 59
def prefixEnd_213457 : Nat := 4983230072969 + 3 ^ 40 * 213457 * 2
def baseEnd_213457 : Nat := 48713795585278480980371

theorem tailTrace_213457 : CollatzResearch.WordTrace tailWord_213457 prefixEnd_213457 48713795585278480980371 := by
  unfold tailWord_213457
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785416387689219398334625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5190277591792812932223083 7785416387689219398334625)
  ·
    refine ⟨5839062290766914548750969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7785416387689219398334625 5839062290766914548750969)
    ·
      refine ⟨4379296718075185911563227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5839062290766914548750969 4379296718075185911563227)
      ·
        refine ⟨6568945077112778867344841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379296718075185911563227 6568945077112778867344841)
        ·
          refine ⟨4926708807834584150508631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6568945077112778867344841 4926708807834584150508631)
          ·
            refine ⟨7390063211751876225762947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926708807834584150508631 7390063211751876225762947)
            ·
              refine ⟨11085094817627814338644421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390063211751876225762947 11085094817627814338644421)
              ·
                refine ⟨2078455278305215188495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11085094817627814338644421 2078455278305215188495829)
                ·
                  refine ⟨48713795585278480980371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2078455278305215188495829 48713795585278480980371)
                  ·
                    rfl

theorem cell21_213457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_213457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213457 prefixEnd_213457 := by exact prefixLift 213457
  have htrace : WordTrace (prefixWord ++ tailWord_213457) baseStart_213457 baseEnd_213457 := by
    simpa [prefixWord, tailWord_213457, baseEnd_213457] using wordTrace_append hprefix tailTrace_213457
  have hstable : (prefixWord ++ tailWord_213457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213457).length < 2 ^ (prefixWord ++ tailWord_213457).sum := by decide
  have hdescent : baseEnd_213457 < baseStart_213457 := by decide
  rcases family_descends (prefixWord ++ tailWord_213457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213460 : List Nat := [2, 4, 1, 2, 2, 3, 7]
def baseStart_213460 : Nat := 118140960795 + 213460 * 2 ^ 59
def prefixEnd_213460 : Nat := 4983230072969 + 3 ^ 40 * 213460 * 2
def baseEnd_213460 : Nat := 5412720025127904714485

theorem tailTrace_213460 : CollatzResearch.WordTrace tailWord_213460 prefixEnd_213460 5412720025127904714485 := by
  unfold tailWord_213460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892762903339175455346917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5190350537785567273795889 3892762903339175455346917)
  ·
    refine ⟨729893044376095397877547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3892762903339175455346917 729893044376095397877547)
    ·
      refine ⟨1094839566564143096816321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729893044376095397877547 1094839566564143096816321)
      ·
        refine ⟨821129674923107322612241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094839566564143096816321 821129674923107322612241)
        ·
          refine ⟨615847256192330491959181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821129674923107322612241 615847256192330491959181)
          ·
            refine ⟨230942721072123934484693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615847256192330491959181 230942721072123934484693)
            ·
              refine ⟨5412720025127904714485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230942721072123934484693 5412720025127904714485)
              ·
                rfl

theorem cell21_213460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 7].length) (baseStart_213460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213460 prefixEnd_213460 := by exact prefixLift 213460
  have htrace : WordTrace (prefixWord ++ tailWord_213460) baseStart_213460 baseEnd_213460 := by
    simpa [prefixWord, tailWord_213460, baseEnd_213460] using wordTrace_append hprefix tailTrace_213460
  have hstable : (prefixWord ++ tailWord_213460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213460).length < 2 ^ (prefixWord ++ tailWord_213460).sum := by decide
  have hdescent : baseEnd_213460 < baseStart_213460 := by decide
  rcases family_descends (prefixWord ++ tailWord_213460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213567 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 3]
def baseStart_213567 : Nat := 118140960795 + 213567 * 2 ^ 59
def prefixEnd_213567 : Nat := 4983230072969 + 3 ^ 40 * 213567 * 2
def baseEnd_213567 : Nat := 48738899083942734146813

theorem tailTrace_213567 : CollatzResearch.WordTrace tailWord_213567 prefixEnd_213567 48738899083942734146813 := by
  unfold tailWord_213567
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789428417290708184838955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5192952278193805456559303 7789428417290708184838955)
  ·
    refine ⟨11684142625936062277258433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789428417290708184838955 11684142625936062277258433)
    ·
      refine ⟨8763106969452046707943825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11684142625936062277258433 8763106969452046707943825)
      ·
        refine ⟨6572330227089035030957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8763106969452046707943825 6572330227089035030957869)
        ·
          refine ⟨2464623835158388136609201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6572330227089035030957869 2464623835158388136609201)
          ·
            refine ⟨1848467876368791102456901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464623835158388136609201 1848467876368791102456901)
            ·
              refine ⟨346587726819148331710669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1848467876368791102456901 346587726819148331710669)
              ·
                refine ⟨129970397557180624391501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346587726819148331710669 129970397557180624391501)
                ·
                  refine ⟨48738899083942734146813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129970397557180624391501 48738899083942734146813)
                  ·
                    rfl

theorem cell21_213567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3].length) (baseStart_213567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213567 prefixEnd_213567 := by exact prefixLift 213567
  have htrace : WordTrace (prefixWord ++ tailWord_213567) baseStart_213567 baseEnd_213567 := by
    simpa [prefixWord, tailWord_213567, baseEnd_213567] using wordTrace_append hprefix tailTrace_213567
  have hstable : (prefixWord ++ tailWord_213567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213567).length < 2 ^ (prefixWord ++ tailWord_213567).sum := by decide
  have hdescent : baseEnd_213567 < baseStart_213567 := by decide
  rcases family_descends (prefixWord ++ tailWord_213567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213736 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_213736 : Nat := 118140960795 + 213736 * 2 ^ 59
def prefixEnd_213736 : Nat := 4983230072969 + 3 ^ 40 * 213736 * 2
def baseEnd_213736 : Nat := 48777467186435995829801

theorem tailTrace_213736 : CollatzResearch.WordTrace tailWord_213736 prefixEnd_213736 48777467186435995829801 := by
  unfold tailWord_213736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897796176839225023870531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5197061569118966698494041 3897796176839225023870531)
  ·
    refine ⟨5846694265258837535805797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3897796176839225023870531 5846694265258837535805797)
    ·
      refine ⟨1096255174736032037963587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5846694265258837535805797 1096255174736032037963587)
      ·
        refine ⟨1644382762104048056945381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096255174736032037963587 1644382762104048056945381)
        ·
          refine ⟨308321767894509010677259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1644382762104048056945381 308321767894509010677259)
          ·
            refine ⟨462482651841763516015889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308321767894509010677259 462482651841763516015889)
            ·
              refine ⟨346861988881322637011917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462482651841763516015889 346861988881322637011917)
              ·
                refine ⟨130073245830495988879469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346861988881322637011917 130073245830495988879469)
                ·
                  refine ⟨48777467186435995829801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130073245830495988879469 48777467186435995829801)
                  ·
                    rfl

theorem cell21_213736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_213736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213736 prefixEnd_213736 := by exact prefixLift 213736
  have htrace : WordTrace (prefixWord ++ tailWord_213736) baseStart_213736 baseEnd_213736 := by
    simpa [prefixWord, tailWord_213736, baseEnd_213736] using wordTrace_append hprefix tailTrace_213736
  have hstable : (prefixWord ++ tailWord_213736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213736).length < 2 ^ (prefixWord ++ tailWord_213736).sum := by decide
  have hdescent : baseEnd_213736 < baseStart_213736 := by decide
  rcases family_descends (prefixWord ++ tailWord_213736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213792 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_213792 : Nat := 118140960795 + 213792 * 2 ^ 59
def prefixEnd_213792 : Nat := 4983230072969 + 3 ^ 40 * 213792 * 2
def baseEnd_213792 : Nat := 48790247149392342896353

theorem tailTrace_213792 : CollatzResearch.WordTrace tailWord_213792 prefixEnd_213792 48790247149392342896353 := by
  unfold tailWord_213792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898817420737785805889815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5198423227650381074519753 3898817420737785805889815)
  ·
    refine ⟨5848226131106678708834723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3898817420737785805889815 5848226131106678708834723)
    ·
      refine ⟨8772339196660018063252085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5848226131106678708834723 8772339196660018063252085)
      ·
        refine ⟨822406799686876693429883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8772339196660018063252085 822406799686876693429883)
        ·
          refine ⟨1233610199530315040144825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822406799686876693429883 1233610199530315040144825)
          ·
            refine ⟨925207649647736280108619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233610199530315040144825 925207649647736280108619)
            ·
              refine ⟨1387811474471604420162929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925207649647736280108619 1387811474471604420162929)
              ·
                refine ⟨1040858605853703315122197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387811474471604420162929 1040858605853703315122197)
                ·
                  refine ⟨48790247149392342896353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1040858605853703315122197 48790247149392342896353)
                  ·
                    rfl

theorem cell21_213792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_213792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213792 prefixEnd_213792 := by exact prefixLift 213792
  have htrace : WordTrace (prefixWord ++ tailWord_213792) baseStart_213792 baseEnd_213792 := by
    simpa [prefixWord, tailWord_213792, baseEnd_213792] using wordTrace_append hprefix tailTrace_213792
  have hstable : (prefixWord ++ tailWord_213792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213792).length < 2 ^ (prefixWord ++ tailWord_213792).sum := by decide
  have hdescent : baseEnd_213792 < baseStart_213792 := by decide
  rcases family_descends (prefixWord ++ tailWord_213792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213812 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_213812 : Nat := 118140960795 + 213812 * 2 ^ 59
def prefixEnd_213812 : Nat := 4983230072969 + 3 ^ 40 * 213812 * 2
def baseEnd_213812 : Nat := 48794811421876752562979

theorem tailTrace_213812 : CollatzResearch.WordTrace tailWord_213812 prefixEnd_213812 48794811421876752562979 := by
  unfold tailWord_213812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899182150701557513753845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5198909534268743351671793 3899182150701557513753845)
  ·
    refine ⟨365548326628271016914423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3899182150701557513753845 365548326628271016914423)
    ·
      refine ⟨548322489942406525371635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365548326628271016914423 548322489942406525371635)
      ·
        refine ⟨822483734913609788057453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548322489942406525371635 822483734913609788057453)
        ·
          refine ⟨308431400592603670521545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822483734913609788057453 308431400592603670521545)
          ·
            refine ⟨231323550444452752891159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308431400592603670521545 231323550444452752891159)
            ·
              refine ⟨346985325666679129336739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231323550444452752891159 346985325666679129336739)
              ·
                refine ⟨520477988500018694005109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346985325666679129336739 520477988500018694005109)
                ·
                  refine ⟨48794811421876752562979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 520477988500018694005109 48794811421876752562979)
                  ·
                    rfl

theorem cell21_213812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_213812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213812 prefixEnd_213812 := by exact prefixLift 213812
  have htrace : WordTrace (prefixWord ++ tailWord_213812) baseStart_213812 baseEnd_213812 := by
    simpa [prefixWord, tailWord_213812, baseEnd_213812] using wordTrace_append hprefix tailTrace_213812
  have hstable : (prefixWord ++ tailWord_213812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213812).length < 2 ^ (prefixWord ++ tailWord_213812).sum := by decide
  have hdescent : baseEnd_213812 < baseStart_213812 := by decide
  rcases family_descends (prefixWord ++ tailWord_213812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213823 : List Nat := [1, 1, 2, 2, 5, 2, 2, 6]
def baseStart_213823 : Nat := 118140960795 + 213823 * 2 ^ 59
def prefixEnd_213823 : Nat := 4983230072969 + 3 ^ 40 * 213823 * 2
def baseEnd_213823 : Nat := 16265773923914392626541

theorem tailTrace_213823 : CollatzResearch.WordTrace tailWord_213823 prefixEnd_213823 16265773923914392626541 := by
  unfold tailWord_213823
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798765504363263906158123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5199177002908842604105415 7798765504363263906158123)
  ·
    refine ⟨11698148256544895859237185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7798765504363263906158123 11698148256544895859237185)
    ·
      refine ⟨8773611192408671894427889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11698148256544895859237185 8773611192408671894427889)
      ·
        refine ⟨6580208394306503920820917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8773611192408671894427889 6580208394306503920820917)
        ·
          refine ⟨616894536966234742576961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6580208394306503920820917 616894536966234742576961)
          ·
            refine ⟨462670902724676056932721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616894536966234742576961 462670902724676056932721)
            ·
              refine ⟨347003177043507042699541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462670902724676056932721 347003177043507042699541)
              ·
                refine ⟨16265773923914392626541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347003177043507042699541 16265773923914392626541)
                ·
                  rfl

theorem cell21_213823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_213823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_213823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_213823 prefixEnd_213823 := by exact prefixLift 213823
  have htrace : WordTrace (prefixWord ++ tailWord_213823) baseStart_213823 baseEnd_213823 := by
    simpa [prefixWord, tailWord_213823, baseEnd_213823] using wordTrace_append hprefix tailTrace_213823
  have hstable : (prefixWord ++ tailWord_213823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213823).length < 2 ^ (prefixWord ++ tailWord_213823).sum := by decide
  have hdescent : baseEnd_213823 < baseStart_213823 := by decide
  rcases family_descends (prefixWord ++ tailWord_213823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214037 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_214037 : Nat := 118140960795 + 214037 * 2 ^ 59
def prefixEnd_214037 : Nat := 4983230072969 + 3 ^ 40 * 214037 * 2
def baseEnd_214037 : Nat := 48846159487326361312519

theorem tailTrace_214037 : CollatzResearch.WordTrace tailWord_214037 prefixEnd_214037 48846159487326361312519 := by
  unfold tailWord_214037
  simp only [CollatzResearch.WordTrace]
  refine ⟨7806570725587978454448365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5204380483725318969632243 7806570725587978454448365)
  ·
    refine ⟨2927464022095491920418137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7806570725587978454448365 2927464022095491920418137)
    ·
      refine ⟨2195598016571618940313603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2927464022095491920418137 2195598016571618940313603)
      ·
        refine ⟨3293397024857428410470405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195598016571618940313603 3293397024857428410470405)
        ·
          refine ⟨617511942160767826963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3293397024857428410470405 617511942160767826963201)
          ·
            refine ⟨463133956620575870222401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617511942160767826963201 463133956620575870222401)
            ·
              refine ⟨347350467465431902666801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463133956620575870222401 347350467465431902666801)
              ·
                refine ⟨260512850599073927000101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347350467465431902666801 260512850599073927000101)
                ·
                  refine ⟨48846159487326361312519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260512850599073927000101 48846159487326361312519)
                  ·
                    rfl

theorem cell21_214037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_214037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214037 prefixEnd_214037 := by exact prefixLift 214037
  have htrace : WordTrace (prefixWord ++ tailWord_214037) baseStart_214037 baseEnd_214037 := by
    simpa [prefixWord, tailWord_214037, baseEnd_214037] using wordTrace_append hprefix tailTrace_214037
  have hstable : (prefixWord ++ tailWord_214037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214037).length < 2 ^ (prefixWord ++ tailWord_214037).sum := by decide
  have hdescent : baseEnd_214037 < baseStart_214037 := by decide
  rcases family_descends (prefixWord ++ tailWord_214037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214040 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_214040 : Nat := 118140960795 + 214040 * 2 ^ 59
def prefixEnd_214040 : Nat := 4983230072969 + 3 ^ 40 * 214040 * 2
def baseEnd_214040 : Nat := 48846844128199022762513

theorem tailTrace_214040 : CollatzResearch.WordTrace tailWord_214040 prefixEnd_214040 48846844128199022762513 := by
  unfold tailWord_214040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903340072288554983403787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5204453429718073311205049 3903340072288554983403787)
  ·
    refine ⟨5855010108432832475105681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903340072288554983403787 5855010108432832475105681)
    ·
      refine ⟨4391257581324624356329261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5855010108432832475105681 4391257581324624356329261)
      ·
        refine ⟨1646721592996734133623473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4391257581324624356329261 1646721592996734133623473)
        ·
          refine ⟨1235041194747550600217605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646721592996734133623473 1235041194747550600217605)
          ·
            refine ⟨231570224015165737540801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1235041194747550600217605 231570224015165737540801)
            ·
              refine ⟨173677668011374303155601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231570224015165737540801 173677668011374303155601)
              ·
                refine ⟨130258251008530727366701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173677668011374303155601 130258251008530727366701)
                ·
                  refine ⟨48846844128199022762513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130258251008530727366701 48846844128199022762513)
                  ·
                    rfl

theorem cell21_214040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_214040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214040 prefixEnd_214040 := by exact prefixLift 214040
  have htrace : WordTrace (prefixWord ++ tailWord_214040) baseStart_214040 baseEnd_214040 := by
    simpa [prefixWord, tailWord_214040, baseEnd_214040] using wordTrace_append hprefix tailTrace_214040
  have hstable : (prefixWord ++ tailWord_214040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214040).length < 2 ^ (prefixWord ++ tailWord_214040).sum := by decide
  have hdescent : baseEnd_214040 < baseStart_214040 := by decide
  rcases family_descends (prefixWord ++ tailWord_214040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214051 : List Nat := [1, 1, 1, 4, 3, 4, 1, 6]
def baseStart_214051 : Nat := 118140960795 + 214051 * 2 ^ 59
def prefixEnd_214051 : Nat := 4983230072969 + 3 ^ 40 * 214051 * 2
def baseEnd_214051 : Nat := 16283118159355149359719

theorem tailTrace_214051 : CollatzResearch.WordTrace tailWord_214051 prefixEnd_214051 16283118159355149359719 := by
  unfold tailWord_214051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807081347537258845458007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5204720898358172563638671 7807081347537258845458007)
  ·
    refine ⟨11710622021305888268187011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7807081347537258845458007 11710622021305888268187011)
    ·
      refine ⟨17565933031958832402280517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11710622021305888268187011 17565933031958832402280517)
      ·
        refine ⟨3293612443492281075427597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17565933031958832402280517 3293612443492281075427597)
        ·
          refine ⟨1235104666309605403285349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3293612443492281075427597 1235104666309605403285349)
          ·
            refine ⟨231582124933051013116003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1235104666309605403285349 231582124933051013116003)
            ·
              refine ⟨347373187399576519674005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231582124933051013116003 347373187399576519674005)
              ·
                refine ⟨16283118159355149359719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347373187399576519674005 16283118159355149359719)
                ·
                  rfl

theorem cell21_214051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 6].length) (baseStart_214051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214051 prefixEnd_214051 := by exact prefixLift 214051
  have htrace : WordTrace (prefixWord ++ tailWord_214051) baseStart_214051 baseEnd_214051 := by
    simpa [prefixWord, tailWord_214051, baseEnd_214051] using wordTrace_append hprefix tailTrace_214051
  have hstable : (prefixWord ++ tailWord_214051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214051).length < 2 ^ (prefixWord ++ tailWord_214051).sum := by decide
  have hdescent : baseEnd_214051 < baseStart_214051 := by decide
  rcases family_descends (prefixWord ++ tailWord_214051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214065 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_214065 : Nat := 118140960795 + 214065 * 2 ^ 59
def prefixEnd_214065 : Nat := 4983230072969 + 3 ^ 40 * 214065 * 2
def baseEnd_214065 : Nat := 48852549468804534845795

theorem tailTrace_214065 : CollatzResearch.WordTrace tailWord_214065 prefixEnd_214065 48852549468804534845795 := by
  unfold tailWord_214065
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807591969486539236467649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5205061312991026157645099 7807591969486539236467649)
  ·
    refine ⟨5855693977114904427350737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7807591969486539236467649 5855693977114904427350737)
    ·
      refine ⟨4391770482836178320513053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5855693977114904427350737 4391770482836178320513053)
      ·
        refine ⟨1646913931063566870192395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4391770482836178320513053 1646913931063566870192395)
        ·
          refine ⟨2470370896595350305288593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646913931063566870192395 2470370896595350305288593)
          ·
            refine ⟨1852778172446512728966445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470370896595350305288593 1852778172446512728966445)
            ·
              refine ⟨694791814667442273362417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852778172446512728966445 694791814667442273362417)
              ·
                refine ⟨521093861000581705021813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694791814667442273362417 521093861000581705021813)
                ·
                  refine ⟨48852549468804534845795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521093861000581705021813 48852549468804534845795)
                  ·
                    rfl

theorem cell21_214065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_214065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214065 prefixEnd_214065 := by exact prefixLift 214065
  have htrace : WordTrace (prefixWord ++ tailWord_214065) baseStart_214065 baseEnd_214065 := by
    simpa [prefixWord, tailWord_214065, baseEnd_214065] using wordTrace_append hprefix tailTrace_214065
  have hstable : (prefixWord ++ tailWord_214065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214065).length < 2 ^ (prefixWord ++ tailWord_214065).sum := by decide
  have hdescent : baseEnd_214065 < baseStart_214065 := by decide
  rcases family_descends (prefixWord ++ tailWord_214065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214079 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_214079 : Nat := 118140960795 + 214079 * 2 ^ 59
def prefixEnd_214079 : Nat := 4983230072969 + 3 ^ 40 * 214079 * 2
def baseEnd_214079 : Nat := 48855744459543621612433

theorem tailTrace_214079 : CollatzResearch.WordTrace tailWord_214079 prefixEnd_214079 48855744459543621612433 := by
  unfold tailWord_214079
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808102591435819627477291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5205401727623879751651527 7808102591435819627477291)
  ·
    refine ⟨11712153887153729441215937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7808102591435819627477291 11712153887153729441215937)
    ·
      refine ⟨8784115415365297080911953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11712153887153729441215937 8784115415365297080911953)
      ·
        refine ⟨6588086561523972810683965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8784115415365297080911953 6588086561523972810683965)
        ·
          refine ⟨2470532460571489804006487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6588086561523972810683965 2470532460571489804006487)
          ·
            refine ⟨3705798690857234706009731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470532460571489804006487 3705798690857234706009731)
            ·
              refine ⟨5558698036285852059014597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705798690857234706009731 5558698036285852059014597)
              ·
                refine ⟨1042255881803597261065237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5558698036285852059014597 1042255881803597261065237)
                ·
                  refine ⟨48855744459543621612433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1042255881803597261065237 48855744459543621612433)
                  ·
                    rfl

theorem cell21_214079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_214079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214079 prefixEnd_214079 := by exact prefixLift 214079
  have htrace : WordTrace (prefixWord ++ tailWord_214079) baseStart_214079 baseEnd_214079 := by
    simpa [prefixWord, tailWord_214079, baseEnd_214079] using wordTrace_append hprefix tailTrace_214079
  have hstable : (prefixWord ++ tailWord_214079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214079).length < 2 ^ (prefixWord ++ tailWord_214079).sum := by decide
  have hdescent : baseEnd_214079 < baseStart_214079 := by decide
  rcases family_descends (prefixWord ++ tailWord_214079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214133 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 3]
def baseStart_214133 : Nat := 118140960795 + 214133 * 2 ^ 59
def prefixEnd_214133 : Nat := 4983230072969 + 3 ^ 40 * 214133 * 2
def baseEnd_214133 : Nat := 48868067995251527712323

theorem tailTrace_214133 : CollatzResearch.WordTrace tailWord_214133 prefixEnd_214133 48868067995251527712323 := by
  unfold tailWord_214133
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810072133240186849943053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5206714755493457899962035 7810072133240186849943053)
  ·
    refine ⟨2928777049965070068728645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7810072133240186849943053 2928777049965070068728645)
    ·
      refine ⟨549145696868450637886621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2928777049965070068728645 549145696868450637886621)
      ·
        refine ⟨205929636325668989207483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549145696868450637886621 205929636325668989207483)
        ·
          refine ⟨308894454488503483811225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205929636325668989207483 308894454488503483811225)
          ·
            refine ⟨231670840866377612858419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308894454488503483811225 231670840866377612858419)
            ·
              refine ⟨347506261299566419287629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231670840866377612858419 347506261299566419287629)
              ·
                refine ⟨130314847987337407232861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347506261299566419287629 130314847987337407232861)
                ·
                  refine ⟨48868067995251527712323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130314847987337407232861 48868067995251527712323)
                  ·
                    rfl

theorem cell21_214133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_214133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214133 prefixEnd_214133 := by exact prefixLift 214133
  have htrace : WordTrace (prefixWord ++ tailWord_214133) baseStart_214133 baseEnd_214133 := by
    simpa [prefixWord, tailWord_214133, baseEnd_214133] using wordTrace_append hprefix tailTrace_214133
  have hstable : (prefixWord ++ tailWord_214133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214133).length < 2 ^ (prefixWord ++ tailWord_214133).sum := by decide
  have hdescent : baseEnd_214133 < baseStart_214133 := by decide
  rcases family_descends (prefixWord ++ tailWord_214133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214158 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_214158 : Nat := 118140960795 + 214158 * 2 ^ 59
def prefixEnd_214158 : Nat := 4983230072969 + 3 ^ 40 * 214158 * 2
def baseEnd_214158 : Nat := 48873773335857039795605

theorem tailTrace_214158 : CollatzResearch.WordTrace tailWord_214158 prefixEnd_214158 48873773335857039795605 := by
  unfold tailWord_214158
  simp only [CollatzResearch.WordTrace]
  refine ⟨976372994768702014950391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5207322638766410746402085 976372994768702014950391)
  ·
    refine ⟨1464559492153053022425587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976372994768702014950391 1464559492153053022425587)
    ·
      refine ⟨2196839238229579533638381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464559492153053022425587 2196839238229579533638381)
      ·
        refine ⟨823814714336092325114393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2196839238229579533638381 823814714336092325114393)
        ·
          refine ⟨617861035752069243835795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823814714336092325114393 617861035752069243835795)
          ·
            refine ⟨926791553628103865753693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617861035752069243835795 926791553628103865753693)
            ·
              refine ⟨347546832610538949657635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926791553628103865753693 347546832610538949657635)
              ·
                refine ⟨521320248915808424486453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347546832610538949657635 521320248915808424486453)
                ·
                  refine ⟨48873773335857039795605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521320248915808424486453 48873773335857039795605)
                  ·
                    rfl

theorem cell21_214158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_214158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214158 prefixEnd_214158 := by exact prefixLift 214158
  have htrace : WordTrace (prefixWord ++ tailWord_214158) baseStart_214158 baseEnd_214158 := by
    simpa [prefixWord, tailWord_214158, baseEnd_214158] using wordTrace_append hprefix tailTrace_214158
  have hstable : (prefixWord ++ tailWord_214158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214158).length < 2 ^ (prefixWord ++ tailWord_214158).sum := by decide
  have hdescent : baseEnd_214158 < baseStart_214158 := by decide
  rcases family_descends (prefixWord ++ tailWord_214158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214200 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_214200 : Nat := 118140960795 + 214200 * 2 ^ 59
def prefixEnd_214200 : Nat := 4983230072969 + 3 ^ 40 * 214200 * 2
def baseEnd_214200 : Nat := 48883358308074300095519

theorem tailTrace_214200 : CollatzResearch.WordTrace tailWord_214200 prefixEnd_214200 48883358308074300095519 := by
  unfold tailWord_214200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906257911998728646316027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5208343882664971528421369 3906257911998728646316027)
  ·
    refine ⟨5859386867998092969474041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3906257911998728646316027 5859386867998092969474041)
    ·
      refine ⟨4394540150998569727105531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5859386867998092969474041 4394540150998569727105531)
      ·
        refine ⟨6591810226497854590658297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394540150998569727105531 6591810226497854590658297)
        ·
          refine ⟨4943857669873390942993723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6591810226497854590658297 4943857669873390942993723)
          ·
            refine ⟨7415786504810086414490585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943857669873390942993723 7415786504810086414490585)
            ·
              refine ⟨5561839878607564810867939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415786504810086414490585 5561839878607564810867939)
              ·
                refine ⟨8342759817911347216301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561839878607564810867939 8342759817911347216301909)
                ·
                  refine ⟨48883358308074300095519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8342759817911347216301909 48883358308074300095519)
                  ·
                    rfl

theorem cell21_214200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_214200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214200 prefixEnd_214200 := by exact prefixLift 214200
  have htrace : WordTrace (prefixWord ++ tailWord_214200) baseStart_214200 baseEnd_214200 := by
    simpa [prefixWord, tailWord_214200, baseEnd_214200] using wordTrace_append hprefix tailTrace_214200
  have hstable : (prefixWord ++ tailWord_214200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214200).length < 2 ^ (prefixWord ++ tailWord_214200).sum := by decide
  have hdescent : baseEnd_214200 < baseStart_214200 := by decide
  rcases family_descends (prefixWord ++ tailWord_214200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214209 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 3]
def baseStart_214209 : Nat := 118140960795 + 214209 * 2 ^ 59
def prefixEnd_214209 : Nat := 4983230072969 + 3 ^ 40 * 214209 * 2
def baseEnd_214209 : Nat := 48885412230692284445501

theorem tailTrace_214209 : CollatzResearch.WordTrace tailWord_214209 prefixEnd_214209 48885412230692284445501 := by
  unfold tailWord_214209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7812844080964851829709681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5208562720643234553139787 7812844080964851829709681)
  ·
    refine ⟨5859633060723638872282261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7812844080964851829709681 5859633060723638872282261)
    ·
      refine ⟨274670299721420572138231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5859633060723638872282261 274670299721420572138231)
      ·
        refine ⟨412005449582130858207347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274670299721420572138231 412005449582130858207347)
        ·
          refine ⟨618008174373196287311021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412005449582130858207347 618008174373196287311021)
          ·
            refine ⟨231753065389948607741633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618008174373196287311021 231753065389948607741633)
            ·
              refine ⟨173814799042461455806225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231753065389948607741633 173814799042461455806225)
              ·
                refine ⟨130361099281846091854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173814799042461455806225 130361099281846091854669)
                ·
                  refine ⟨48885412230692284445501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130361099281846091854669 48885412230692284445501)
                  ·
                    rfl

theorem cell21_214209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_214209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214209 prefixEnd_214209 := by exact prefixLift 214209
  have htrace : WordTrace (prefixWord ++ tailWord_214209) baseStart_214209 baseEnd_214209 := by
    simpa [prefixWord, tailWord_214209, baseEnd_214209] using wordTrace_append hprefix tailTrace_214209
  have hstable : (prefixWord ++ tailWord_214209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214209).length < 2 ^ (prefixWord ++ tailWord_214209).sum := by decide
  have hdescent : baseEnd_214209 < baseStart_214209 := by decide
  rcases family_descends (prefixWord ++ tailWord_214209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214302 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_214302 : Nat := 118140960795 + 214302 * 2 ^ 59
def prefixEnd_214302 : Nat := 4983230072969 + 3 ^ 40 * 214302 * 2
def baseEnd_214302 : Nat := 48906636097744789395311

theorem tailTrace_214302 : CollatzResearch.WordTrace tailWord_214302 prefixEnd_214302 48906636097744789395311 := by
  unfold tailWord_214302
  simp only [CollatzResearch.WordTrace]
  refine ⟨977029508703491089105645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5210824046418619141896773 977029508703491089105645)
  ·
    refine ⟨366386065763809158414617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 977029508703491089105645 366386065763809158414617)
    ·
      refine ⟨274789549322856868810963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366386065763809158414617 274789549322856868810963)
      ·
        refine ⟨412184323984285303216445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274789549322856868810963 412184323984285303216445)
        ·
          refine ⟨154569121494106988706167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412184323984285303216445 154569121494106988706167)
          ·
            refine ⟨231853682241160483059251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154569121494106988706167 231853682241160483059251)
            ·
              refine ⟨347780523361740724588877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231853682241160483059251 347780523361740724588877)
              ·
                refine ⟨130417696260652771720829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347780523361740724588877 130417696260652771720829)
                ·
                  refine ⟨48906636097744789395311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130417696260652771720829 48906636097744789395311)
                  ·
                    rfl

theorem cell21_214302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_214302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214302 prefixEnd_214302 := by exact prefixLift 214302
  have htrace : WordTrace (prefixWord ++ tailWord_214302) baseStart_214302 baseEnd_214302 := by
    simpa [prefixWord, tailWord_214302, baseEnd_214302] using wordTrace_append hprefix tailTrace_214302
  have hstable : (prefixWord ++ tailWord_214302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214302).length < 2 ^ (prefixWord ++ tailWord_214302).sum := by decide
  have hdescent : baseEnd_214302 < baseStart_214302 := by decide
  rcases family_descends (prefixWord ++ tailWord_214302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214307 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_214307 : Nat := 118140960795 + 214307 * 2 ^ 59
def prefixEnd_214307 : Nat := 4983230072969 + 3 ^ 40 * 214307 * 2
def baseEnd_214307 : Nat := 48907777165865891811967

theorem tailTrace_214307 : CollatzResearch.WordTrace tailWord_214307 prefixEnd_214307 48907777165865891811967 := by
  unfold tailWord_214307
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816418434609814566777175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5210945623073209711184783 7816418434609814566777175)
  ·
    refine ⟨11724627651914721850165763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7816418434609814566777175 11724627651914721850165763)
    ·
      refine ⟨17586941477872082775248645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11724627651914721850165763 17586941477872082775248645)
      ·
        refine ⟨3297551527101015520359121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17586941477872082775248645 3297551527101015520359121)
        ·
          refine ⟨2473163645325761640269341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3297551527101015520359121 2473163645325761640269341)
          ·
            refine ⟨927436366997160615101003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2473163645325761640269341 927436366997160615101003)
            ·
              refine ⟨1391154550495740922651505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927436366997160615101003 1391154550495740922651505)
              ·
                refine ⟨1043365912871805691988629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391154550495740922651505 1043365912871805691988629)
                ·
                  refine ⟨48907777165865891811967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1043365912871805691988629 48907777165865891811967)
                  ·
                    rfl

theorem cell21_214307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_214307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214307 prefixEnd_214307 := by exact prefixLift 214307
  have htrace : WordTrace (prefixWord ++ tailWord_214307) baseStart_214307 baseEnd_214307 := by
    simpa [prefixWord, tailWord_214307, baseEnd_214307] using wordTrace_append hprefix tailTrace_214307
  have hstable : (prefixWord ++ tailWord_214307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214307).length < 2 ^ (prefixWord ++ tailWord_214307).sum := by decide
  have hdescent : baseEnd_214307 < baseStart_214307 := by decide
  rcases family_descends (prefixWord ++ tailWord_214307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214324 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_214324 : Nat := 118140960795 + 214324 * 2 ^ 59
def prefixEnd_214324 : Nat := 4983230072969 + 3 ^ 40 * 214324 * 2
def baseEnd_214324 : Nat := 48911656797477640028599

theorem tailTrace_214324 : CollatzResearch.WordTrace tailWord_214324 prefixEnd_214324 48911656797477640028599 := by
  unfold tailWord_214324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908519237774113235073013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5211358983698817646764017 3908519237774113235073013)
  ·
    refine ⟨366423678541323115788095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3908519237774113235073013 366423678541323115788095)
    ·
      refine ⟨549635517811984673682143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366423678541323115788095 549635517811984673682143)
      ·
        refine ⟨824453276717977010523215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549635517811984673682143 824453276717977010523215)
        ·
          refine ⟨1236679915076965515784823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824453276717977010523215 1236679915076965515784823)
          ·
            refine ⟨1855019872615448273677235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236679915076965515784823 1855019872615448273677235)
            ·
              refine ⟨2782529808923172410515853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855019872615448273677235 2782529808923172410515853)
              ·
                refine ⟨1043448678346189653943445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782529808923172410515853 1043448678346189653943445)
                ·
                  refine ⟨48911656797477640028599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1043448678346189653943445 48911656797477640028599)
                  ·
                    rfl

theorem cell21_214324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_214324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214324 prefixEnd_214324 := by exact prefixLift 214324
  have htrace : WordTrace (prefixWord ++ tailWord_214324) baseStart_214324 baseEnd_214324 := by
    simpa [prefixWord, tailWord_214324, baseEnd_214324] using wordTrace_append hprefix tailTrace_214324
  have hstable : (prefixWord ++ tailWord_214324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214324).length < 2 ^ (prefixWord ++ tailWord_214324).sum := by decide
  have hdescent : baseEnd_214324 < baseStart_214324 := by decide
  rcases family_descends (prefixWord ++ tailWord_214324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214352 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_214352 : Nat := 118140960795 + 214352 * 2 ^ 59
def prefixEnd_214352 : Nat := 4983230072969 + 3 ^ 40 * 214352 * 2
def baseEnd_214352 : Nat := 48918046778955813561875

theorem tailTrace_214352 : CollatzResearch.WordTrace tailWord_214352 prefixEnd_214352 48918046778955813561875 := by
  unfold tailWord_214352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909029859723393626082655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5212039812964524834776873 3909029859723393626082655)
  ·
    refine ⟨5863544789585090439123983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3909029859723393626082655 5863544789585090439123983)
    ·
      refine ⟨8795317184377635658685975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863544789585090439123983 8795317184377635658685975)
      ·
        refine ⟨13192975776566453488028963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795317184377635658685975 13192975776566453488028963)
        ·
          refine ⟨19789463664849680232043445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192975776566453488028963 19789463664849680232043445)
          ·
            refine ⟨1855262218579657521754073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19789463664849680232043445 1855262218579657521754073)
            ·
              refine ⟨1391446663934743141315555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855262218579657521754073 1391446663934743141315555)
              ·
                refine ⟨2087169995902114711973333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391446663934743141315555 2087169995902114711973333)
                ·
                  refine ⟨48918046778955813561875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2087169995902114711973333 48918046778955813561875)
                  ·
                    rfl

theorem cell21_214352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_214352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214352 prefixEnd_214352 := by exact prefixLift 214352
  have htrace : WordTrace (prefixWord ++ tailWord_214352) baseStart_214352 baseEnd_214352 := by
    simpa [prefixWord, tailWord_214352, baseEnd_214352] using wordTrace_append hprefix tailTrace_214352
  have hstable : (prefixWord ++ tailWord_214352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214352).length < 2 ^ (prefixWord ++ tailWord_214352).sum := by decide
  have hdescent : baseEnd_214352 < baseStart_214352 := by decide
  rcases family_descends (prefixWord ++ tailWord_214352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214386 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_214386 : Nat := 118140960795 + 214386 * 2 ^ 59
def prefixEnd_214386 : Nat := 4983230072969 + 3 ^ 40 * 214386 * 2
def baseEnd_214386 : Nat := 48925806042179309995139

theorem tailTrace_214386 : CollatzResearch.WordTrace tailWord_214386 prefixEnd_214386 48925806042179309995139 := by
  unfold tailWord_214386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954824950330902764725753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5212866534215740705935341 1954824950330902764725753)
  ·
    refine ⟨1466118712748177073544315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954824950330902764725753 1466118712748177073544315)
    ·
      refine ⟨2199178069122265610316473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466118712748177073544315 2199178069122265610316473)
      ·
        refine ⟨1649383551841699207737355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199178069122265610316473 1649383551841699207737355)
        ·
          refine ⟨2474075327762548811606033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649383551841699207737355 2474075327762548811606033)
          ·
            refine ⟨1855556495821911608704525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474075327762548811606033 1855556495821911608704525)
            ·
              refine ⟨695833685933216853264197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1855556495821911608704525 695833685933216853264197)
              ·
                refine ⟨130468816112478159987037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695833685933216853264197 130468816112478159987037)
                ·
                  refine ⟨48925806042179309995139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130468816112478159987037 48925806042179309995139)
                  ·
                    rfl

theorem cell21_214386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_214386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214386 prefixEnd_214386 := by exact prefixLift 214386
  have htrace : WordTrace (prefixWord ++ tailWord_214386) baseStart_214386 baseEnd_214386 := by
    simpa [prefixWord, tailWord_214386, baseEnd_214386] using wordTrace_append hprefix tailTrace_214386
  have hstable : (prefixWord ++ tailWord_214386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214386).length < 2 ^ (prefixWord ++ tailWord_214386).sum := by decide
  have hdescent : baseEnd_214386 < baseStart_214386 := by decide
  rcases family_descends (prefixWord ++ tailWord_214386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214490 : List Nat := [3, 1, 1, 2, 3, 4, 7]
def baseStart_214490 : Nat := 118140960795 + 214490 * 2 ^ 59
def prefixEnd_214490 : Nat := 4983230072969 + 3 ^ 40 * 214490 * 2
def baseEnd_214490 : Nat := 5438837806566471140177

theorem tailTrace_214490 : CollatzResearch.WordTrace tailWord_214490 prefixEnd_214490 5438837806566471140177 := by
  unfold tailWord_214490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955773248236709205172231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5215395328631224547125949 1955773248236709205172231)
  ·
    refine ⟨2933659872355063807758347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1955773248236709205172231 2933659872355063807758347)
    ·
      refine ⟨4400489808532595711637521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2933659872355063807758347 4400489808532595711637521)
      ·
        refine ⟨3300367356399446783728141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4400489808532595711637521 3300367356399446783728141)
        ·
          refine ⟨1237637758649792543898053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3300367356399446783728141 1237637758649792543898053)
          ·
            refine ⟨232057079746836101980885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1237637758649792543898053 232057079746836101980885)
            ·
              refine ⟨5438837806566471140177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232057079746836101980885 5438837806566471140177)
              ·
                rfl

theorem cell21_214490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 7].length) (baseStart_214490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214490 prefixEnd_214490 := by exact prefixLift 214490
  have htrace : WordTrace (prefixWord ++ tailWord_214490) baseStart_214490 baseEnd_214490 := by
    simpa [prefixWord, tailWord_214490, baseEnd_214490] using wordTrace_append hprefix tailTrace_214490
  have hstable : (prefixWord ++ tailWord_214490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214490).length < 2 ^ (prefixWord ++ tailWord_214490).sum := by decide
  have hdescent : baseEnd_214490 < baseStart_214490 := by decide
  rcases family_descends (prefixWord ++ tailWord_214490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214549 : List Nat := [1, 3, 2, 1, 3, 11]
def baseStart_214549 : Nat := 118140960795 + 214549 * 2 ^ 59
def prefixEnd_214549 : Nat := 4983230072969 + 3 ^ 40 * 214549 * 2
def baseEnd_214549 : Nat := 1813444624552861065857

theorem tailTrace_214549 : CollatzResearch.WordTrace tailWord_214549 prefixEnd_214549 1813444624552861065857 := by
  unfold tailWord_214549
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825244899733089897086701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5216829933155393264724467 7825244899733089897086701)
  ·
    refine ⟨2934466837399908711407513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7825244899733089897086701 2934466837399908711407513)
    ·
      refine ⟨2200850128049931533555635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2934466837399908711407513 2200850128049931533555635)
      ·
        refine ⟨3301275192074897300333453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200850128049931533555635 3301275192074897300333453)
        ·
          refine ⟨1237978197028086487625045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3301275192074897300333453 1237978197028086487625045)
          ·
            refine ⟨1813444624552861065857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1237978197028086487625045 1813444624552861065857)
            ·
              rfl

theorem cell21_214549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 11].length) (baseStart_214549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214549 prefixEnd_214549 := by exact prefixLift 214549
  have htrace : WordTrace (prefixWord ++ tailWord_214549) baseStart_214549 baseEnd_214549 := by
    simpa [prefixWord, tailWord_214549, baseEnd_214549] using wordTrace_append hprefix tailTrace_214549
  have hstable : (prefixWord ++ tailWord_214549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214549).length < 2 ^ (prefixWord ++ tailWord_214549).sum := by decide
  have hdescent : baseEnd_214549 < baseStart_214549 := by decide
  rcases family_descends (prefixWord ++ tailWord_214549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214558 : List Nat := [4, 3, 3, 1, 1, 2, 1, 6]
def baseStart_214558 : Nat := 118140960795 + 214558 * 2 ^ 59
def prefixEnd_214558 : Nat := 4983230072969 + 3 ^ 40 * 214558 * 2
def baseEnd_214558 : Nat := 16321686261848411042707

theorem tailTrace_214558 : CollatzResearch.WordTrace tailWord_214558 prefixEnd_214558 16321686261848411042707 := by
  unfold tailWord_214558
  simp only [CollatzResearch.WordTrace]
  refine ⟨978196644587560554270541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5217048771133656289442885 978196644587560554270541)
  ·
    refine ⟨366823741720335207851453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 978196644587560554270541 366823741720335207851453)
    ·
      refine ⟨137558903145125702944295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 366823741720335207851453 137558903145125702944295)
      ·
        refine ⟨206338354717688554416443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137558903145125702944295 206338354717688554416443)
        ·
          refine ⟨309507532076532831624665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206338354717688554416443 309507532076532831624665)
          ·
            refine ⟨232130649057399623718499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309507532076532831624665 232130649057399623718499)
            ·
              refine ⟨348195973586099435577749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232130649057399623718499 348195973586099435577749)
              ·
                refine ⟨16321686261848411042707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348195973586099435577749 16321686261848411042707)
                ·
                  rfl

theorem cell21_214558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_214558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214558 prefixEnd_214558 := by exact prefixLift 214558
  have htrace : WordTrace (prefixWord ++ tailWord_214558) baseStart_214558 baseEnd_214558 := by
    simpa [prefixWord, tailWord_214558, baseEnd_214558] using wordTrace_append hprefix tailTrace_214558
  have hstable : (prefixWord ++ tailWord_214558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214558).length < 2 ^ (prefixWord ++ tailWord_214558).sum := by decide
  have hdescent : baseEnd_214558 < baseStart_214558 := by decide
  rcases family_descends (prefixWord ++ tailWord_214558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214625 : List Nat := [1, 2, 3, 1, 1, 3, 2, 8]
def baseStart_214625 : Nat := 118140960795 + 214625 * 2 ^ 59
def prefixEnd_214625 : Nat := 4983230072969 + 3 ^ 40 * 214625 * 2
def baseEnd_214625 : Nat := 16326783032789335170439

theorem tailTrace_214625 : CollatzResearch.WordTrace tailWord_214625 prefixEnd_214625 16326783032789335170439 := by
  unfold tailWord_214625
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828016847457754876853329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5218677898305169917902219 7828016847457754876853329)
  ·
    refine ⟨5871012635593316157639997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7828016847457754876853329 5871012635593316157639997)
    ·
      refine ⟨2201629738347493559114999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5871012635593316157639997 2201629738347493559114999)
      ·
        refine ⟨3302444607521240338672499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201629738347493559114999 3302444607521240338672499)
        ·
          refine ⟨4953666911281860508008749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302444607521240338672499 4953666911281860508008749)
          ·
            refine ⟨1857625091730697690503281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4953666911281860508008749 1857625091730697690503281)
            ·
              refine ⟨1393218818798023267877461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857625091730697690503281 1393218818798023267877461)
              ·
                refine ⟨16326783032789335170439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1393218818798023267877461 16326783032789335170439)
                ·
                  rfl

theorem cell21_214625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_214625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214625 prefixEnd_214625 := by exact prefixLift 214625
  have htrace : WordTrace (prefixWord ++ tailWord_214625) baseStart_214625 baseEnd_214625 := by
    simpa [prefixWord, tailWord_214625, baseEnd_214625] using wordTrace_append hprefix tailTrace_214625
  have hstable : (prefixWord ++ tailWord_214625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214625).length < 2 ^ (prefixWord ++ tailWord_214625).sum := by decide
  have hdescent : baseEnd_214625 < baseStart_214625 := by decide
  rcases family_descends (prefixWord ++ tailWord_214625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214642 : List Nat := [3, 2, 1, 2, 3, 2, 1, 7]
def baseStart_214642 : Nat := 118140960795 + 214642 * 2 ^ 59
def prefixEnd_214642 : Nat := 4983230072969 + 3 ^ 40 * 214642 * 2
def baseEnd_214642 : Nat := 16328076243326584575983

theorem tailTrace_214642 : CollatzResearch.WordTrace tailWord_214642 prefixEnd_214642 16328076243326584575983 := by
  unfold tailWord_214642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1957159222099041695055545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5219091258930777853481453 1957159222099041695055545)
  ·
    refine ⟨1467869416574281271291659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1957159222099041695055545 1467869416574281271291659)
    ·
      refine ⟨2201804124861421906937489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467869416574281271291659 2201804124861421906937489)
      ·
        refine ⟨1651353093646066430203117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201804124861421906937489 1651353093646066430203117)
        ·
          refine ⟨619257410117274911326169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1651353093646066430203117 619257410117274911326169)
          ·
            refine ⟨464443057587956183494627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619257410117274911326169 464443057587956183494627)
            ·
              refine ⟨696664586381934275241941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464443057587956183494627 696664586381934275241941)
              ·
                refine ⟨16328076243326584575983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 696664586381934275241941 16328076243326584575983)
                ·
                  rfl

theorem cell21_214642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_214642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214642 prefixEnd_214642 := by exact prefixLift 214642
  have htrace : WordTrace (prefixWord ++ tailWord_214642) baseStart_214642 baseEnd_214642 := by
    simpa [prefixWord, tailWord_214642, baseEnd_214642] using wordTrace_append hprefix tailTrace_214642
  have hstable : (prefixWord ++ tailWord_214642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214642).length < 2 ^ (prefixWord ++ tailWord_214642).sum := by decide
  have hdescent : baseEnd_214642 < baseStart_214642 := by decide
  rcases family_descends (prefixWord ++ tailWord_214642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214766 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_214766 : Nat := 118140960795 + 214766 * 2 ^ 59
def prefixEnd_214766 : Nat := 4983230072969 + 3 ^ 40 * 214766 * 2
def baseEnd_214766 : Nat := 49012527219383093661029

theorem tailTrace_214766 : CollatzResearch.WordTrace tailWord_214766 prefixEnd_214766 49012527219383093661029 := by
  unfold tailWord_214766
  simp only [CollatzResearch.WordTrace]
  refine ⟨979144942493366994717019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5222106359964623971824101 979144942493366994717019)
  ·
    refine ⟨1468717413740050492075529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 979144942493366994717019 1468717413740050492075529)
    ·
      refine ⟨1101538060305037869056647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1468717413740050492075529 1101538060305037869056647)
      ·
        refine ⟨1652307090457556803584971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101538060305037869056647 1652307090457556803584971)
        ·
          refine ⟨2478460635686335205377457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652307090457556803584971 2478460635686335205377457)
          ·
            refine ⟨1858845476764751404033093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2478460635686335205377457 1858845476764751404033093)
            ·
              refine ⟨348533526893390888256205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1858845476764751404033093 348533526893390888256205)
              ·
                refine ⟨130700072585021583096077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348533526893390888256205 130700072585021583096077)
                ·
                  refine ⟨49012527219383093661029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130700072585021583096077 49012527219383093661029)
                  ·
                    rfl

theorem cell21_214766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_214766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214766 prefixEnd_214766 := by exact prefixLift 214766
  have htrace : WordTrace (prefixWord ++ tailWord_214766) baseStart_214766 baseEnd_214766 := by
    simpa [prefixWord, tailWord_214766, baseEnd_214766] using wordTrace_append hprefix tailTrace_214766
  have hstable : (prefixWord ++ tailWord_214766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214766).length < 2 ^ (prefixWord ++ tailWord_214766).sum := by decide
  have hdescent : baseEnd_214766 < baseStart_214766 := by decide
  rcases family_descends (prefixWord ++ tailWord_214766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214808 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_214808 : Nat := 118140960795 + 214808 * 2 ^ 59
def prefixEnd_214808 : Nat := 4983230072969 + 3 ^ 40 * 214808 * 2
def baseEnd_214808 : Nat := 49022112191600353960943

theorem tailTrace_214808 : CollatzResearch.WordTrace tailWord_214808 prefixEnd_214808 49022112191600353960943 := by
  unfold tailWord_214808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917345702897388565382539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5223127603863184753843385 3917345702897388565382539)
  ·
    refine ⟨5876018554346082848073809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3917345702897388565382539 5876018554346082848073809)
    ·
      refine ⟨4407013915759562136055357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5876018554346082848073809 4407013915759562136055357)
      ·
        refine ⟨1652630218409835801020759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4407013915759562136055357 1652630218409835801020759)
        ·
          refine ⟨2478945327614753701531139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652630218409835801020759 2478945327614753701531139)
          ·
            refine ⟨3718417991422130552296709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478945327614753701531139 3718417991422130552296709)
            ·
              refine ⟨697203373391649478555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3718417991422130552296709 697203373391649478555633)
              ·
                refine ⟨522902530043737108916725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697203373391649478555633 522902530043737108916725)
                ·
                  refine ⟨49022112191600353960943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 522902530043737108916725 49022112191600353960943)
                  ·
                    rfl

theorem cell21_214808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_214808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214808 prefixEnd_214808 := by exact prefixLift 214808
  have htrace : WordTrace (prefixWord ++ tailWord_214808) baseStart_214808 baseEnd_214808 := by
    simpa [prefixWord, tailWord_214808, baseEnd_214808] using wordTrace_append hprefix tailTrace_214808
  have hstable : (prefixWord ++ tailWord_214808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214808).length < 2 ^ (prefixWord ++ tailWord_214808).sum := by decide
  have hdescent : baseEnd_214808 < baseStart_214808 := by decide
  rcases family_descends (prefixWord ++ tailWord_214808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214853 : List Nat := [1, 3, 1, 1, 1, 2, 6, 6]
def baseStart_214853 : Nat := 118140960795 + 214853 * 2 ^ 59
def prefixEnd_214853 : Nat := 4983230072969 + 3 ^ 40 * 214853 * 2
def baseEnd_214853 : Nat := 16344127268230091903617

theorem tailTrace_214853 : CollatzResearch.WordTrace tailWord_214853 prefixEnd_214853 16344127268230091903617 := by
  unfold tailWord_214853
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836332690631749816153213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5224221793754499877435475 7836332690631749816153213)
  ·
    refine ⟨2938624758986906181057455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7836332690631749816153213 2938624758986906181057455)
    ·
      refine ⟨4407937138480359271586183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2938624758986906181057455 4407937138480359271586183)
      ·
        refine ⟨6611905707720538907379275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407937138480359271586183 6611905707720538907379275)
        ·
          refine ⟨9917858561580808361068913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611905707720538907379275 9917858561580808361068913)
          ·
            refine ⟨7438393921185606270801685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917858561580808361068913 7438393921185606270801685)
            ·
              refine ⟨348674715055575293943829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7438393921185606270801685 348674715055575293943829)
              ·
                refine ⟨16344127268230091903617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348674715055575293943829 16344127268230091903617)
                ·
                  rfl

theorem cell21_214853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_214853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214853 prefixEnd_214853 := by exact prefixLift 214853
  have htrace : WordTrace (prefixWord ++ tailWord_214853) baseStart_214853 baseEnd_214853 := by
    simpa [prefixWord, tailWord_214853, baseEnd_214853] using wordTrace_append hprefix tailTrace_214853
  have hstable : (prefixWord ++ tailWord_214853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214853).length < 2 ^ (prefixWord ++ tailWord_214853).sum := by decide
  have hdescent : baseEnd_214853 < baseStart_214853 := by decide
  rcases family_descends (prefixWord ++ tailWord_214853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214856 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_214856 : Nat := 118140960795 + 214856 * 2 ^ 59
def prefixEnd_214856 : Nat := 4983230072969 + 3 ^ 40 * 214856 * 2
def baseEnd_214856 : Nat := 49033066445562937160845

theorem tailTrace_214856 : CollatzResearch.WordTrace tailWord_214856 prefixEnd_214856 49033066445562937160845 := by
  unfold tailWord_214856
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918221054810440664256211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5224294739747254219008281 3918221054810440664256211)
  ·
    refine ⟨5877331582215660996384317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3918221054810440664256211 5877331582215660996384317)
    ·
      refine ⟨2203999343330872873644119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5877331582215660996384317 2203999343330872873644119)
      ·
        refine ⟨3305999014996309310466179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203999343330872873644119 3305999014996309310466179)
        ·
          refine ⟨4958998522494463965699269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305999014996309310466179 4958998522494463965699269)
          ·
            refine ⟨929812222967711993568613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4958998522494463965699269 929812222967711993568613)
            ·
              refine ⟨174339791806445998794115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 929812222967711993568613 174339791806445998794115)
              ·
                refine ⟨261509687709668998191173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174339791806445998794115 261509687709668998191173)
                ·
                  refine ⟨49033066445562937160845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261509687709668998191173 49033066445562937160845)
                  ·
                    rfl

theorem cell21_214856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_214856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214856 prefixEnd_214856 := by exact prefixLift 214856
  have htrace : WordTrace (prefixWord ++ tailWord_214856) baseStart_214856 baseEnd_214856 := by
    simpa [prefixWord, tailWord_214856, baseEnd_214856] using wordTrace_append hprefix tailTrace_214856
  have hstable : (prefixWord ++ tailWord_214856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214856).length < 2 ^ (prefixWord ++ tailWord_214856).sum := by decide
  have hdescent : baseEnd_214856 < baseStart_214856 := by decide
  rcases family_descends (prefixWord ++ tailWord_214856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214915 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_214915 : Nat := 118140960795 + 214915 * 2 ^ 59
def prefixEnd_214915 : Nat := 4983230072969 + 3 ^ 40 * 214915 * 2
def baseEnd_214915 : Nat := 49046531049391945677391

theorem tailTrace_214915 : CollatzResearch.WordTrace tailWord_214915 prefixEnd_214915 49046531049391945677391 := by
  unfold tailWord_214915
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838594016407134404910199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5225729344271422936606799 7838594016407134404910199)
  ·
    refine ⟨11757891024610701607365299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7838594016407134404910199 11757891024610701607365299)
    ·
      refine ⟨17636836536916052411047949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11757891024610701607365299 17636836536916052411047949)
      ·
        refine ⟨6613813701343519654142981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17636836536916052411047949 6613813701343519654142981)
        ·
          refine ⟨1240090069001909935151809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6613813701343519654142981 1240090069001909935151809)
          ·
            refine ⟨930067551751432451363857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240090069001909935151809 930067551751432451363857)
            ·
              refine ⟨697550663813574338522893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930067551751432451363857 697550663813574338522893)
              ·
                refine ⟨261581498930090376946085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697550663813574338522893 261581498930090376946085)
                ·
                  refine ⟨49046531049391945677391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261581498930090376946085 49046531049391945677391)
                  ·
                    rfl

theorem cell21_214915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_214915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214915 prefixEnd_214915 := by exact prefixLift 214915
  have htrace : WordTrace (prefixWord ++ tailWord_214915) baseStart_214915 baseEnd_214915 := by
    simpa [prefixWord, tailWord_214915, baseEnd_214915] using wordTrace_append hprefix tailTrace_214915
  have hstable : (prefixWord ++ tailWord_214915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214915).length < 2 ^ (prefixWord ++ tailWord_214915).sum := by decide
  have hdescent : baseEnd_214915 < baseStart_214915 := by decide
  rcases family_descends (prefixWord ++ tailWord_214915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214946 : List Nat := [3, 3, 1, 2, 3, 1, 8]
def baseStart_214946 : Nat := 118140960795 + 214946 * 2 ^ 59
def prefixEnd_214946 : Nat := 4983230072969 + 3 ^ 40 * 214946 * 2
def baseEnd_214946 : Nat := 5450400630193642295629

theorem tailTrace_214946 : CollatzResearch.WordTrace tailWord_214946 prefixEnd_214946 5450400630193642295629 := by
  unfold tailWord_214946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959931169823706674822173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5226483119529884466192461 1959931169823706674822173)
  ·
    refine ⟨734974188683890003058315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1959931169823706674822173 734974188683890003058315)
    ·
      refine ⟨1102461283025835004587473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734974188683890003058315 1102461283025835004587473)
      ·
        refine ⟨826845962269376253440605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1102461283025835004587473 826845962269376253440605)
        ·
          refine ⟨310067235851016095040227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 826845962269376253440605 310067235851016095040227)
          ·
            refine ⟨465100853776524142560341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310067235851016095040227 465100853776524142560341)
            ·
              refine ⟨5450400630193642295629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 465100853776524142560341 5450400630193642295629)
              ·
                rfl

theorem cell21_214946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 8].length) (baseStart_214946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_214946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_214946 prefixEnd_214946 := by exact prefixLift 214946
  have htrace : WordTrace (prefixWord ++ tailWord_214946) baseStart_214946 baseEnd_214946 := by
    simpa [prefixWord, tailWord_214946, baseEnd_214946] using wordTrace_append hprefix tailTrace_214946
  have hstable : (prefixWord ++ tailWord_214946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214946).length < 2 ^ (prefixWord ++ tailWord_214946).sum := by decide
  have hdescent : baseEnd_214946 < baseStart_214946 := by decide
  rcases family_descends (prefixWord ++ tailWord_214946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215022 : List Nat := [4, 1, 2, 1, 3, 2, 2, 6]
def baseStart_215022 : Nat := 118140960795 + 215022 * 2 ^ 59
def prefixEnd_215022 : Nat := 4983230072969 + 3 ^ 40 * 215022 * 2
def baseEnd_215022 : Nat := 16356983302394512464613

theorem tailTrace_215022 : CollatzResearch.WordTrace tailWord_215022 prefixEnd_215022 16356983302394512464613 := by
  unfold tailWord_215022
  simp only [CollatzResearch.WordTrace]
  refine ⟨980312078377436459881915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5228331084679661119370213 980312078377436459881915)
  ·
    refine ⟨1470468117566154689822873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980312078377436459881915 1470468117566154689822873)
    ·
      refine ⟨1102851088174616017367155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1470468117566154689822873 1102851088174616017367155)
      ·
        refine ⟨1654276632261924026050733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102851088174616017367155 1654276632261924026050733)
        ·
          refine ⟨620353737098221509769025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1654276632261924026050733 620353737098221509769025)
          ·
            refine ⟨465265302823666132326769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620353737098221509769025 465265302823666132326769)
            ·
              refine ⟨348948977117749599245077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465265302823666132326769 348948977117749599245077)
              ·
                refine ⟨16356983302394512464613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348948977117749599245077 16356983302394512464613)
                ·
                  rfl

theorem cell21_215022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_215022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215022 prefixEnd_215022 := by exact prefixLift 215022
  have htrace : WordTrace (prefixWord ++ tailWord_215022) baseStart_215022 baseEnd_215022 := by
    simpa [prefixWord, tailWord_215022, baseEnd_215022] using wordTrace_append hprefix tailTrace_215022
  have hstable : (prefixWord ++ tailWord_215022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215022).length < 2 ^ (prefixWord ++ tailWord_215022).sum := by decide
  have hdescent : baseEnd_215022 < baseStart_215022 := by decide
  rcases family_descends (prefixWord ++ tailWord_215022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215025 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 4]
def baseStart_215025 : Nat := 118140960795 + 215025 * 2 ^ 59
def prefixEnd_215025 : Nat := 4983230072969 + 3 ^ 40 * 215025 * 2
def baseEnd_215025 : Nat := 49071634548056198843833

theorem tailTrace_215025 : CollatzResearch.WordTrace tailWord_215025 prefixEnd_215025 49071634548056198843833 := by
  unfold tailWord_215025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842606046008623191414529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5228404030672415460943019 7842606046008623191414529)
  ·
    refine ⟨5881954534506467393560897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7842606046008623191414529 5881954534506467393560897)
    ·
      refine ⟨4411465900879850545170673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5881954534506467393560897 4411465900879850545170673)
      ·
        refine ⟨3308599425659887908878005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4411465900879850545170673 3308599425659887908878005)
        ·
          refine ⟨310181196155614491457313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3308599425659887908878005 310181196155614491457313)
          ·
            refine ⟨232635897116710868592985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310181196155614491457313 232635897116710868592985)
            ·
              refine ⟨174476922837533151444739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232635897116710868592985 174476922837533151444739)
              ·
                refine ⟨261715384256299727167109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174476922837533151444739 261715384256299727167109)
                ·
                  refine ⟨49071634548056198843833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261715384256299727167109 49071634548056198843833)
                  ·
                    rfl

theorem cell21_215025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 4].length) (baseStart_215025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215025 prefixEnd_215025 := by exact prefixLift 215025
  have htrace : WordTrace (prefixWord ++ tailWord_215025) baseStart_215025 baseEnd_215025 := by
    simpa [prefixWord, tailWord_215025, baseEnd_215025] using wordTrace_append hprefix tailTrace_215025
  have hstable : (prefixWord ++ tailWord_215025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215025).length < 2 ^ (prefixWord ++ tailWord_215025).sum := by decide
  have hdescent : baseEnd_215025 < baseStart_215025 := by decide
  rcases family_descends (prefixWord ++ tailWord_215025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215095 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_215095 : Nat := 118140960795 + 215095 * 2 ^ 59
def prefixEnd_215095 : Nat := 4983230072969 + 3 ^ 40 * 215095 * 2
def baseEnd_215095 : Nat := 49087609501751632677023

theorem tailTrace_215095 : CollatzResearch.WordTrace tailWord_215095 prefixEnd_215095 49087609501751632677023 := by
  unfold tailWord_215095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845159155755025146462739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5230106103836683430975159 7845159155755025146462739)
  ·
    refine ⟨11767738733632537719694109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7845159155755025146462739 11767738733632537719694109)
    ·
      refine ⟨4412902025112201644885291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11767738733632537719694109 4412902025112201644885291)
      ·
        refine ⟨6619353037668302467327937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412902025112201644885291 6619353037668302467327937)
        ·
          refine ⟨4964514778251226850495953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6619353037668302467327937 4964514778251226850495953)
          ·
            refine ⟨3723386083688420137871965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4964514778251226850495953 3723386083688420137871965)
            ·
              refine ⟨1396269781383157551701987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3723386083688420137871965 1396269781383157551701987)
              ·
                refine ⟨2094404672074736327552981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396269781383157551701987 2094404672074736327552981)
                ·
                  refine ⟨49087609501751632677023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2094404672074736327552981 49087609501751632677023)
                  ·
                    rfl

theorem cell21_215095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_215095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215095 prefixEnd_215095 := by exact prefixLift 215095
  have htrace : WordTrace (prefixWord ++ tailWord_215095) baseStart_215095 baseEnd_215095 := by
    simpa [prefixWord, tailWord_215095, baseEnd_215095] using wordTrace_append hprefix tailTrace_215095
  have hstable : (prefixWord ++ tailWord_215095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215095).length < 2 ^ (prefixWord ++ tailWord_215095).sum := by decide
  have hdescent : baseEnd_215095 < baseStart_215095 := by decide
  rcases family_descends (prefixWord ++ tailWord_215095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215194 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_215194 : Nat := 118140960795 + 215194 * 2 ^ 59
def prefixEnd_215194 : Nat := 4983230072969 + 3 ^ 40 * 215194 * 2
def baseEnd_215194 : Nat := 49110202650549460526821

theorem tailTrace_215194 : CollatzResearch.WordTrace tailWord_215194 prefixEnd_215194 49110202650549460526821 := by
  unfold tailWord_215194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962192495599091263579159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5232513321597576702877757 1962192495599091263579159)
  ·
    refine ⟨2943288743398636895368739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962192495599091263579159 2943288743398636895368739)
    ·
      refine ⟨4414933115097955343053109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943288743398636895368739 4414933115097955343053109)
      ·
        refine ⟨413899979540433313411229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4414933115097955343053109 413899979540433313411229)
        ·
          refine ⟨155212492327662492529211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413899979540433313411229 155212492327662492529211)
          ·
            refine ⟨232818738491493738793817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155212492327662492529211 232818738491493738793817)
            ·
              refine ⟨174614053868620304095363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232818738491493738793817 174614053868620304095363)
              ·
                refine ⟨261921080802930456143045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174614053868620304095363 261921080802930456143045)
                ·
                  refine ⟨49110202650549460526821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261921080802930456143045 49110202650549460526821)
                  ·
                    rfl

theorem cell21_215194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_215194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215194 prefixEnd_215194 := by exact prefixLift 215194
  have htrace : WordTrace (prefixWord ++ tailWord_215194) baseStart_215194 baseEnd_215194 := by
    simpa [prefixWord, tailWord_215194, baseEnd_215194] using wordTrace_append hprefix tailTrace_215194
  have hstable : (prefixWord ++ tailWord_215194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215194).length < 2 ^ (prefixWord ++ tailWord_215194).sum := by decide
  have hdescent : baseEnd_215194 < baseStart_215194 := by decide
  rcases family_descends (prefixWord ++ tailWord_215194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215233 : List Nat := [1, 2, 6, 1, 11]
def baseStart_215233 : Nat := 118140960795 + 215233 * 2 ^ 59
def prefixEnd_215233 : Nat := 4983230072969 + 3 ^ 40 * 215233 * 2
def baseEnd_215233 : Nat := 606408678788815547861

theorem tailTrace_215233 : CollatzResearch.WordTrace tailWord_215233 prefixEnd_215233 606408678788815547861 := by
  unfold tailWord_215233
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850192429255074714986353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5233461619503383143324235 7850192429255074714986353)
  ·
    refine ⟨5887644321941306036239765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7850192429255074714986353 5887644321941306036239765)
    ·
      refine ⟨275983327590998720448739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5887644321941306036239765 275983327590998720448739)
      ·
        refine ⟨413974991386498080673109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275983327590998720448739 413974991386498080673109)
        ·
          refine ⟨606408678788815547861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 413974991386498080673109 606408678788815547861)
          ·
            rfl

theorem cell21_215233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 11].length) (baseStart_215233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215233 prefixEnd_215233 := by exact prefixLift 215233
  have htrace : WordTrace (prefixWord ++ tailWord_215233) baseStart_215233 baseEnd_215233 := by
    simpa [prefixWord, tailWord_215233, baseEnd_215233] using wordTrace_append hprefix tailTrace_215233
  have hstable : (prefixWord ++ tailWord_215233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215233).length < 2 ^ (prefixWord ++ tailWord_215233).sum := by decide
  have hdescent : baseEnd_215233 < baseStart_215233 := by decide
  rcases family_descends (prefixWord ++ tailWord_215233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215236 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_215236 : Nat := 118140960795 + 215236 * 2 ^ 59
def prefixEnd_215236 : Nat := 4983230072969 + 3 ^ 40 * 215236 * 2
def baseEnd_215236 : Nat := 49119787622766720826735

theorem tailTrace_215236 : CollatzResearch.WordTrace tailWord_215236 prefixEnd_215236 49119787622766720826735 := by
  unfold tailWord_215236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925150924122103113672781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5233534565496137484897041 3925150924122103113672781)
  ·
    refine ⟨1471931596545788667627293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3925150924122103113672781 1471931596545788667627293)
    ·
      refine ⟨551974348704670750360235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1471931596545788667627293 551974348704670750360235)
      ·
        refine ⟨827961523057006125540353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551974348704670750360235 827961523057006125540353)
        ·
          refine ⟨620971142292754594155265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827961523057006125540353 620971142292754594155265)
          ·
            refine ⟨465728356719565945616449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620971142292754594155265 465728356719565945616449)
            ·
              refine ⟨349296267539674459212337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465728356719565945616449 349296267539674459212337)
              ·
                refine ⟨261972200654755844409253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349296267539674459212337 261972200654755844409253)
                ·
                  refine ⟨49119787622766720826735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261972200654755844409253 49119787622766720826735)
                  ·
                    rfl

theorem cell21_215236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_215236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215236 prefixEnd_215236 := by exact prefixLift 215236
  have htrace : WordTrace (prefixWord ++ tailWord_215236) baseStart_215236 baseEnd_215236 := by
    simpa [prefixWord, tailWord_215236, baseEnd_215236] using wordTrace_append hprefix tailTrace_215236
  have hstable : (prefixWord ++ tailWord_215236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215236).length < 2 ^ (prefixWord ++ tailWord_215236).sum := by decide
  have hdescent : baseEnd_215236 < baseStart_215236 := by decide
  rcases family_descends (prefixWord ++ tailWord_215236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215247 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_215247 : Nat := 118140960795 + 215247 * 2 ^ 59
def prefixEnd_215247 : Nat := 4983230072969 + 3 ^ 40 * 215247 * 2
def baseEnd_215247 : Nat := 49122297972633146143379

theorem tailTrace_215247 : CollatzResearch.WordTrace tailWord_215247 prefixEnd_215247 49122297972633146143379 := by
  unfold tailWord_215247
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850703051204355105995995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5233802034136236737330663 7850703051204355105995995)
  ·
    refine ⟨11776054576806532658993993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850703051204355105995995 11776054576806532658993993)
    ·
      refine ⟨8832040932604899494245495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11776054576806532658993993 8832040932604899494245495)
      ·
        refine ⟨13248061398907349241368243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8832040932604899494245495 13248061398907349241368243)
        ·
          refine ⟨19872092098361023862052365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13248061398907349241368243 19872092098361023862052365)
          ·
            refine ⟨7452034536885383948269637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19872092098361023862052365 7452034536885383948269637)
            ·
              refine ⟨1397256475666009490300557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7452034536885383948269637 1397256475666009490300557)
              ·
                refine ⟨523971178374753558862709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1397256475666009490300557 523971178374753558862709)
                ·
                  refine ⟨49122297972633146143379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523971178374753558862709 49122297972633146143379)
                  ·
                    rfl

theorem cell21_215247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_215247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215247 prefixEnd_215247 := by exact prefixLift 215247
  have htrace : WordTrace (prefixWord ++ tailWord_215247) baseStart_215247 baseEnd_215247 := by
    simpa [prefixWord, tailWord_215247, baseEnd_215247] using wordTrace_append hprefix tailTrace_215247
  have hstable : (prefixWord ++ tailWord_215247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215247).length < 2 ^ (prefixWord ++ tailWord_215247).sum := by decide
  have hdescent : baseEnd_215247 < baseStart_215247 := by decide
  rcases family_descends (prefixWord ++ tailWord_215247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215250 : List Nat := [3, 2, 2, 2, 1, 4, 1, 6]
def baseStart_215250 : Nat := 118140960795 + 215250 * 2 ^ 59
def prefixEnd_215250 : Nat := 4983230072969 + 3 ^ 40 * 215250 * 2
def baseEnd_215250 : Nat := 16374327537835269197791

theorem tailTrace_215250 : CollatzResearch.WordTrace tailWord_215250 prefixEnd_215250 16374327537835269197791 := by
  unfold tailWord_215250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962703117548371654588801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5233874980128991078903469 1962703117548371654588801)
  ·
    refine ⟨1472027338161278740941601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1962703117548371654588801 1472027338161278740941601)
    ·
      refine ⟨1104020503620959055706201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1472027338161278740941601 1104020503620959055706201)
      ·
        refine ⟨828015377715719291779651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104020503620959055706201 828015377715719291779651)
        ·
          refine ⟨1242023066573578937669477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828015377715719291779651 1242023066573578937669477)
          ·
            refine ⟨232879324982546050813027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1242023066573578937669477 232879324982546050813027)
            ·
              refine ⟨349318987473819076219541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232879324982546050813027 349318987473819076219541)
              ·
                refine ⟨16374327537835269197791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 349318987473819076219541 16374327537835269197791)
                ·
                  rfl

theorem cell21_215250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_215250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215250 prefixEnd_215250 := by exact prefixLift 215250
  have htrace : WordTrace (prefixWord ++ tailWord_215250) baseStart_215250 baseEnd_215250 := by
    simpa [prefixWord, tailWord_215250, baseEnd_215250] using wordTrace_append hprefix tailTrace_215250
  have hstable : (prefixWord ++ tailWord_215250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215250).length < 2 ^ (prefixWord ++ tailWord_215250).sum := by decide
  have hdescent : baseEnd_215250 < baseStart_215250 := by decide
  rcases family_descends (prefixWord ++ tailWord_215250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215267 : List Nat := [1, 1, 1, 8, 1, 1, 3, 5]
def baseStart_215267 : Nat := 118140960795 + 215267 * 2 ^ 59
def prefixEnd_215267 : Nat := 4983230072969 + 3 ^ 40 * 215267 * 2
def baseEnd_215267 : Nat := 16375620748372518603335

theorem tailTrace_215267 : CollatzResearch.WordTrace tailWord_215267 prefixEnd_215267 16375620748372518603335 := by
  unfold tailWord_215267
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851432511131898521724055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5234288340754599014482703 7851432511131898521724055)
  ·
    refine ⟨11777148766697847782586083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7851432511131898521724055 11777148766697847782586083)
    ·
      refine ⟨17665723150046771673879125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11777148766697847782586083 17665723150046771673879125)
      ·
        refine ⟨207020193164610605553271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 17665723150046771673879125 207020193164610605553271)
        ·
          refine ⟨310530289746915908329907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207020193164610605553271 310530289746915908329907)
          ·
            refine ⟨465795434620373862494861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310530289746915908329907 465795434620373862494861)
            ·
              refine ⟨174673287982640198435573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465795434620373862494861 174673287982640198435573)
              ·
                refine ⟨16375620748372518603335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174673287982640198435573 16375620748372518603335)
                ·
                  rfl

theorem cell21_215267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 5].length) (baseStart_215267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215267 prefixEnd_215267 := by exact prefixLift 215267
  have htrace : WordTrace (prefixWord ++ tailWord_215267) baseStart_215267 baseEnd_215267 := by
    simpa [prefixWord, tailWord_215267, baseEnd_215267] using wordTrace_append hprefix tailTrace_215267
  have hstable : (prefixWord ++ tailWord_215267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215267).length < 2 ^ (prefixWord ++ tailWord_215267).sum := by decide
  have hdescent : baseEnd_215267 < baseStart_215267 := by decide
  rcases family_descends (prefixWord ++ tailWord_215267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215278 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_215278 : Nat := 118140960795 + 215278 * 2 ^ 59
def prefixEnd_215278 : Nat := 4983230072969 + 3 ^ 40 * 215278 * 2
def baseEnd_215278 : Nat := 49129372594983981126649

theorem tailTrace_215278 : CollatzResearch.WordTrace tailWord_215278 prefixEnd_215278 49129372594983981126649 := by
  unfold tailWord_215278
  simp only [CollatzResearch.WordTrace]
  refine ⟨981479214261505925046811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5234555809394698266916325 981479214261505925046811)
  ·
    refine ⟨1472218821392258887570217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981479214261505925046811 1472218821392258887570217)
    ·
      refine ⟨1104164116044194165677663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1472218821392258887570217 1104164116044194165677663)
      ·
        refine ⟨1656246174066291248516495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104164116044194165677663 1656246174066291248516495)
        ·
          refine ⟨2484369261099436872774743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656246174066291248516495 2484369261099436872774743)
          ·
            refine ⟨3726553891649155309162115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484369261099436872774743 3726553891649155309162115)
            ·
              refine ⟨5589830837473732963743173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726553891649155309162115 5589830837473732963743173)
              ·
                refine ⟨1048093282026324930701845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5589830837473732963743173 1048093282026324930701845)
                ·
                  refine ⟨49129372594983981126649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1048093282026324930701845 49129372594983981126649)
                  ·
                    rfl

theorem cell21_215278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_215278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215278 prefixEnd_215278 := by exact prefixLift 215278
  have htrace : WordTrace (prefixWord ++ tailWord_215278) baseStart_215278 baseEnd_215278 := by
    simpa [prefixWord, tailWord_215278, baseEnd_215278] using wordTrace_append hprefix tailTrace_215278
  have hstable : (prefixWord ++ tailWord_215278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215278).length < 2 ^ (prefixWord ++ tailWord_215278).sum := by decide
  have hdescent : baseEnd_215278 < baseStart_215278 := by decide
  rcases family_descends (prefixWord ++ tailWord_215278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215298 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_215298 : Nat := 118140960795 + 215298 * 2 ^ 59
def prefixEnd_215298 : Nat := 4983230072969 + 3 ^ 40 * 215298 * 2
def baseEnd_215298 : Nat := 49133936867468390793275

theorem tailTrace_215298 : CollatzResearch.WordTrace tailWord_215298 prefixEnd_215298 49133936867468390793275 := by
  unfold tailWord_215298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963140793504897704025637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5235042116013060544068365 1963140793504897704025637)
  ·
    refine ⟨368088898782168319504807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1963140793504897704025637 368088898782168319504807)
    ·
      refine ⟨552133348173252479257211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368088898782168319504807 552133348173252479257211)
      ·
        refine ⟨828200022259878718885817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552133348173252479257211 828200022259878718885817)
        ·
          refine ⟨621150016694909039164363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828200022259878718885817 621150016694909039164363)
          ·
            refine ⟨931725025042363558746545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621150016694909039164363 931725025042363558746545)
            ·
              refine ⟨698793768781772669059909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931725025042363558746545 698793768781772669059909)
              ·
                refine ⟨131023831646582375448733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 698793768781772669059909 131023831646582375448733)
                ·
                  refine ⟨49133936867468390793275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131023831646582375448733 49133936867468390793275)
                  ·
                    rfl

theorem cell21_215298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_215298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215298 prefixEnd_215298 := by exact prefixLift 215298
  have htrace : WordTrace (prefixWord ++ tailWord_215298) baseStart_215298 baseEnd_215298 := by
    simpa [prefixWord, tailWord_215298, baseEnd_215298] using wordTrace_append hprefix tailTrace_215298
  have hstable : (prefixWord ++ tailWord_215298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215298).length < 2 ^ (prefixWord ++ tailWord_215298).sum := by decide
  have hdescent : baseEnd_215298 < baseStart_215298 := by decide
  rcases family_descends (prefixWord ++ tailWord_215298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215323 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_215323 : Nat := 118140960795 + 215323 * 2 ^ 59
def prefixEnd_215323 : Nat := 4983230072969 + 3 ^ 40 * 215323 * 2
def baseEnd_215323 : Nat := 49139642208073902876557

theorem tailTrace_215323 : CollatzResearch.WordTrace tailWord_215323 prefixEnd_215323 49139642208073902876557 := by
  unfold tailWord_215323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853474998929020085762623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5235649999286013390508415 7853474998929020085762623)
  ·
    refine ⟨11780212498393530128643935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853474998929020085762623 11780212498393530128643935)
    ·
      refine ⟨17670318747590295192965903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11780212498393530128643935 17670318747590295192965903)
      ·
        refine ⟨26505478121385442789448855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17670318747590295192965903 26505478121385442789448855)
        ·
          refine ⟨39758217182078164184173283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26505478121385442789448855 39758217182078164184173283)
          ·
            refine ⟨59637325773117246276259925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39758217182078164184173283 59637325773117246276259925)
            ·
              refine ⟨698874911403717729799921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 59637325773117246276259925 698874911403717729799921)
              ·
                refine ⟨524156183552788297349941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698874911403717729799921 524156183552788297349941)
                ·
                  refine ⟨49139642208073902876557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524156183552788297349941 49139642208073902876557)
                  ·
                    rfl

theorem cell21_215323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_215323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215323 prefixEnd_215323 := by exact prefixLift 215323
  have htrace : WordTrace (prefixWord ++ tailWord_215323) baseStart_215323 baseEnd_215323 := by
    simpa [prefixWord, tailWord_215323, baseEnd_215323] using wordTrace_append hprefix tailTrace_215323
  have hstable : (prefixWord ++ tailWord_215323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215323).length < 2 ^ (prefixWord ++ tailWord_215323).sum := by decide
  have hdescent : baseEnd_215323 < baseStart_215323 := by decide
  rcases family_descends (prefixWord ++ tailWord_215323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215354 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_215354 : Nat := 118140960795 + 215354 * 2 ^ 59
def prefixEnd_215354 : Nat := 4983230072969 + 3 ^ 40 * 215354 * 2
def baseEnd_215354 : Nat := 49146716830424737859827

theorem tailTrace_215354 : CollatzResearch.WordTrace tailWord_215354 prefixEnd_215354 49146716830424737859827 := by
  unfold tailWord_215354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963651415454178095035279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5236403774544474920094077 1963651415454178095035279)
  ·
    refine ⟨2945477123181267142552919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1963651415454178095035279 2945477123181267142552919)
    ·
      refine ⟨4418215684771900713829379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2945477123181267142552919 4418215684771900713829379)
      ·
        refine ⟨6627323527157851070744069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418215684771900713829379 6627323527157851070744069)
        ·
          refine ⟨1242623161342097075764513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6627323527157851070744069 1242623161342097075764513)
          ·
            refine ⟨931967371006572806823385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242623161342097075764513 931967371006572806823385)
            ·
              refine ⟨698975528254929605117539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931967371006572806823385 698975528254929605117539)
              ·
                refine ⟨1048463292382394407676309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698975528254929605117539 1048463292382394407676309)
                ·
                  refine ⟨49146716830424737859827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1048463292382394407676309 49146716830424737859827)
                  ·
                    rfl

theorem cell21_215354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_215354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215354 prefixEnd_215354 := by exact prefixLift 215354
  have htrace : WordTrace (prefixWord ++ tailWord_215354) baseStart_215354 baseEnd_215354 := by
    simpa [prefixWord, tailWord_215354, baseEnd_215354] using wordTrace_append hprefix tailTrace_215354
  have hstable : (prefixWord ++ tailWord_215354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215354).length < 2 ^ (prefixWord ++ tailWord_215354).sum := by decide
  have hdescent : baseEnd_215354 < baseStart_215354 := by decide
  rcases family_descends (prefixWord ++ tailWord_215354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215368 : List Nat := [2, 1, 3, 1, 1, 2, 3, 8]
def baseStart_215368 : Nat := 118140960795 + 215368 * 2 ^ 59
def prefixEnd_215368 : Nat := 4983230072969 + 3 ^ 40 * 215368 * 2
def baseEnd_215368 : Nat := 16383303940387941542155

theorem tailTrace_215368 : CollatzResearch.WordTrace tailWord_215368 prefixEnd_215368 16383303940387941542155 := by
  unfold tailWord_215368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927558141882996385575379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5236744189177328514100505 3927558141882996385575379)
  ·
    refine ⟨5891337212824494578363069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3927558141882996385575379 5891337212824494578363069)
    ·
      refine ⟨2209251454809185466886151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5891337212824494578363069 2209251454809185466886151)
      ·
        refine ⟨3313877182213778200329227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209251454809185466886151 3313877182213778200329227)
        ·
          refine ⟨4970815773320667300493841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3313877182213778200329227 4970815773320667300493841)
          ·
            refine ⟨3728111829990500475370381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970815773320667300493841 3728111829990500475370381)
            ·
              refine ⟨1398041936246437678263893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3728111829990500475370381 1398041936246437678263893)
              ·
                refine ⟨16383303940387941542155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1398041936246437678263893 16383303940387941542155)
                ·
                  rfl

theorem cell21_215368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_215368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215368 prefixEnd_215368 := by exact prefixLift 215368
  have htrace : WordTrace (prefixWord ++ tailWord_215368) baseStart_215368 baseEnd_215368 := by
    simpa [prefixWord, tailWord_215368, baseEnd_215368] using wordTrace_append hprefix tailTrace_215368
  have hstable : (prefixWord ++ tailWord_215368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215368).length < 2 ^ (prefixWord ++ tailWord_215368).sum := by decide
  have hdescent : baseEnd_215368 < baseStart_215368 := by decide
  rcases family_descends (prefixWord ++ tailWord_215368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215464 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_215464 : Nat := 118140960795 + 215464 * 2 ^ 59
def prefixEnd_215464 : Nat := 4983230072969 + 3 ^ 40 * 215464 * 2
def baseEnd_215464 : Nat := 49171820329088991026269

theorem tailTrace_215464 : CollatzResearch.WordTrace tailWord_215464 prefixEnd_215464 49171820329088991026269 := by
  unfold tailWord_215464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929308845709100583322723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5239078460945467444430297 3929308845709100583322723)
  ·
    refine ⟨5893963268563650874984085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3929308845709100583322723 5893963268563650874984085)
    ·
      refine ⟨276279528213921134764879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5893963268563650874984085 276279528213921134764879)
      ·
        refine ⟨414419292320881702147319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276279528213921134764879 414419292320881702147319)
        ·
          refine ⟨621628938481322553220979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414419292320881702147319 621628938481322553220979)
          ·
            refine ⟨932443407721983829831469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621628938481322553220979 932443407721983829831469)
            ·
              refine ⟨349666277895743936186801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932443407721983829831469 349666277895743936186801)
              ·
                refine ⟨262249708421807952140101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349666277895743936186801 262249708421807952140101)
                ·
                  refine ⟨49171820329088991026269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262249708421807952140101 49171820329088991026269)
                  ·
                    rfl

theorem cell21_215464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_215464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215464 prefixEnd_215464 := by exact prefixLift 215464
  have htrace : WordTrace (prefixWord ++ tailWord_215464) baseStart_215464 baseEnd_215464 := by
    simpa [prefixWord, tailWord_215464, baseEnd_215464] using wordTrace_append hprefix tailTrace_215464
  have hstable : (prefixWord ++ tailWord_215464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215464).length < 2 ^ (prefixWord ++ tailWord_215464).sum := by decide
  have hdescent : baseEnd_215464 < baseStart_215464 := by decide
  rcases family_descends (prefixWord ++ tailWord_215464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215509 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 3]
def baseStart_215509 : Nat := 118140960795 + 215509 * 2 ^ 59
def prefixEnd_215509 : Nat := 4983230072969 + 3 ^ 40 * 215509 * 2
def baseEnd_215509 : Nat := 49182089942178912776177

theorem tailTrace_215509 : CollatzResearch.WordTrace tailWord_215509 prefixEnd_215509 49182089942178912776177 := by
  unfold tailWord_215509
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860258976255173852033581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5240172650836782568022387 7860258976255173852033581)
  ·
    refine ⟨2947597116095690194512593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7860258976255173852033581 2947597116095690194512593)
    ·
      refine ⟨2210697837071767645884445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947597116095690194512593 2210697837071767645884445)
      ·
        refine ⟨829011688901912867206667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2210697837071767645884445 829011688901912867206667)
        ·
          refine ⟨1243517533352869300810001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829011688901912867206667 1243517533352869300810001)
          ·
            refine ⟨932638150014651975607501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243517533352869300810001 932638150014651975607501)
            ·
              refine ⟨349739306255494490852813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 932638150014651975607501 349739306255494490852813)
              ·
                refine ⟨131152239845810434069805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349739306255494490852813 131152239845810434069805)
                ·
                  refine ⟨49182089942178912776177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131152239845810434069805 49182089942178912776177)
                  ·
                    rfl

theorem cell21_215509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_215509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215509 prefixEnd_215509 := by exact prefixLift 215509
  have htrace : WordTrace (prefixWord ++ tailWord_215509) baseStart_215509 baseEnd_215509 := by
    simpa [prefixWord, tailWord_215509, baseEnd_215509] using wordTrace_append hprefix tailTrace_215509
  have hstable : (prefixWord ++ tailWord_215509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215509).length < 2 ^ (prefixWord ++ tailWord_215509).sum := by decide
  have hdescent : baseEnd_215509 < baseStart_215509 := by decide
  rcases family_descends (prefixWord ++ tailWord_215509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215706 : List Nat := [3, 1, 1, 6, 1, 1, 2, 6]
def baseStart_215706 : Nat := 118140960795 + 215706 * 2 ^ 59
def prefixEnd_215706 : Nat := 4983230072969 + 3 ^ 40 * 215706 * 2
def baseEnd_215706 : Nat := 16409016008716782664147

theorem tailTrace_215706 : CollatzResearch.WordTrace tailWord_215706 prefixEnd_215706 16409016008716782664147 := by
  unfold tailWord_215706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966861039135369124238743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5244962771027650997969981 1966861039135369124238743)
  ·
    refine ⟨2950291558703053686358115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1966861039135369124238743 2950291558703053686358115)
    ·
      refine ⟨4425437338054580529537173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950291558703053686358115 4425437338054580529537173)
      ·
        refine ⟨207442375221308462322055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4425437338054580529537173 207442375221308462322055)
        ·
          refine ⟨311163562831962693483083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207442375221308462322055 311163562831962693483083)
          ·
            refine ⟨466745344247944040224625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311163562831962693483083 466745344247944040224625)
            ·
              refine ⟨350059008185958030168469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466745344247944040224625 350059008185958030168469)
              ·
                refine ⟨16409016008716782664147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 350059008185958030168469 16409016008716782664147)
                ·
                  rfl

theorem cell21_215706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_215706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215706 prefixEnd_215706 := by exact prefixLift 215706
  have htrace : WordTrace (prefixWord ++ tailWord_215706) baseStart_215706 baseEnd_215706 := by
    simpa [prefixWord, tailWord_215706, baseEnd_215706] using wordTrace_append hprefix tailTrace_215706
  have hstable : (prefixWord ++ tailWord_215706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215706).length < 2 ^ (prefixWord ++ tailWord_215706).sum := by decide
  have hdescent : baseEnd_215706 < baseStart_215706 := by decide
  rcases family_descends (prefixWord ++ tailWord_215706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215748 : List Nat := [2, 3, 3, 1, 1, 11]
def baseStart_215748 : Nat := 118140960795 + 215748 * 2 ^ 59
def prefixEnd_215748 : Nat := 4983230072969 + 3 ^ 40 * 215748 * 2
def baseEnd_215748 : Nat := 1823578999939541047865

theorem tailTrace_215748 : CollatzResearch.WordTrace tailWord_215748 prefixEnd_215748 1823578999939541047865 := by
  unfold tailWord_215748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934488011194658834991949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5245984014926211779989265 3934488011194658834991949)
  ·
    refine ⟨1475433004197997063121981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3934488011194658834991949 1475433004197997063121981)
    ·
      refine ⟨553287376574248898670743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1475433004197997063121981 553287376574248898670743)
      ·
        refine ⟨829931064861373348006115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553287376574248898670743 829931064861373348006115)
        ·
          refine ⟨1244896597292060022009173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829931064861373348006115 1244896597292060022009173)
          ·
            refine ⟨1823578999939541047865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1244896597292060022009173 1823578999939541047865)
            ·
              rfl

theorem cell21_215748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 11].length) (baseStart_215748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215748 prefixEnd_215748 := by exact prefixLift 215748
  have htrace : WordTrace (prefixWord ++ tailWord_215748) baseStart_215748 baseEnd_215748 := by
    simpa [prefixWord, tailWord_215748, baseEnd_215748] using wordTrace_append hprefix tailTrace_215748
  have hstable : (prefixWord ++ tailWord_215748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215748).length < 2 ^ (prefixWord ++ tailWord_215748).sum := by decide
  have hdescent : baseEnd_215748 < baseStart_215748 := by decide
  rcases family_descends (prefixWord ++ tailWord_215748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215754 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_215754 : Nat := 118140960795 + 215754 * 2 ^ 59
def prefixEnd_215754 : Nat := 4983230072969 + 3 ^ 40 * 215754 * 2
def baseEnd_215754 : Nat := 49238002280112931192343

theorem tailTrace_215754 : CollatzResearch.WordTrace tailWord_215754 prefixEnd_215754 49238002280112931192343 := by
  unfold tailWord_215754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967298715091895173675579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5246129906911720463134877 1967298715091895173675579)
  ·
    refine ⟨2950948072637842760513369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967298715091895173675579 2950948072637842760513369)
    ·
      refine ⟨2213211054478382070385027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2950948072637842760513369 2213211054478382070385027)
      ·
        refine ⟨3319816581717573105577541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213211054478382070385027 3319816581717573105577541)
        ·
          refine ⟨622465609072044957295789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3319816581717573105577541 622465609072044957295789)
          ·
            refine ⟨233424603402016858985921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622465609072044957295789 233424603402016858985921)
            ·
              refine ⟨175068452551512644239441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233424603402016858985921 175068452551512644239441)
              ·
                refine ⟨131301339413634483179581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175068452551512644239441 131301339413634483179581)
                ·
                  refine ⟨49238002280112931192343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131301339413634483179581 49238002280112931192343)
                  ·
                    rfl

theorem cell21_215754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_215754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215754 prefixEnd_215754 := by exact prefixLift 215754
  have htrace : WordTrace (prefixWord ++ tailWord_215754) baseStart_215754 baseEnd_215754 := by
    simpa [prefixWord, tailWord_215754, baseEnd_215754] using wordTrace_append hprefix tailTrace_215754
  have hstable : (prefixWord ++ tailWord_215754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215754).length < 2 ^ (prefixWord ++ tailWord_215754).sum := by decide
  have hdescent : baseEnd_215754 < baseStart_215754 := by decide
  rcases family_descends (prefixWord ++ tailWord_215754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215779 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_215779 : Nat := 118140960795 + 215779 * 2 ^ 59
def prefixEnd_215779 : Nat := 4983230072969 + 3 ^ 40 * 215779 * 2
def baseEnd_215779 : Nat := 49243707620718443275625

theorem tailTrace_215779 : CollatzResearch.WordTrace tailWord_215779 prefixEnd_215779 49243707620718443275625 := by
  unfold tailWord_215779
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870106685277009964362391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5246737790184673309574927 7870106685277009964362391)
  ·
    refine ⟨11805160027915514946543587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7870106685277009964362391 11805160027915514946543587)
    ·
      refine ⟨17707740041873272419815381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11805160027915514946543587 17707740041873272419815381)
      ·
        refine ⟨415025157231404822339423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17707740041873272419815381 415025157231404822339423)
        ·
          refine ⟨622537735847107233509135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415025157231404822339423 622537735847107233509135)
          ·
            refine ⟨933806603770660850263703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622537735847107233509135 933806603770660850263703)
            ·
              refine ⟨1400709905655991275395555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933806603770660850263703 1400709905655991275395555)
              ·
                refine ⟨2101064858483986913093333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400709905655991275395555 2101064858483986913093333)
                ·
                  refine ⟨49243707620718443275625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2101064858483986913093333 49243707620718443275625)
                  ·
                    rfl

theorem cell21_215779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_215779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215779 prefixEnd_215779 := by exact prefixLift 215779
  have htrace : WordTrace (prefixWord ++ tailWord_215779) baseStart_215779 baseEnd_215779 := by
    simpa [prefixWord, tailWord_215779, baseEnd_215779] using wordTrace_append hprefix tailTrace_215779
  have hstable : (prefixWord ++ tailWord_215779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215779).length < 2 ^ (prefixWord ++ tailWord_215779).sum := by decide
  have hdescent : baseEnd_215779 < baseStart_215779 := by decide
  rcases family_descends (prefixWord ++ tailWord_215779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215793 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_215793 : Nat := 118140960795 + 215793 * 2 ^ 59
def prefixEnd_215793 : Nat := 4983230072969 + 3 ^ 40 * 215793 * 2
def baseEnd_215793 : Nat := 49246902611457530042263

theorem tailTrace_215793 : CollatzResearch.WordTrace tailWord_215793 prefixEnd_215793 49246902611457530042263 := by
  unfold tailWord_215793
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870617307226290355372033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5247078204817526903581355 7870617307226290355372033)
  ·
    refine ⟨5902962980419717766529025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7870617307226290355372033 5902962980419717766529025)
    ·
      refine ⟨4427222235314788324896769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5902962980419717766529025 4427222235314788324896769)
      ·
        refine ⟨3320416676486091243672577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4427222235314788324896769 3320416676486091243672577)
        ·
          refine ⟨2490312507364568432754433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320416676486091243672577 2490312507364568432754433)
          ·
            refine ⟨1867734380523426324565825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490312507364568432754433 1867734380523426324565825)
            ·
              refine ⟨1400800785392569743424369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1867734380523426324565825 1400800785392569743424369)
              ·
                refine ⟨1050600589044427307568277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400800785392569743424369 1050600589044427307568277)
                ·
                  refine ⟨49246902611457530042263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1050600589044427307568277 49246902611457530042263)
                  ·
                    rfl

theorem cell21_215793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_215793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215793 prefixEnd_215793 := by exact prefixLift 215793
  have htrace : WordTrace (prefixWord ++ tailWord_215793) baseStart_215793 baseEnd_215793 := by
    simpa [prefixWord, tailWord_215793, baseEnd_215793] using wordTrace_append hprefix tailTrace_215793
  have hstable : (prefixWord ++ tailWord_215793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215793).length < 2 ^ (prefixWord ++ tailWord_215793).sum := by decide
  have hdescent : baseEnd_215793 < baseStart_215793 := by decide
  rcases family_descends (prefixWord ++ tailWord_215793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215878 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_215878 : Nat := 118140960795 + 215878 * 2 ^ 59
def prefixEnd_215878 : Nat := 4983230072969 + 3 ^ 40 * 215878 * 2
def baseEnd_215878 : Nat := 49266300769516271125423

theorem tailTrace_215878 : CollatzResearch.WordTrace tailWord_215878 prefixEnd_215878 49266300769516271125423 := by
  unfold tailWord_215878
  simp only [CollatzResearch.WordTrace]
  refine ⟨246053672247448433506759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5249145007945566581477525 246053672247448433506759)
  ·
    refine ⟨369080508371172650260139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246053672247448433506759 369080508371172650260139)
    ·
      refine ⟨553620762556758975390209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369080508371172650260139 553620762556758975390209)
      ·
        refine ⟨415215571917569231542657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553620762556758975390209 415215571917569231542657)
        ·
          refine ⟨311411678938176923656993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415215571917569231542657 311411678938176923656993)
          ·
            refine ⟨233558759203632692742745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311411678938176923656993 233558759203632692742745)
            ·
              refine ⟨175169069402724519557059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233558759203632692742745 175169069402724519557059)
              ·
                refine ⟨262753604104086779335589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175169069402724519557059 262753604104086779335589)
                ·
                  refine ⟨49266300769516271125423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262753604104086779335589 49266300769516271125423)
                  ·
                    rfl

theorem cell21_215878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_215878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_215878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_215878 prefixEnd_215878 := by exact prefixLift 215878
  have htrace : WordTrace (prefixWord ++ tailWord_215878) baseStart_215878 baseEnd_215878 := by
    simpa [prefixWord, tailWord_215878, baseEnd_215878] using wordTrace_append hprefix tailTrace_215878
  have hstable : (prefixWord ++ tailWord_215878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215878).length < 2 ^ (prefixWord ++ tailWord_215878).sum := by decide
  have hdescent : baseEnd_215878 < baseStart_215878 := by decide
  rcases family_descends (prefixWord ++ tailWord_215878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216024 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_216024 : Nat := 118140960795 + 216024 * 2 ^ 59
def prefixEnd_216024 : Nat := 4983230072969 + 3 ^ 40 * 216024 * 2
def baseEnd_216024 : Nat := 49299619958652461691791

theorem tailTrace_216024 : CollatzResearch.WordTrace tailWord_216024 prefixEnd_216024 49299619958652461691791 := by
  unfold tailWord_216024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3939521284694708403515563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5252695046259611204687417 3939521284694708403515563)
  ·
    refine ⟨5909281927042062605273345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3939521284694708403515563 5909281927042062605273345)
    ·
      refine ⟨4431961445281546953955009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5909281927042062605273345 4431961445281546953955009)
      ·
        refine ⟨3323971083961160215466257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4431961445281546953955009 3323971083961160215466257)
        ·
          refine ⟨2492978312970870161599693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3323971083961160215466257 2492978312970870161599693)
          ·
            refine ⟨934866867364076310599885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2492978312970870161599693 934866867364076310599885)
            ·
              refine ⟨350575075261528616474957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 934866867364076310599885 350575075261528616474957)
              ·
                refine ⟨131465653223073231178109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350575075261528616474957 131465653223073231178109)
                ·
                  refine ⟨49299619958652461691791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131465653223073231178109 49299619958652461691791)
                  ·
                    rfl

theorem cell21_216024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_216024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216024 prefixEnd_216024 := by exact prefixLift 216024
  have htrace : WordTrace (prefixWord ++ tailWord_216024) baseStart_216024 baseEnd_216024 := by
    simpa [prefixWord, tailWord_216024, baseEnd_216024] using wordTrace_append hprefix tailTrace_216024
  have hstable : (prefixWord ++ tailWord_216024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216024).length < 2 ^ (prefixWord ++ tailWord_216024).sum := by decide
  have hdescent : baseEnd_216024 < baseStart_216024 := by decide
  rcases family_descends (prefixWord ++ tailWord_216024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216083 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 3]
def baseStart_216083 : Nat := 118140960795 + 216083 * 2 ^ 59
def prefixEnd_216083 : Nat := 4983230072969 + 3 ^ 40 * 216083 * 2
def baseEnd_216083 : Nat := 49313084562481470208337

theorem tailTrace_216083 : CollatzResearch.WordTrace tailWord_216083 prefixEnd_216083 49313084562481470208337 := by
  unfold tailWord_216083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881194476175669883428903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5254129650783779922285935 7881194476175669883428903)
  ·
    refine ⟨11821791714263504825143355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7881194476175669883428903 11821791714263504825143355)
    ·
      refine ⟨17732687571395257237715033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11821791714263504825143355 17732687571395257237715033)
      ·
        refine ⟨13299515678546442928286275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17732687571395257237715033 13299515678546442928286275)
        ·
          refine ⟨19949273517819664392429413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13299515678546442928286275 19949273517819664392429413)
          ·
            refine ⟨3740488784591187073580515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19949273517819664392429413 3740488784591187073580515)
            ·
              refine ⟨5610733176886780610370773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740488784591187073580515 5610733176886780610370773)
              ·
                refine ⟨131501558833283920555565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5610733176886780610370773 131501558833283920555565)
                ·
                  refine ⟨49313084562481470208337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131501558833283920555565 49313084562481470208337)
                  ·
                    rfl

theorem cell21_216083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3].length) (baseStart_216083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216083 prefixEnd_216083 := by exact prefixLift 216083
  have htrace : WordTrace (prefixWord ++ tailWord_216083) baseStart_216083 baseEnd_216083 := by
    simpa [prefixWord, tailWord_216083, baseEnd_216083] using wordTrace_append hprefix tailTrace_216083
  have hstable : (prefixWord ++ tailWord_216083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216083).length < 2 ^ (prefixWord ++ tailWord_216083).sum := by decide
  have hdescent : baseEnd_216083 < baseStart_216083 := by decide
  rcases family_descends (prefixWord ++ tailWord_216083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216128 : List Nat := [2, 1, 1, 2, 2, 3, 5, 5]
def baseStart_216128 : Nat := 118140960795 + 216128 * 2 ^ 59
def prefixEnd_216128 : Nat := 4983230072969 + 3 ^ 40 * 216128 * 2
def baseEnd_216128 : Nat := 16441118058523797319415

theorem tailTrace_216128 : CollatzResearch.WordTrace tailWord_216128 prefixEnd_216128 16441118058523797319415 := by
  unfold tailWord_216128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941417880506321284408519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5255223840675095045878025 3941417880506321284408519)
  ·
    refine ⟨5912126820759481926612779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3941417880506321284408519 5912126820759481926612779)
    ·
      refine ⟨8868190231139222889919169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5912126820759481926612779 8868190231139222889919169)
      ·
        refine ⟨6651142673354417167439377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8868190231139222889919169 6651142673354417167439377)
        ·
          refine ⟨4988357005015812875579533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6651142673354417167439377 4988357005015812875579533)
          ·
            refine ⟨1870633876880929828342325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988357005015812875579533 1870633876880929828342325)
            ·
              refine ⟨175371925957587171407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1870633876880929828342325 175371925957587171407093)
              ·
                refine ⟨16441118058523797319415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175371925957587171407093 16441118058523797319415)
                ·
                  rfl

theorem cell21_216128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_216128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216128 prefixEnd_216128 := by exact prefixLift 216128
  have htrace : WordTrace (prefixWord ++ tailWord_216128) baseStart_216128 baseEnd_216128 := by
    simpa [prefixWord, tailWord_216128, baseEnd_216128] using wordTrace_append hprefix tailTrace_216128
  have hstable : (prefixWord ++ tailWord_216128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216128).length < 2 ^ (prefixWord ++ tailWord_216128).sum := by decide
  have hdescent : baseEnd_216128 < baseStart_216128 := by decide
  rcases family_descends (prefixWord ++ tailWord_216128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216134 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_216134 : Nat := 118140960795 + 216134 * 2 ^ 59
def prefixEnd_216134 : Nat := 4983230072969 + 3 ^ 40 * 216134 * 2
def baseEnd_216134 : Nat := 49324723457316714858233

theorem tailTrace_216134 : CollatzResearch.WordTrace tailWord_216134 prefixEnd_216134 49324723457316714858233 := by
  unfold tailWord_216134
  simp only [CollatzResearch.WordTrace]
  refine ⟨246345456218465799797983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5255369732660603729023637 246345456218465799797983)
  ·
    refine ⟨369518184327698699696975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246345456218465799797983 369518184327698699696975)
    ·
      refine ⟨554277276491548049545463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369518184327698699696975 554277276491548049545463)
      ·
        refine ⟨831415914737322074318195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554277276491548049545463 831415914737322074318195)
        ·
          refine ⟨1247123872105983111477293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 831415914737322074318195 1247123872105983111477293)
          ·
            refine ⟨467671452039743666803985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1247123872105983111477293 467671452039743666803985)
            ·
              refine ⟨350753589029807750102989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467671452039743666803985 350753589029807750102989)
              ·
                refine ⟨131532595886177906288621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350753589029807750102989 131532595886177906288621)
                ·
                  refine ⟨49324723457316714858233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131532595886177906288621 49324723457316714858233)
                  ·
                    rfl

theorem cell21_216134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_216134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216134 prefixEnd_216134 := by exact prefixLift 216134
  have htrace : WordTrace (prefixWord ++ tailWord_216134) baseStart_216134 baseEnd_216134 := by
    simpa [prefixWord, tailWord_216134, baseEnd_216134] using wordTrace_append hprefix tailTrace_216134
  have hstable : (prefixWord ++ tailWord_216134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216134).length < 2 ^ (prefixWord ++ tailWord_216134).sum := by decide
  have hdescent : baseEnd_216134 < baseStart_216134 := by decide
  rcases family_descends (prefixWord ++ tailWord_216134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216142 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_216142 : Nat := 118140960795 + 216142 * 2 ^ 59
def prefixEnd_216142 : Nat := 4983230072969 + 3 ^ 40 * 216142 * 2
def baseEnd_216142 : Nat := 49326549166310478724883

theorem tailTrace_216142 : CollatzResearch.WordTrace tailWord_216142 prefixEnd_216142 49326549166310478724883 := by
  unfold tailWord_216142
  simp only [CollatzResearch.WordTrace]
  refine ⟨985418297870240369978335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5255564255307948639884453 985418297870240369978335)
  ·
    refine ⟨1478127446805360554967503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 985418297870240369978335 1478127446805360554967503)
    ·
      refine ⟨2217191170208040832451255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478127446805360554967503 2217191170208040832451255)
      ·
        refine ⟨3325786755312061248676883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217191170208040832451255 3325786755312061248676883)
        ·
          refine ⟨4988680132968091873015325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325786755312061248676883 4988680132968091873015325)
          ·
            refine ⟨1870755049863034452380747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988680132968091873015325 1870755049863034452380747)
            ·
              refine ⟨2806132574794551678571121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870755049863034452380747 2806132574794551678571121)
              ·
                refine ⟨2104599431095913758928341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2806132574794551678571121 2104599431095913758928341)
                ·
                  refine ⟨49326549166310478724883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2104599431095913758928341 49326549166310478724883)
                  ·
                    rfl

theorem cell21_216142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_216142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216142 prefixEnd_216142 := by exact prefixLift 216142
  have htrace : WordTrace (prefixWord ++ tailWord_216142) baseStart_216142 baseEnd_216142 := by
    simpa [prefixWord, tailWord_216142, baseEnd_216142] using wordTrace_append hprefix tailTrace_216142
  have hstable : (prefixWord ++ tailWord_216142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216142).length < 2 ^ (prefixWord ++ tailWord_216142).sum := by decide
  have hdescent : baseEnd_216142 < baseStart_216142 := by decide
  rcases family_descends (prefixWord ++ tailWord_216142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216159 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 3]
def baseStart_216159 : Nat := 118140960795 + 216159 * 2 ^ 59
def prefixEnd_216159 : Nat := 4983230072969 + 3 ^ 40 * 216159 * 2
def baseEnd_216159 : Nat := 49330428797922226941515

theorem tailTrace_216159 : CollatzResearch.WordTrace tailWord_216159 prefixEnd_216159 49330428797922226941515 := by
  unfold tailWord_216159
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883966423900334863195531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5255977615933556575463687 7883966423900334863195531)
  ·
    refine ⟨11825949635850502294793297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7883966423900334863195531 11825949635850502294793297)
    ·
      refine ⟨8869462226887876721094973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11825949635850502294793297 8869462226887876721094973)
      ·
        refine ⟨3326048335082953770410615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8869462226887876721094973 3326048335082953770410615)
        ·
          refine ⟨4989072502624430655615923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326048335082953770410615 4989072502624430655615923)
          ·
            refine ⟨7483608753936645983423885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4989072502624430655615923 7483608753936645983423885)
            ·
              refine ⟨2806353282726242243783957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7483608753936645983423885 2806353282726242243783957)
              ·
                refine ⟨131547810127792605177373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2806353282726242243783957 131547810127792605177373)
                ·
                  refine ⟨49330428797922226941515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131547810127792605177373 49330428797922226941515)
                  ·
                    rfl

theorem cell21_216159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 3].length) (baseStart_216159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216159 prefixEnd_216159 := by exact prefixLift 216159
  have htrace : WordTrace (prefixWord ++ tailWord_216159) baseStart_216159 baseEnd_216159 := by
    simpa [prefixWord, tailWord_216159, baseEnd_216159] using wordTrace_append hprefix tailTrace_216159
  have hstable : (prefixWord ++ tailWord_216159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216159).length < 2 ^ (prefixWord ++ tailWord_216159).sum := by decide
  have hdescent : baseEnd_216159 < baseStart_216159 := by decide
  rcases family_descends (prefixWord ++ tailWord_216159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216193 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 3]
def baseStart_216193 : Nat := 118140960795 + 216193 * 2 ^ 59
def prefixEnd_216193 : Nat := 4983230072969 + 3 ^ 40 * 216193 * 2
def baseEnd_216193 : Nat := 49338188061145723374779

theorem tailTrace_216193 : CollatzResearch.WordTrace tailWord_216193 prefixEnd_216193 49338188061145723374779 := by
  unfold tailWord_216193
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885206505777158669933233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5256804337184772446622155 7885206505777158669933233)
  ·
    refine ⟨5913904879332869002449925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7885206505777158669933233 5913904879332869002449925)
    ·
      refine ⟨1108857164874912937959361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5913904879332869002449925 1108857164874912937959361)
      ·
        refine ⟨831642873656184703469521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1108857164874912937959361 831642873656184703469521)
        ·
          refine ⟨623732155242138527602141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831642873656184703469521 623732155242138527602141)
          ·
            refine ⟨233899558215801947850803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623732155242138527602141 233899558215801947850803)
            ·
              refine ⟨350849337323702921776205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233899558215801947850803 350849337323702921776205)
              ·
                refine ⟨131568501496388595666077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350849337323702921776205 131568501496388595666077)
                ·
                  refine ⟨49338188061145723374779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131568501496388595666077 49338188061145723374779)
                  ·
                    rfl

theorem cell21_216193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_216193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216193 prefixEnd_216193 := by exact prefixLift 216193
  have htrace : WordTrace (prefixWord ++ tailWord_216193) baseStart_216193 baseEnd_216193 := by
    simpa [prefixWord, tailWord_216193, baseEnd_216193] using wordTrace_append hprefix tailTrace_216193
  have hstable : (prefixWord ++ tailWord_216193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216193).length < 2 ^ (prefixWord ++ tailWord_216193).sum := by decide
  have hdescent : baseEnd_216193 < baseStart_216193 := by decide
  rcases family_descends (prefixWord ++ tailWord_216193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216266 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_216266 : Nat := 118140960795 + 216266 * 2 ^ 59
def prefixEnd_216266 : Nat := 4983230072969 + 3 ^ 40 * 216266 * 2
def baseEnd_216266 : Nat := 49354847655713818657963

theorem tailTrace_216266 : CollatzResearch.WordTrace tailWord_216266 prefixEnd_216266 49354847655713818657963 := by
  unfold tailWord_216266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971967258628173034335163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5258579356341794758227101 1971967258628173034335163)
  ·
    refine ⟨2957950887942259551502745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1971967258628173034335163 2957950887942259551502745)
    ·
      refine ⟨2218463165956694663627059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2957950887942259551502745 2218463165956694663627059)
      ·
        refine ⟨3327694748935041995440589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218463165956694663627059 3327694748935041995440589)
        ·
          refine ⟨1247885530850640748290221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3327694748935041995440589 1247885530850640748290221)
          ·
            refine ⟨467957074068990280608833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1247885530850640748290221 467957074068990280608833)
            ·
              refine ⟨350967805551742710456625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467957074068990280608833 350967805551742710456625)
              ·
                refine ⟨263225854163807032842469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350967805551742710456625 263225854163807032842469)
                ·
                  refine ⟨49354847655713818657963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263225854163807032842469 49354847655713818657963)
                  ·
                    rfl

theorem cell21_216266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_216266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216266 prefixEnd_216266 := by exact prefixLift 216266
  have htrace : WordTrace (prefixWord ++ tailWord_216266) baseStart_216266 baseEnd_216266 := by
    simpa [prefixWord, tailWord_216266, baseEnd_216266] using wordTrace_append hprefix tailTrace_216266
  have hstable : (prefixWord ++ tailWord_216266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216266).length < 2 ^ (prefixWord ++ tailWord_216266).sum := by decide
  have hdescent : baseEnd_216266 < baseStart_216266 := by decide
  rcases family_descends (prefixWord ++ tailWord_216266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216384 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_216384 : Nat := 118140960795 + 216384 * 2 ^ 59
def prefixEnd_216384 : Nat := 4983230072969 + 3 ^ 40 * 216384 * 2
def baseEnd_216384 : Nat := 49381776863371835691055

theorem tailTrace_216384 : CollatzResearch.WordTrace tailWord_216384 prefixEnd_216384 49381776863371835691055 := by
  unfold tailWord_216384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946086424042599145068103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5261448565390132193424137 3946086424042599145068103)
  ·
    refine ⟨5919129636063898717602155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3946086424042599145068103 5919129636063898717602155)
    ·
      refine ⟨8878694454095848076403233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919129636063898717602155 8878694454095848076403233)
      ·
        refine ⟨6659020840571886057302425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8878694454095848076403233 6659020840571886057302425)
        ·
          refine ⟨4994265630428914542976819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6659020840571886057302425 4994265630428914542976819)
          ·
            refine ⟨7491398445643371814465229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994265630428914542976819 7491398445643371814465229)
            ·
              refine ⟨2809274417116264430424461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7491398445643371814465229 2809274417116264430424461)
              ·
                refine ⟨1053477906418599161409173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2809274417116264430424461 1053477906418599161409173)
                ·
                  refine ⟨49381776863371835691055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1053477906418599161409173 49381776863371835691055)
                  ·
                    rfl

theorem cell21_216384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_216384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216384 prefixEnd_216384 := by exact prefixLift 216384
  have htrace : WordTrace (prefixWord ++ tailWord_216384) baseStart_216384 baseEnd_216384 := by
    simpa [prefixWord, tailWord_216384, baseEnd_216384] using wordTrace_append hprefix tailTrace_216384
  have hstable : (prefixWord ++ tailWord_216384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216384).length < 2 ^ (prefixWord ++ tailWord_216384).sum := by decide
  have hdescent : baseEnd_216384 < baseStart_216384 := by decide
  rcases family_descends (prefixWord ++ tailWord_216384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216401 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_216401 : Nat := 118140960795 + 216401 * 2 ^ 59
def prefixEnd_216401 : Nat := 4983230072969 + 3 ^ 40 * 216401 * 2
def baseEnd_216401 : Nat := 49385656494983583907687

theorem tailTrace_216401 : CollatzResearch.WordTrace tailWord_216401 prefixEnd_216401 49385656494983583907687 := by
  unfold tailWord_216401
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892792889023610193505057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5261861926015740129003371 7892792889023610193505057)
  ·
    refine ⟨5919594666767707645128793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7892792889023610193505057 5919594666767707645128793)
    ·
      refine ⟨4439696000075780733846595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5919594666767707645128793 4439696000075780733846595)
      ·
        refine ⟨6659544000113671100769893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439696000075780733846595 6659544000113671100769893)
        ·
          refine ⟨1248664500021313331394355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6659544000113671100769893 1248664500021313331394355)
          ·
            refine ⟨1872996750031969997091533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248664500021313331394355 1872996750031969997091533)
            ·
              refine ⟨702373781261988748909325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872996750031969997091533 702373781261988748909325)
              ·
                refine ⟨263390167973245780840997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 702373781261988748909325 263390167973245780840997)
                ·
                  refine ⟨49385656494983583907687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263390167973245780840997 49385656494983583907687)
                  ·
                    rfl

theorem cell21_216401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_216401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216401 prefixEnd_216401 := by exact prefixLift 216401
  have htrace : WordTrace (prefixWord ++ tailWord_216401) baseStart_216401 baseEnd_216401 := by
    simpa [prefixWord, tailWord_216401, baseEnd_216401] using wordTrace_append hprefix tailTrace_216401
  have hstable : (prefixWord ++ tailWord_216401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216401).length < 2 ^ (prefixWord ++ tailWord_216401).sum := by decide
  have hdescent : baseEnd_216401 < baseStart_216401 := by decide
  rcases family_descends (prefixWord ++ tailWord_216401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216449 : List Nat := [1, 2, 4, 3, 2, 2, 1, 6]
def baseStart_216449 : Nat := 118140960795 + 216449 * 2 ^ 59
def prefixEnd_216449 : Nat := 4983230072969 + 3 ^ 40 * 216449 * 2
def baseEnd_216449 : Nat := 16465536916315389035863

theorem tailTrace_216449 : CollatzResearch.WordTrace tailWord_216449 prefixEnd_216449 16465536916315389035863 := by
  unfold tailWord_216449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894543592849714391252401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5263029061899809594168267 7894543592849714391252401)
  ·
    refine ⟨5920907694637285793439301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7894543592849714391252401 5920907694637285793439301)
    ·
      refine ⟨1110170192744491086269869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5920907694637285793439301 1110170192744491086269869)
      ·
        refine ⟨416313822279184157351201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1110170192744491086269869 416313822279184157351201)
        ·
          refine ⟨312235366709388118013401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416313822279184157351201 312235366709388118013401)
          ·
            refine ⟨234176525032041088510051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312235366709388118013401 234176525032041088510051)
            ·
              refine ⟨351264787548061632765077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234176525032041088510051 351264787548061632765077)
              ·
                refine ⟨16465536916315389035863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 351264787548061632765077 16465536916315389035863)
                ·
                  rfl

theorem cell21_216449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 6].length) (baseStart_216449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216449 prefixEnd_216449 := by exact prefixLift 216449
  have htrace : WordTrace (prefixWord ++ tailWord_216449) baseStart_216449 baseEnd_216449 := by
    simpa [prefixWord, tailWord_216449, baseEnd_216449] using wordTrace_append hprefix tailTrace_216449
  have hstable : (prefixWord ++ tailWord_216449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216449).length < 2 ^ (prefixWord ++ tailWord_216449).sum := by decide
  have hdescent : baseEnd_216449 < baseStart_216449 := by decide
  rcases family_descends (prefixWord ++ tailWord_216449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216466 : List Nat := [3, 2, 3, 3, 1, 1, 3, 5]
def baseStart_216466 : Nat := 118140960795 + 216466 * 2 ^ 59
def prefixEnd_216466 : Nat := 4983230072969 + 3 ^ 40 * 216466 * 2
def baseEnd_216466 : Nat := 16466830126852638441407

theorem tailTrace_216466 : CollatzResearch.WordTrace tailWord_216466 prefixEnd_216466 16466830126852638441407 := by
  unfold tailWord_216466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973790908447031573655313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5263442422525417529747501 1973790908447031573655313)
  ·
    refine ⟨1480343181335273680241485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1973790908447031573655313 1480343181335273680241485)
    ·
      refine ⟨555128693000727630090557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1480343181335273680241485 555128693000727630090557)
      ·
        refine ⟨208173259875272861283959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555128693000727630090557 208173259875272861283959)
        ·
          refine ⟨312259889812909291925939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208173259875272861283959 312259889812909291925939)
          ·
            refine ⟨468389834719363937888909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312259889812909291925939 468389834719363937888909)
            ·
              refine ⟨175646188019761476708341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468389834719363937888909 175646188019761476708341)
              ·
                refine ⟨16466830126852638441407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175646188019761476708341 16466830126852638441407)
                ·
                  rfl

theorem cell21_216466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_216466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216466 prefixEnd_216466 := by exact prefixLift 216466
  have htrace : WordTrace (prefixWord ++ tailWord_216466) baseStart_216466 baseEnd_216466 := by
    simpa [prefixWord, tailWord_216466, baseEnd_216466] using wordTrace_append hprefix tailTrace_216466
  have hstable : (prefixWord ++ tailWord_216466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216466).length < 2 ^ (prefixWord ++ tailWord_216466).sum := by decide
  have hdescent : baseEnd_216466 < baseStart_216466 := by decide
  rcases family_descends (prefixWord ++ tailWord_216466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216522 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_216522 : Nat := 118140960795 + 216522 * 2 ^ 59
def prefixEnd_216522 : Nat := 4983230072969 + 3 ^ 40 * 216522 * 2
def baseEnd_216522 : Nat := 49413270343514262390773

theorem tailTrace_216522 : CollatzResearch.WordTrace tailWord_216522 prefixEnd_216522 49413270343514262390773 := by
  unfold tailWord_216522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974301530396311964664955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5264804081056831905773213 1974301530396311964664955)
  ·
    refine ⟨2961452295594467946997433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974301530396311964664955 2961452295594467946997433)
    ·
      refine ⟨2221089221695850960248075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2961452295594467946997433 2221089221695850960248075)
      ·
        refine ⟨3331633832543776440372113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221089221695850960248075 3331633832543776440372113)
        ·
          refine ⟨2498725374407832330279085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331633832543776440372113 2498725374407832330279085)
          ·
            refine ⟨937022015402937123854657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2498725374407832330279085 937022015402937123854657)
            ·
              refine ⟨702766511552202842890993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937022015402937123854657 702766511552202842890993)
              ·
                refine ⟨527074883664152132168245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702766511552202842890993 527074883664152132168245)
                ·
                  refine ⟨49413270343514262390773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 527074883664152132168245 49413270343514262390773)
                  ·
                    rfl

theorem cell21_216522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_216522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216522 prefixEnd_216522 := by exact prefixLift 216522
  have htrace : WordTrace (prefixWord ++ tailWord_216522) baseStart_216522 baseEnd_216522 := by
    simpa [prefixWord, tailWord_216522, baseEnd_216522] using wordTrace_append hprefix tailTrace_216522
  have hstable : (prefixWord ++ tailWord_216522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216522).length < 2 ^ (prefixWord ++ tailWord_216522).sum := by decide
  have hdescent : baseEnd_216522 < baseStart_216522 := by decide
  rcases family_descends (prefixWord ++ tailWord_216522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216536 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_216536 : Nat := 118140960795 + 216536 * 2 ^ 59
def prefixEnd_216536 : Nat := 4983230072969 + 3 ^ 40 * 216536 * 2
def baseEnd_216536 : Nat := 49416465334253349157411

theorem tailTrace_216536 : CollatzResearch.WordTrace tailWord_216536 prefixEnd_216536 49416465334253349157411 := by
  unfold tailWord_216536
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948858371767264124834731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5265144495689685499779641 3948858371767264124834731)
  ·
    refine ⟨5923287557650896187252097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948858371767264124834731 5923287557650896187252097)
    ·
      refine ⟨4442465668238172140439073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5923287557650896187252097 4442465668238172140439073)
      ·
        refine ⟨3331849251178629105329305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4442465668238172140439073 3331849251178629105329305)
        ·
          refine ⟨2498886938383971828996979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331849251178629105329305 2498886938383971828996979)
          ·
            refine ⟨3748330407575957743495469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498886938383971828996979 3748330407575957743495469)
            ·
              refine ⟨1405623902840984153810801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3748330407575957743495469 1405623902840984153810801)
              ·
                refine ⟨1054217927130738115358101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405623902840984153810801 1054217927130738115358101)
                ·
                  refine ⟨49416465334253349157411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1054217927130738115358101 49416465334253349157411)
                  ·
                    rfl

theorem cell21_216536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_216536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216536 prefixEnd_216536 := by exact prefixLift 216536
  have htrace : WordTrace (prefixWord ++ tailWord_216536) baseStart_216536 baseEnd_216536 := by
    simpa [prefixWord, tailWord_216536, baseEnd_216536] using wordTrace_append hprefix tailTrace_216536
  have hstable : (prefixWord ++ tailWord_216536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216536).length < 2 ^ (prefixWord ++ tailWord_216536).sum := by decide
  have hdescent : baseEnd_216536 < baseStart_216536 := by decide
  rcases family_descends (prefixWord ++ tailWord_216536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216581 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_216581 : Nat := 118140960795 + 216581 * 2 ^ 59
def prefixEnd_216581 : Nat := 4983230072969 + 3 ^ 40 * 216581 * 2
def baseEnd_216581 : Nat := 49426734947343270907319

theorem tailTrace_216581 : CollatzResearch.WordTrace tailWord_216581 prefixEnd_216581 49426734947343270907319 := by
  unfold tailWord_216581
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899358028371500935057597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5266238685581000623371731 7899358028371500935057597)
  ·
    refine ⟨2962259260639312850646599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7899358028371500935057597 2962259260639312850646599)
    ·
      refine ⟨4443388890958969275969899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962259260639312850646599 4443388890958969275969899)
      ·
        refine ⟨6665083336438453913954849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443388890958969275969899 6665083336438453913954849)
        ·
          refine ⟨4998812502328840435466137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6665083336438453913954849 4998812502328840435466137)
          ·
            refine ⟨3749109376746630326599603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4998812502328840435466137 3749109376746630326599603)
            ·
              refine ⟨5623664065119945489899405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3749109376746630326599603 5623664065119945489899405)
              ·
                refine ⟨2108874024419979558712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5623664065119945489899405 2108874024419979558712277)
                ·
                  refine ⟨49426734947343270907319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2108874024419979558712277 49426734947343270907319)
                  ·
                    rfl

theorem cell21_216581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_216581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216581 prefixEnd_216581 := by exact prefixLift 216581
  have htrace : WordTrace (prefixWord ++ tailWord_216581) baseStart_216581 baseEnd_216581 := by
    simpa [prefixWord, tailWord_216581, baseEnd_216581] using wordTrace_append hprefix tailTrace_216581
  have hstable : (prefixWord ++ tailWord_216581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216581).length < 2 ^ (prefixWord ++ tailWord_216581).sum := by decide
  have hdescent : baseEnd_216581 < baseStart_216581 := by decide
  rcases family_descends (prefixWord ++ tailWord_216581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216629 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_216629 : Nat := 118140960795 + 216629 * 2 ^ 59
def prefixEnd_216629 : Nat := 4983230072969 + 3 ^ 40 * 216629 * 2
def baseEnd_216629 : Nat := 49437689201305854107221

theorem tailTrace_216629 : CollatzResearch.WordTrace tailWord_216629 prefixEnd_216629 49437689201305854107221 := by
  unfold tailWord_216629
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901108732197605132804941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5267405821465070088536627 7901108732197605132804941)
  ·
    refine ⟨2962915774574101924801853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7901108732197605132804941 2962915774574101924801853)
    ·
      refine ⟨1111093415465288221800695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2962915774574101924801853 1111093415465288221800695)
      ·
        refine ⟨1666640123197932332701043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111093415465288221800695 1666640123197932332701043)
        ·
          refine ⟨2499960184796898499051565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666640123197932332701043 2499960184796898499051565)
          ·
            refine ⟨937485069298836937144337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2499960184796898499051565 937485069298836937144337)
            ·
              refine ⟨703113801974127702858253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937485069298836937144337 703113801974127702858253)
              ·
                refine ⟨263667675740297888571845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703113801974127702858253 263667675740297888571845)
                ·
                  refine ⟨49437689201305854107221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263667675740297888571845 49437689201305854107221)
                  ·
                    rfl

theorem cell21_216629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_216629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216629 prefixEnd_216629 := by exact prefixLift 216629
  have htrace : WordTrace (prefixWord ++ tailWord_216629) baseStart_216629 baseEnd_216629 := by
    simpa [prefixWord, tailWord_216629, baseEnd_216629] using wordTrace_append hprefix tailTrace_216629
  have hstable : (prefixWord ++ tailWord_216629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216629).length < 2 ^ (prefixWord ++ tailWord_216629).sum := by decide
  have hdescent : baseEnd_216629 < baseStart_216629 := by decide
  rcases family_descends (prefixWord ++ tailWord_216629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216657 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_216657 : Nat := 118140960795 + 216657 * 2 ^ 59
def prefixEnd_216657 : Nat := 4983230072969 + 3 ^ 40 * 216657 * 2
def baseEnd_216657 : Nat := 49444079182784027640497

theorem tailTrace_216657 : CollatzResearch.WordTrace tailWord_216657 prefixEnd_216657 49444079182784027640497 := by
  unfold tailWord_216657
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902129976096165914824225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5268086650730777276549483 7902129976096165914824225)
  ·
    refine ⟨5926597482072124436118169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7902129976096165914824225 5926597482072124436118169)
    ·
      refine ⟨4444948111554093327088627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5926597482072124436118169 4444948111554093327088627)
      ·
        refine ⟨6667422167331139990632941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444948111554093327088627 6667422167331139990632941)
        ·
          refine ⟨2500283312749177496487353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6667422167331139990632941 2500283312749177496487353)
          ·
            refine ⟨1875212484561883122365515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500283312749177496487353 1875212484561883122365515)
            ·
              refine ⟨2812818726842824683548273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875212484561883122365515 2812818726842824683548273)
              ·
                refine ⟨2109614045132118512661205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812818726842824683548273 2109614045132118512661205)
                ·
                  refine ⟨49444079182784027640497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2109614045132118512661205 49444079182784027640497)
                  ·
                    rfl

theorem cell21_216657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_216657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216657 prefixEnd_216657 := by exact prefixLift 216657
  have htrace : WordTrace (prefixWord ++ tailWord_216657) baseStart_216657 baseEnd_216657 := by
    simpa [prefixWord, tailWord_216657, baseEnd_216657] using wordTrace_append hprefix tailTrace_216657
  have hstable : (prefixWord ++ tailWord_216657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216657).length < 2 ^ (prefixWord ++ tailWord_216657).sum := by decide
  have hdescent : baseEnd_216657 < baseStart_216657 := by decide
  rcases family_descends (prefixWord ++ tailWord_216657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216770 : List Nat := [3, 5, 1, 2, 2, 8]
def baseStart_216770 : Nat := 118140960795 + 216770 * 2 ^ 59
def prefixEnd_216770 : Nat := 4983230072969 + 3 ^ 40 * 216770 * 2
def baseEnd_216770 : Nat := 1832217308234108972479

theorem tailTrace_216770 : CollatzResearch.WordTrace tailWord_216770 prefixEnd_216770 1832217308234108972479 := by
  unfold tailWord_216770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976562856171696553421941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5270834283124524142458509 1976562856171696553421941)
  ·
    refine ⟨185302767766096551883307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1976562856171696553421941 185302767766096551883307)
    ·
      refine ⟨277954151649144827824961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185302767766096551883307 277954151649144827824961)
      ·
        refine ⟨208465613736858620868721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277954151649144827824961 208465613736858620868721)
        ·
          refine ⟨156349210302643965651541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208465613736858620868721 156349210302643965651541)
          ·
            refine ⟨1832217308234108972479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 156349210302643965651541 1832217308234108972479)
            ·
              rfl

theorem cell21_216770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 8].length) (baseStart_216770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216770 prefixEnd_216770 := by exact prefixLift 216770
  have htrace : WordTrace (prefixWord ++ tailWord_216770) baseStart_216770 baseEnd_216770 := by
    simpa [prefixWord, tailWord_216770, baseEnd_216770] using wordTrace_append hprefix tailTrace_216770
  have hstable : (prefixWord ++ tailWord_216770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216770).length < 2 ^ (prefixWord ++ tailWord_216770).sum := by decide
  have hdescent : baseEnd_216770 < baseStart_216770 := by decide
  rcases family_descends (prefixWord ++ tailWord_216770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216778 : List Nat := [3, 1, 2, 1, 14]
def baseStart_216778 : Nat := 118140960795 + 216778 * 2 ^ 59
def prefixEnd_216778 : Nat := 4983230072969 + 3 ^ 40 * 216778 * 2
def baseEnd_216778 : Nat := 610761642361909952143

theorem tailTrace_216778 : CollatzResearch.WordTrace tailWord_216778 prefixEnd_216778 610761642361909952143 := by
  unfold tailWord_216778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976635802164450894994747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5271028805771869053319325 1976635802164450894994747)
  ·
    refine ⟨2964953703246676342492121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1976635802164450894994747 2964953703246676342492121)
    ·
      refine ⟨2223715277435007256869091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2964953703246676342492121 2223715277435007256869091)
      ·
        refine ⟨3335572916152510885303637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223715277435007256869091 3335572916152510885303637)
        ·
          refine ⟨610761642361909952143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 3335572916152510885303637 610761642361909952143)
          ·
            rfl

theorem cell21_216778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 14].length) (baseStart_216778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216778 prefixEnd_216778 := by exact prefixLift 216778
  have htrace : WordTrace (prefixWord ++ tailWord_216778) baseStart_216778 baseEnd_216778 := by
    simpa [prefixWord, tailWord_216778, baseEnd_216778] using wordTrace_append hprefix tailTrace_216778
  have hstable : (prefixWord ++ tailWord_216778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216778).length < 2 ^ (prefixWord ++ tailWord_216778).sum := by decide
  have hdescent : baseEnd_216778 < baseStart_216778 := by decide
  rcases family_descends (prefixWord ++ tailWord_216778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216840 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_216840 : Nat := 118140960795 + 216840 * 2 ^ 59
def prefixEnd_216840 : Nat := 4983230072969 + 3 ^ 40 * 216840 * 2
def baseEnd_216840 : Nat := 49485842276016376090123

theorem tailTrace_216840 : CollatzResearch.WordTrace tailWord_216840 prefixEnd_216840 49485842276016376090123 := by
  unfold tailWord_216840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954402267216594084367987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5272536356288792112490649 3954402267216594084367987)
  ·
    refine ⟨5931603400824891126551981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954402267216594084367987 5931603400824891126551981)
    ·
      refine ⟨2224351275309334172456993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5931603400824891126551981 2224351275309334172456993)
      ·
        refine ⟨1668263456482000629342745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224351275309334172456993 1668263456482000629342745)
        ·
          refine ⟨1251197592361500472007059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668263456482000629342745 1251197592361500472007059)
          ·
            refine ⟨1876796388542250708010589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251197592361500472007059 1876796388542250708010589)
            ·
              refine ⟨703798645703344015503971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1876796388542250708010589 703798645703344015503971)
              ·
                refine ⟨1055697968555016023255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703798645703344015503971 1055697968555016023255957)
                ·
                  refine ⟨49485842276016376090123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1055697968555016023255957 49485842276016376090123)
                  ·
                    rfl

theorem cell21_216840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_216840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216840 prefixEnd_216840 := by exact prefixLift 216840
  have htrace : WordTrace (prefixWord ++ tailWord_216840) baseStart_216840 baseEnd_216840 := by
    simpa [prefixWord, tailWord_216840, baseEnd_216840] using wordTrace_append hprefix tailTrace_216840
  have hstable : (prefixWord ++ tailWord_216840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216840).length < 2 ^ (prefixWord ++ tailWord_216840).sum := by decide
  have hdescent : baseEnd_216840 < baseStart_216840 := by decide
  rcases family_descends (prefixWord ++ tailWord_216840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216978 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_216978 : Nat := 118140960795 + 216978 * 2 ^ 59
def prefixEnd_216978 : Nat := 4983230072969 + 3 ^ 40 * 216978 * 2
def baseEnd_216978 : Nat := 49517335756158802789841

theorem tailTrace_216978 : CollatzResearch.WordTrace tailWord_216978 prefixEnd_216978 49517335756158802789841 := by
  unfold tailWord_216978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978459451983309434314897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5275891871955491824839725 1978459451983309434314897)
  ·
    refine ⟨1483844588987482075736173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1978459451983309434314897 1483844588987482075736173)
    ·
      refine ⟨556441720870305778401065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1483844588987482075736173 556441720870305778401065)
      ·
        refine ⟨417331290652729333800799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556441720870305778401065 417331290652729333800799)
        ·
          refine ⟨625996935979094000701199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417331290652729333800799 625996935979094000701199)
          ·
            refine ⟨938995403968641001051799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625996935979094000701199 938995403968641001051799)
            ·
              refine ⟨1408493105952961501577699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938995403968641001051799 1408493105952961501577699)
              ·
                refine ⟨2112739658929442252366549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408493105952961501577699 2112739658929442252366549)
                ·
                  refine ⟨49517335756158802789841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2112739658929442252366549 49517335756158802789841)
                  ·
                    rfl

theorem cell21_216978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_216978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_216978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_216978 prefixEnd_216978 := by exact prefixLift 216978
  have htrace : WordTrace (prefixWord ++ tailWord_216978) baseStart_216978 baseEnd_216978 := by
    simpa [prefixWord, tailWord_216978, baseEnd_216978] using wordTrace_append hprefix tailTrace_216978
  have hstable : (prefixWord ++ tailWord_216978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216978).length < 2 ^ (prefixWord ++ tailWord_216978).sum := by decide
  have hdescent : baseEnd_216978 < baseStart_216978 := by decide
  rcases family_descends (prefixWord ++ tailWord_216978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217009 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_217009 : Nat := 118140960795 + 217009 * 2 ^ 59
def prefixEnd_217009 : Nat := 4983230072969 + 3 ^ 40 * 217009 * 2
def baseEnd_217009 : Nat := 49524410378509637773111

theorem tailTrace_217009 : CollatzResearch.WordTrace tailWord_217009 prefixEnd_217009 49524410378509637773111 := by
  unfold tailWord_217009
  simp only [CollatzResearch.WordTrace]
  refine ⟨7914968470820930031638081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5276645647213953354425387 7914968470820930031638081)
  ·
    refine ⟨5936226353115697523728561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7914968470820930031638081 5936226353115697523728561)
    ·
      refine ⟨4452169764836773142796421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5936226353115697523728561 4452169764836773142796421)
      ·
        refine ⟨834781830906894964274329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4452169764836773142796421 834781830906894964274329)
        ·
          refine ⟨626086373180171223205747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834781830906894964274329 626086373180171223205747)
          ·
            refine ⟨939129559770256834808621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626086373180171223205747 939129559770256834808621)
            ·
              refine ⟨352173584913846313053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 939129559770256834808621 352173584913846313053233)
              ·
                refine ⟨264130188685384734789925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352173584913846313053233 264130188685384734789925)
                ·
                  refine ⟨49524410378509637773111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264130188685384734789925 49524410378509637773111)
                  ·
                    rfl

theorem cell21_217009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_217009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217009 prefixEnd_217009 := by exact prefixLift 217009
  have htrace : WordTrace (prefixWord ++ tailWord_217009) baseStart_217009 baseEnd_217009 := by
    simpa [prefixWord, tailWord_217009, baseEnd_217009] using wordTrace_append hprefix tailTrace_217009
  have hstable : (prefixWord ++ tailWord_217009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217009).length < 2 ^ (prefixWord ++ tailWord_217009).sum := by decide
  have hdescent : baseEnd_217009 < baseStart_217009 := by decide
  rcases family_descends (prefixWord ++ tailWord_217009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217012 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_217012 : Nat := 118140960795 + 217012 * 2 ^ 59
def prefixEnd_217012 : Nat := 4983230072969 + 3 ^ 40 * 217012 * 2
def baseEnd_217012 : Nat := 49525095019382299223105

theorem tailTrace_217012 : CollatzResearch.WordTrace tailWord_217012 prefixEnd_217012 49525095019382299223105 := by
  unfold tailWord_217012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957538944905030771998645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5276718593206707695998193 3957538944905030771998645)
  ·
    refine ⟨371019276084846634874873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3957538944905030771998645 371019276084846634874873)
    ·
      refine ⟨278264457063634976156155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371019276084846634874873 278264457063634976156155)
      ·
        refine ⟨417396685595452464234233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278264457063634976156155 417396685595452464234233)
        ·
          refine ⟨313047514196589348175675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417396685595452464234233 313047514196589348175675)
          ·
            refine ⟨469571271294884022263513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313047514196589348175675 469571271294884022263513)
            ·
              refine ⟨352178453471163016697635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469571271294884022263513 352178453471163016697635)
              ·
                refine ⟨528267680206744525046453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352178453471163016697635 528267680206744525046453)
                ·
                  refine ⟨49525095019382299223105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528267680206744525046453 49525095019382299223105)
                  ·
                    rfl

theorem cell21_217012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_217012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217012 prefixEnd_217012 := by exact prefixLift 217012
  have htrace : WordTrace (prefixWord ++ tailWord_217012) baseStart_217012 baseEnd_217012 := by
    simpa [prefixWord, tailWord_217012, baseEnd_217012] using wordTrace_append hprefix tailTrace_217012
  have hstable : (prefixWord ++ tailWord_217012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217012).length < 2 ^ (prefixWord ++ tailWord_217012).sum := by decide
  have hdescent : baseEnd_217012 < baseStart_217012 := by decide
  rcases family_descends (prefixWord ++ tailWord_217012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217046 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_217046 : Nat := 118140960795 + 217046 * 2 ^ 59
def prefixEnd_217046 : Nat := 4983230072969 + 3 ^ 40 * 217046 * 2
def baseEnd_217046 : Nat := 49532854282605795656369

theorem tailTrace_217046 : CollatzResearch.WordTrace tailWord_217046 prefixEnd_217046 49532854282605795656369 := by
  unfold tailWord_217046
  simp only [CollatzResearch.WordTrace]
  refine ⟨494769873230430334420937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5277545314457923567156661 494769873230430334420937)
  ·
    refine ⟨371077404922822750815703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 494769873230430334420937 371077404922822750815703)
    ·
      refine ⟨556616107384234126223555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371077404922822750815703 556616107384234126223555)
      ·
        refine ⟨834924161076351189335333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556616107384234126223555 834924161076351189335333)
        ·
          refine ⟨156548280201815848000375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 834924161076351189335333 156548280201815848000375)
          ·
            refine ⟨234822420302723772000563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156548280201815848000375 234822420302723772000563)
            ·
              refine ⟨352233630454085658000845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234822420302723772000563 352233630454085658000845)
              ·
                refine ⟨132087611420282121750317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352233630454085658000845 132087611420282121750317)
                ·
                  refine ⟨49532854282605795656369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132087611420282121750317 49532854282605795656369)
                  ·
                    rfl

theorem cell21_217046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_217046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217046 prefixEnd_217046 := by exact prefixLift 217046
  have htrace : WordTrace (prefixWord ++ tailWord_217046) baseStart_217046 baseEnd_217046 := by
    simpa [prefixWord, tailWord_217046, baseEnd_217046] using wordTrace_append hprefix tailTrace_217046
  have hstable : (prefixWord ++ tailWord_217046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217046).length < 2 ^ (prefixWord ++ tailWord_217046).sum := by decide
  have hdescent : baseEnd_217046 < baseStart_217046 := by decide
  rcases family_descends (prefixWord ++ tailWord_217046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217071 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 3]
def baseStart_217071 : Nat := 118140960795 + 217071 * 2 ^ 59
def prefixEnd_217071 : Nat := 4983230072969 + 3 ^ 40 * 217071 * 2
def baseEnd_217071 : Nat := 49538559623211307739651

theorem tailTrace_217071 : CollatzResearch.WordTrace tailWord_217071 prefixEnd_217071 49538559623211307739651 := by
  unfold tailWord_217071
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917229796596314620395067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5278153197730876413596711 7917229796596314620395067)
  ·
    refine ⟨11875844694894471930592601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917229796596314620395067 11875844694894471930592601)
    ·
      refine ⟨8906883521170853947944451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11875844694894471930592601 8906883521170853947944451)
      ·
        refine ⟨13360325281756280921916677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906883521170853947944451 13360325281756280921916677)
        ·
          refine ⟨2505060990329302672859377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13360325281756280921916677 2505060990329302672859377)
          ·
            refine ⟨1878795742746977004644533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505060990329302672859377 1878795742746977004644533)
            ·
              refine ⟨176137100882529094185425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1878795742746977004644533 176137100882529094185425)
              ·
                refine ⟨132102825661896820639069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176137100882529094185425 132102825661896820639069)
                ·
                  refine ⟨49538559623211307739651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132102825661896820639069 49538559623211307739651)
                  ·
                    rfl

theorem cell21_217071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 3].length) (baseStart_217071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217071 prefixEnd_217071 := by exact prefixLift 217071
  have htrace : WordTrace (prefixWord ++ tailWord_217071) baseStart_217071 baseEnd_217071 := by
    simpa [prefixWord, tailWord_217071, baseEnd_217071] using wordTrace_append hprefix tailTrace_217071
  have hstable : (prefixWord ++ tailWord_217071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217071).length < 2 ^ (prefixWord ++ tailWord_217071).sum := by decide
  have hdescent : baseEnd_217071 < baseStart_217071 := by decide
  rcases family_descends (prefixWord ++ tailWord_217071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217085 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 4]
def baseStart_217085 : Nat := 118140960795 + 217085 * 2 ^ 59
def prefixEnd_217085 : Nat := 4983230072969 + 3 ^ 40 * 217085 * 2
def baseEnd_217085 : Nat := 49541754613950394506289

theorem tailTrace_217085 : CollatzResearch.WordTrace tailWord_217085 prefixEnd_217085 49541754613950394506289 := by
  unfold tailWord_217085
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917740418545595011404709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5278493612363730007603139 7917740418545595011404709)
  ·
    refine ⟨1484576328477299064638383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7917740418545595011404709 1484576328477299064638383)
    ·
      refine ⟨2226864492715948596957575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484576328477299064638383 2226864492715948596957575)
      ·
        refine ⟨3340296739073922895436363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226864492715948596957575 3340296739073922895436363)
        ·
          refine ⟨5010445108610884343154545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340296739073922895436363 5010445108610884343154545)
          ·
            refine ⟨3757833831458163257365909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5010445108610884343154545 3757833831458163257365909)
            ·
              refine ⟨176148460849601402689027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3757833831458163257365909 176148460849601402689027)
              ·
                refine ⟨264222691274402104033541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176148460849601402689027 264222691274402104033541)
                ·
                  refine ⟨49541754613950394506289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264222691274402104033541 49541754613950394506289)
                  ·
                    rfl

theorem cell21_217085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_217085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217085 prefixEnd_217085 := by exact prefixLift 217085
  have htrace : WordTrace (prefixWord ++ tailWord_217085) baseStart_217085 baseEnd_217085 := by
    simpa [prefixWord, tailWord_217085, baseEnd_217085] using wordTrace_append hprefix tailTrace_217085
  have hstable : (prefixWord ++ tailWord_217085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217085).length < 2 ^ (prefixWord ++ tailWord_217085).sum := by decide
  have hdescent : baseEnd_217085 < baseStart_217085 := by decide
  rcases family_descends (prefixWord ++ tailWord_217085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217189 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_217189 : Nat := 118140960795 + 217189 * 2 ^ 59
def prefixEnd_217189 : Nat := 4983230072969 + 3 ^ 40 * 217189 * 2
def baseEnd_217189 : Nat := 49565488830869324772743

theorem tailTrace_217189 : CollatzResearch.WordTrace tailWord_217189 prefixEnd_217189 49565488830869324772743 := by
  unfold tailWord_217189
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921533610168820773190621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5281022406779213848793747 7921533610168820773190621)
  ·
    refine ⟨2970575103813307789946483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7921533610168820773190621 2970575103813307789946483)
    ·
      refine ⟨4455862655719961684919725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970575103813307789946483 4455862655719961684919725)
      ·
        refine ⟨1670948495894985631844897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4455862655719961684919725 1670948495894985631844897)
        ·
          refine ⟨1253211371921239223883673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670948495894985631844897 1253211371921239223883673)
          ·
            refine ⟨939908528940929417912755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253211371921239223883673 939908528940929417912755)
            ·
              refine ⟨1409862793411394126869133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939908528940929417912755 1409862793411394126869133)
              ·
                refine ⟨528698547529272797575925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1409862793411394126869133 528698547529272797575925)
                ·
                  refine ⟨49565488830869324772743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528698547529272797575925 49565488830869324772743)
                  ·
                    rfl

theorem cell21_217189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_217189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217189 prefixEnd_217189 := by exact prefixLift 217189
  have htrace : WordTrace (prefixWord ++ tailWord_217189) baseStart_217189 baseEnd_217189 := by
    simpa [prefixWord, tailWord_217189, baseEnd_217189] using wordTrace_append hprefix tailTrace_217189
  have hstable : (prefixWord ++ tailWord_217189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217189).length < 2 ^ (prefixWord ++ tailWord_217189).sum := by decide
  have hdescent : baseEnd_217189 < baseStart_217189 := by decide
  rcases family_descends (prefixWord ++ tailWord_217189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217206 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_217206 : Nat := 118140960795 + 217206 * 2 ^ 59
def prefixEnd_217206 : Nat := 4983230072969 + 3 ^ 40 * 217206 * 2
def baseEnd_217206 : Nat := 49569368462481072989375

theorem tailTrace_217206 : CollatzResearch.WordTrace tailWord_217206 prefixEnd_217206 49569368462481072989375 := by
  unfold tailWord_217206
  simp only [CollatzResearch.WordTrace]
  refine ⟨495134603194202042284967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5281435767404821784372981 495134603194202042284967)
  ·
    refine ⟨742701904791303063427451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495134603194202042284967 742701904791303063427451)
    ·
      refine ⟨1114052857186954595141177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742701904791303063427451 1114052857186954595141177)
      ·
        refine ⟨835539642890215946355883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114052857186954595141177 835539642890215946355883)
        ·
          refine ⟨1253309464335323919533825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835539642890215946355883 1253309464335323919533825)
          ·
            refine ⟨939982098251492939650369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253309464335323919533825 939982098251492939650369)
            ·
              refine ⟨704986573688619704737777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939982098251492939650369 704986573688619704737777)
              ·
                refine ⟨528739930266464778553333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704986573688619704737777 528739930266464778553333)
                ·
                  refine ⟨49569368462481072989375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 528739930266464778553333 49569368462481072989375)
                  ·
                    rfl

theorem cell21_217206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_217206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217206 prefixEnd_217206 := by exact prefixLift 217206
  have htrace : WordTrace (prefixWord ++ tailWord_217206) baseStart_217206 baseEnd_217206 := by
    simpa [prefixWord, tailWord_217206, baseEnd_217206] using wordTrace_append hprefix tailTrace_217206
  have hstable : (prefixWord ++ tailWord_217206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217206).length < 2 ^ (prefixWord ++ tailWord_217206).sum := by decide
  have hdescent : baseEnd_217206 < baseStart_217206 := by decide
  rcases family_descends (prefixWord ++ tailWord_217206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217240 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_217240 : Nat := 118140960795 + 217240 * 2 ^ 59
def prefixEnd_217240 : Nat := 4983230072969 + 3 ^ 40 * 217240 * 2
def baseEnd_217240 : Nat := 49577127725704569422639

theorem tailTrace_217240 : CollatzResearch.WordTrace tailWord_217240 prefixEnd_217240 49577127725704569422639 := by
  unfold tailWord_217240
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961696866492028241648587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5282262488656037655531449 3961696866492028241648587)
  ·
    refine ⟨5942545299738042362472881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961696866492028241648587 5942545299738042362472881)
    ·
      refine ⟨4456908974803531771854661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5942545299738042362472881 4456908974803531771854661)
      ·
        refine ⟨835670432775662207222749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4456908974803531771854661 835670432775662207222749)
        ·
          refine ⟨313376412290873327708531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835670432775662207222749 313376412290873327708531)
          ·
            refine ⟨470064618436309991562797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313376412290873327708531 470064618436309991562797)
            ·
              refine ⟨176274231913616246836049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470064618436309991562797 176274231913616246836049)
              ·
                refine ⟨132205673935212185127037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176274231913616246836049 132205673935212185127037)
                ·
                  refine ⟨49577127725704569422639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132205673935212185127037 49577127725704569422639)
                  ·
                    rfl

theorem cell21_217240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_217240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217240 prefixEnd_217240 := by exact prefixLift 217240
  have htrace : WordTrace (prefixWord ++ tailWord_217240) baseStart_217240 baseEnd_217240 := by
    simpa [prefixWord, tailWord_217240, baseEnd_217240] using wordTrace_append hprefix tailTrace_217240
  have hstable : (prefixWord ++ tailWord_217240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217240).length < 2 ^ (prefixWord ++ tailWord_217240).sum := by decide
  have hdescent : baseEnd_217240 < baseStart_217240 := by decide
  rcases family_descends (prefixWord ++ tailWord_217240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217327 : List Nat := [1, 1, 2, 1, 6, 2, 3, 5]
def baseStart_217327 : Nat := 118140960795 + 217327 * 2 ^ 59
def prefixEnd_217327 : Nat := 4983230072969 + 3 ^ 40 * 217327 * 2
def baseEnd_217327 : Nat := 16532327437003917157487

theorem tailTrace_217327 : CollatzResearch.WordTrace tailWord_217327 prefixEnd_217327 16532327437003917157487 := by
  unfold tailWord_217327
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926566883668870341714235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5284377922445913561142823 7926566883668870341714235)
  ·
    refine ⟨11889850325503305512571353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7926566883668870341714235 11889850325503305512571353)
    ·
      refine ⟨8917387744127479134428515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11889850325503305512571353 8917387744127479134428515)
      ·
        refine ⟨13376081616191218701642773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917387744127479134428515 13376081616191218701642773)
        ·
          refine ⟨627003825758963376639505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13376081616191218701642773 627003825758963376639505)
          ·
            refine ⟨470252869319222532479629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627003825758963376639505 470252869319222532479629)
            ·
              refine ⟨176344825994708449679861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470252869319222532479629 176344825994708449679861)
              ·
                refine ⟨16532327437003917157487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176344825994708449679861 16532327437003917157487)
                ·
                  rfl

theorem cell21_217327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 5].length) (baseStart_217327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_217327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_217327 prefixEnd_217327 := by exact prefixLift 217327
  have htrace : WordTrace (prefixWord ++ tailWord_217327) baseStart_217327 baseEnd_217327 := by
    simpa [prefixWord, tailWord_217327, baseEnd_217327] using wordTrace_append hprefix tailTrace_217327
  have hstable : (prefixWord ++ tailWord_217327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217327).length < 2 ^ (prefixWord ++ tailWord_217327).sum := by decide
  have hdescent : baseEnd_217327 < baseStart_217327 := by decide
  rcases family_descends (prefixWord ++ tailWord_217327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
