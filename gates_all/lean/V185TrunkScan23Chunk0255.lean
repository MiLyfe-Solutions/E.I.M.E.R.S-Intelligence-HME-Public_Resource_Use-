import V185TrunkScan23Chunk0254

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1509154 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1509154 : Nat := 118140960795 + 1509154 * 2 ^ 59
def prefixEnd_1509154 : Nat := 4983230072969 + 3 ^ 40 * 1509154 * 2
def baseEnd_1509154 : Nat := 258307127885164553911511

theorem tailTrace_1509154 : CollatzResearch.WordTrace tailWord_1509154 prefixEnd_1509154 258307127885164553911511 := by
  unfold tailWord_1509154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13760842093650068957085629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36695578916400183885561677 13760842093650068957085629)
  ·
    refine ⟨5160315785118775858907111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13760842093650068957085629 5160315785118775858907111)
    ·
      refine ⟨7740473677678163788360667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5160315785118775858907111 7740473677678163788360667)
      ·
        refine ⟨11610710516517245682541001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7740473677678163788360667 11610710516517245682541001)
        ·
          refine ⟨8708032887387934261905751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11610710516517245682541001 8708032887387934261905751)
          ·
            refine ⟨13062049331081901392858627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8708032887387934261905751 13062049331081901392858627)
            ·
              refine ⟨19593073996622852089287941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062049331081901392858627 19593073996622852089287941)
              ·
                refine ⟨3673701374366784766741489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19593073996622852089287941 3673701374366784766741489)
                ·
                  refine ⟨2755276030775088575056117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3673701374366784766741489 2755276030775088575056117)
                  ·
                    refine ⟨258307127885164553911511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2755276030775088575056117 258307127885164553911511)
                    ·
                      rfl

theorem cell23_1509154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1509154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509154 prefixEnd_1509154 := by exact prefixLift 1509154
  have htrace : WordTrace (prefixWord ++ tailWord_1509154) baseStart_1509154 baseEnd_1509154 := by
    simpa [prefixWord, tailWord_1509154, baseEnd_1509154] using wordTrace_append hprefix tailTrace_1509154
  have hstable : (prefixWord ++ tailWord_1509154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509154).length < 2 ^ (prefixWord ++ tailWord_1509154).sum := by decide
  have hdescent : baseEnd_1509154 < baseStart_1509154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509194 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1509194 : Nat := 118140960795 + 1509194 * 2 ^ 59
def prefixEnd_1509194 : Nat := 4983230072969 + 3 ^ 40 * 1509194 * 2
def baseEnd_1509194 : Nat := 774941922881673505234349

theorem tailTrace_1509194 : CollatzResearch.WordTrace tailWord_1509194 prefixEnd_1509194 774941922881673505234349 := by
  unfold tailWord_1509194
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761206823613840664949659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36696551529636908439865757 13761206823613840664949659)
  ·
    refine ⟨20641810235420760997424489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13761206823613840664949659 20641810235420760997424489)
    ·
      refine ⟨15481357676565570748068367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20641810235420760997424489 15481357676565570748068367)
      ·
        refine ⟨23222036514848356122102551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15481357676565570748068367 23222036514848356122102551)
        ·
          refine ⟨34833054772272534183153827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23222036514848356122102551 34833054772272534183153827)
          ·
            refine ⟨52249582158408801274730741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34833054772272534183153827 52249582158408801274730741)
            ·
              refine ⟨4898398327350825119506007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52249582158408801274730741 4898398327350825119506007)
              ·
                refine ⟨7347597491026237679259011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898398327350825119506007 7347597491026237679259011)
                ·
                  refine ⟨11021396236539356518888517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347597491026237679259011 11021396236539356518888517)
                  ·
                    refine ⟨2066511794351129347291597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11021396236539356518888517 2066511794351129347291597)
                    ·
                      refine ⟨774941922881673505234349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2066511794351129347291597 774941922881673505234349)
                      ·
                        rfl

theorem cell23_1509194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1509194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509194 prefixEnd_1509194 := by exact prefixLift 1509194
  have htrace : WordTrace (prefixWord ++ tailWord_1509194) baseStart_1509194 baseEnd_1509194 := by
    simpa [prefixWord, tailWord_1509194, baseEnd_1509194] using wordTrace_append hprefix tailTrace_1509194
  have hstable : (prefixWord ++ tailWord_1509194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509194).length < 2 ^ (prefixWord ++ tailWord_1509194).sum := by decide
  have hdescent : baseEnd_1509194 < baseStart_1509194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509204 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1509204 : Nat := 118140960795 + 1509204 * 2 ^ 59
def prefixEnd_1509204 : Nat := 4983230072969 + 3 ^ 40 * 1509204 * 2
def baseEnd_1509204 : Nat := 774947057688218466109303

theorem tailTrace_1509204 : CollatzResearch.WordTrace tailWord_1509204 prefixEnd_1509204 774947057688218466109303 := by
  unfold tailWord_1509204
  simp only [CollatzResearch.WordTrace]
  refine ⟨27522596012209567183831333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36696794682946089578441777 27522596012209567183831333)
  ·
    refine ⟨5160486752289293846968375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27522596012209567183831333 5160486752289293846968375)
    ·
      refine ⟨7740730128433940770452563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5160486752289293846968375 7740730128433940770452563)
      ·
        refine ⟨11611095192650911155678845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7740730128433940770452563 11611095192650911155678845)
        ·
          refine ⟨4354160697244091683379567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11611095192650911155678845 4354160697244091683379567)
          ·
            refine ⟨6531241045866137525069351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354160697244091683379567 6531241045866137525069351)
            ·
              refine ⟨9796861568799206287604027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531241045866137525069351 9796861568799206287604027)
              ·
                refine ⟨14695292353198809431406041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9796861568799206287604027 14695292353198809431406041)
                ·
                  refine ⟨11021469264899107073554531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14695292353198809431406041 11021469264899107073554531)
                  ·
                    refine ⟨16532203897348660610331797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11021469264899107073554531 16532203897348660610331797)
                    ·
                      refine ⟨774947057688218466109303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16532203897348660610331797 774947057688218466109303)
                      ·
                        rfl

theorem cell23_1509204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1509204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509204 prefixEnd_1509204 := by exact prefixLift 1509204
  have htrace : WordTrace (prefixWord ++ tailWord_1509204) baseStart_1509204 baseEnd_1509204 := by
    simpa [prefixWord, tailWord_1509204, baseEnd_1509204] using wordTrace_append hprefix tailTrace_1509204
  have hstable : (prefixWord ++ tailWord_1509204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509204).length < 2 ^ (prefixWord ++ tailWord_1509204).sum := by decide
  have hdescent : baseEnd_1509204 < baseStart_1509204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509217 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1509217 : Nat := 118140960795 + 1509217 * 2 ^ 59
def prefixEnd_1509217 : Nat := 4983230072969 + 3 ^ 40 * 1509217 * 2
def baseEnd_1509217 : Nat := 774953732936726915246743

theorem tailTrace_1509217 : CollatzResearch.WordTrace tailWord_1509217 prefixEnd_1509217 774953732936726915246743 := by
  unfold tailWord_1509217
  simp only [CollatzResearch.WordTrace]
  refine ⟨55045666173372037587885905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36697110782248025058590603 55045666173372037587885905)
  ·
    refine ⟨41284249630029028190914429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55045666173372037587885905 41284249630029028190914429)
    ·
      refine ⟨15481593611260885571592911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41284249630029028190914429 15481593611260885571592911)
      ·
        refine ⟨23222390416891328357389367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15481593611260885571592911 23222390416891328357389367)
        ·
          refine ⟨34833585625336992536084051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23222390416891328357389367 34833585625336992536084051)
          ·
            refine ⟨52250378438005488804126077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34833585625336992536084051 52250378438005488804126077)
            ·
              refine ⟨19593891914252058301547279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52250378438005488804126077 19593891914252058301547279)
              ·
                refine ⟨29390837871378087452320919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19593891914252058301547279 29390837871378087452320919)
                ·
                  refine ⟨44086256807067131178481379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29390837871378087452320919 44086256807067131178481379)
                  ·
                    refine ⟨66129385210600696767722069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44086256807067131178481379 66129385210600696767722069)
                    ·
                      refine ⟨774953732936726915246743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66129385210600696767722069 774953732936726915246743)
                      ·
                        rfl

theorem cell23_1509217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1509217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509217 prefixEnd_1509217 := by exact prefixLift 1509217
  have htrace : WordTrace (prefixWord ++ tailWord_1509217) baseStart_1509217 baseEnd_1509217 := by
    simpa [prefixWord, tailWord_1509217, baseEnd_1509217] using wordTrace_append hprefix tailTrace_1509217
  have hstable : (prefixWord ++ tailWord_1509217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509217).length < 2 ^ (prefixWord ++ tailWord_1509217).sum := by decide
  have hdescent : baseEnd_1509217 < baseStart_1509217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509218 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1509218 : Nat := 118140960795 + 1509218 * 2 ^ 59
def prefixEnd_1509218 : Nat := 4983230072969 + 3 ^ 40 * 1509218 * 2
def baseEnd_1509218 : Nat := 258318082139127137111413

theorem tailTrace_1509218 : CollatzResearch.WordTrace tailWord_1509218 prefixEnd_1509218 258318082139127137111413 := by
  unfold tailWord_1509218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761425661592103689668077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36697135097578943172448205 13761425661592103689668077)
  ·
    refine ⟨5160534623097038883625529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13761425661592103689668077 5160534623097038883625529)
    ·
      refine ⟨3870400967322779162719147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5160534623097038883625529 3870400967322779162719147)
      ·
        refine ⟨5805601450984168744078721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870400967322779162719147 5805601450984168744078721)
        ·
          refine ⟨4354201088238126558059041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805601450984168744078721 4354201088238126558059041)
          ·
            refine ⟨3265650816178594918544281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4354201088238126558059041 3265650816178594918544281)
            ·
              refine ⟨2449238112133946188908211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3265650816178594918544281 2449238112133946188908211)
              ·
                refine ⟨3673857168200919283362317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449238112133946188908211 3673857168200919283362317)
                ·
                  refine ⟨1377696438075344731260869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3673857168200919283362317 1377696438075344731260869)
                  ·
                    refine ⟨258318082139127137111413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1377696438075344731260869 258318082139127137111413)
                    ·
                      rfl

theorem cell23_1509218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1509218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509218 prefixEnd_1509218 := by exact prefixLift 1509218
  have htrace : WordTrace (prefixWord ++ tailWord_1509218) baseStart_1509218 baseEnd_1509218 := by
    simpa [prefixWord, tailWord_1509218, baseEnd_1509218] using wordTrace_append hprefix tailTrace_1509218
  have hstable : (prefixWord ++ tailWord_1509218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509218).length < 2 ^ (prefixWord ++ tailWord_1509218).sum := by decide
  have hdescent : baseEnd_1509218 < baseStart_1509218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509241 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 3]
def baseStart_1509241 : Nat := 118140960795 + 1509241 * 2 ^ 59
def prefixEnd_1509241 : Nat := 4983230072969 + 3 ^ 40 * 1509241 * 2
def baseEnd_1509241 : Nat := 774966056472434821346633

theorem tailTrace_1509241 : CollatzResearch.WordTrace tailWord_1509241 prefixEnd_1509241 774966056472434821346633 := by
  unfold tailWord_1509241
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046541525285089686759577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36697694350190059791173051 55046541525285089686759577)
  ·
    refine ⟨41284906143963817265069683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55046541525285089686759577 41284906143963817265069683)
    ·
      refine ⟨61927359215945725897604525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41284906143963817265069683 61927359215945725897604525)
      ·
        refine ⟨23222759705979647211601697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61927359215945725897604525 23222759705979647211601697)
        ·
          refine ⟨17417069779484735408701273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23222759705979647211601697 17417069779484735408701273)
          ·
            refine ⟨13062802334613551556525955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17417069779484735408701273 13062802334613551556525955)
            ·
              refine ⟨19594203501920327334788933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13062802334613551556525955 19594203501920327334788933)
              ·
                refine ⟨3673913156610061375272925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19594203501920327334788933 3673913156610061375272925)
                ·
                  refine ⟨1377717433728773015727347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3673913156610061375272925 1377717433728773015727347)
                  ·
                    refine ⟨2066576150593159523591021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1377717433728773015727347 2066576150593159523591021)
                    ·
                      refine ⟨774966056472434821346633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2066576150593159523591021 774966056472434821346633)
                      ·
                        rfl

theorem cell23_1509241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_1509241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509241 prefixEnd_1509241 := by exact prefixLift 1509241
  have htrace : WordTrace (prefixWord ++ tailWord_1509241) baseStart_1509241 baseEnd_1509241 := by
    simpa [prefixWord, tailWord_1509241, baseEnd_1509241] using wordTrace_append hprefix tailTrace_1509241
  have hstable : (prefixWord ++ tailWord_1509241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509241).length < 2 ^ (prefixWord ++ tailWord_1509241).sum := by decide
  have hdescent : baseEnd_1509241 < baseStart_1509241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509251 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 5, 2]
def baseStart_1509251 : Nat := 118140960795 + 1509251 * 2 ^ 59
def prefixEnd_1509251 : Nat := 4983230072969 + 3 ^ 40 * 1509251 * 2
def baseEnd_1509251 : Nat := 774971191278979782221587

theorem tailTrace_1509251 : CollatzResearch.WordTrace tailWord_1509251 prefixEnd_1509251 774971191278979782221587 := by
  unfold tailWord_1509251
  simp only [CollatzResearch.WordTrace]
  refine ⟨55046906255248861394623607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36697937503499240929749071 55046906255248861394623607)
  ·
    refine ⟨82570359382873292091935411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55046906255248861394623607 82570359382873292091935411)
    ·
      refine ⟨123855539074309938137903117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82570359382873292091935411 123855539074309938137903117)
      ·
        refine ⟨46445827152866226801713669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123855539074309938137903117 46445827152866226801713669)
        ·
          refine ⟨8708592591162417525321313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46445827152866226801713669 8708592591162417525321313)
          ·
            refine ⟨6531444443371813143990985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8708592591162417525321313 6531444443371813143990985)
            ·
              refine ⟨4898583332528859857993239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6531444443371813143990985 4898583332528859857993239)
              ·
                refine ⟨7347874998793289786989859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898583332528859857993239 7347874998793289786989859)
                ·
                  refine ⟨11021812498189934680484789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347874998793289786989859 11021812498189934680484789)
                  ·
                    refine ⟨1033294921705306376295449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11021812498189934680484789 1033294921705306376295449)
                    ·
                      refine ⟨774971191278979782221587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033294921705306376295449 774971191278979782221587)
                      ·
                        rfl

theorem cell23_1509251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_1509251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509251 prefixEnd_1509251 := by exact prefixLift 1509251
  have htrace : WordTrace (prefixWord ++ tailWord_1509251) baseStart_1509251 baseEnd_1509251 := by
    simpa [prefixWord, tailWord_1509251, baseEnd_1509251] using wordTrace_append hprefix tailTrace_1509251
  have hstable : (prefixWord ++ tailWord_1509251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509251).length < 2 ^ (prefixWord ++ tailWord_1509251).sum := by decide
  have hdescent : baseEnd_1509251 < baseStart_1509251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509268 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1509268 : Nat := 118140960795 + 1509268 * 2 ^ 59
def prefixEnd_1509268 : Nat := 4983230072969 + 3 ^ 40 * 1509268 * 2
def baseEnd_1509268 : Nat := 774979920450106215709009

theorem tailTrace_1509268 : CollatzResearch.WordTrace tailWord_1509268 prefixEnd_1509268 774979920450106215709009 := by
  unfold tailWord_1509268
  simp only [CollatzResearch.WordTrace]
  refine ⟨27523763148093636648996229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36698350864124848865328305 27523763148093636648996229)
  ·
    refine ⟨5160705590267556871686793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27523763148093636648996229 5160705590267556871686793)
    ·
      refine ⟨3870529192700667653765095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5160705590267556871686793 3870529192700667653765095)
      ·
        refine ⟨5805793789051001480647643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870529192700667653765095 5805793789051001480647643)
        ·
          refine ⟨8708690683576502220971465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805793789051001480647643 8708690683576502220971465)
          ·
            refine ⟨6531518012682376665728599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8708690683576502220971465 6531518012682376665728599)
            ·
              refine ⟨9797277019023564998592899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531518012682376665728599 9797277019023564998592899)
              ·
                refine ⟨14695915528535347497889349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9797277019023564998592899 14695915528535347497889349)
                ·
                  refine ⟨2755484161600377655854253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14695915528535347497889349 2755484161600377655854253)
                  ·
                    refine ⟨1033306560600141620945345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2755484161600377655854253 1033306560600141620945345)
                    ·
                      refine ⟨774979920450106215709009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033306560600141620945345 774979920450106215709009)
                      ·
                        rfl

theorem cell23_1509268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1509268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509268 prefixEnd_1509268 := by exact prefixLift 1509268
  have htrace : WordTrace (prefixWord ++ tailWord_1509268) baseStart_1509268 baseEnd_1509268 := by
    simpa [prefixWord, tailWord_1509268, baseEnd_1509268] using wordTrace_append hprefix tailTrace_1509268
  have hstable : (prefixWord ++ tailWord_1509268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509268).length < 2 ^ (prefixWord ++ tailWord_1509268).sum := by decide
  have hdescent : baseEnd_1509268 < baseStart_1509268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509298 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_1509298 : Nat := 118140960795 + 1509298 * 2 ^ 59
def prefixEnd_1509298 : Nat := 4983230072969 + 3 ^ 40 * 1509298 * 2
def baseEnd_1509298 : Nat := 774995324869741098333871

theorem tailTrace_1509298 : CollatzResearch.WordTrace tailWord_1509298 prefixEnd_1509298 774995324869741098333871 := by
  unfold tailWord_1509298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13762155121519647105396137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36699080324052392281056365 13762155121519647105396137)
  ·
    refine ⟨10321616341139735329047103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13762155121519647105396137 10321616341139735329047103)
    ·
      refine ⟨15482424511709602993570655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321616341139735329047103 15482424511709602993570655)
      ·
        refine ⟨23223636767564404490355983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15482424511709602993570655 23223636767564404490355983)
        ·
          refine ⟨34835455151346606735533975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23223636767564404490355983 34835455151346606735533975)
          ·
            refine ⟨52253182727019910103300963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34835455151346606735533975 52253182727019910103300963)
            ·
              refine ⟨78379774090529865154951445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52253182727019910103300963 78379774090529865154951445)
              ·
                refine ⟨3674051910493587429138349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78379774090529865154951445 3674051910493587429138349)
                ·
                  refine ⟨1377769466435095285926881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3674051910493587429138349 1377769466435095285926881)
                  ·
                    refine ⟨1033327099826321464445161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377769466435095285926881 1033327099826321464445161)
                    ·
                      refine ⟨774995324869741098333871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033327099826321464445161 774995324869741098333871)
                      ·
                        rfl

theorem cell23_1509298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_1509298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509298 prefixEnd_1509298 := by exact prefixLift 1509298
  have htrace : WordTrace (prefixWord ++ tailWord_1509298) baseStart_1509298 baseEnd_1509298 := by
    simpa [prefixWord, tailWord_1509298, baseEnd_1509298] using wordTrace_append hprefix tailTrace_1509298
  have hstable : (prefixWord ++ tailWord_1509298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509298).length < 2 ^ (prefixWord ++ tailWord_1509298).sum := by decide
  have hdescent : baseEnd_1509298 < baseStart_1509298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509308 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1509308 : Nat := 118140960795 + 1509308 * 2 ^ 59
def prefixEnd_1509308 : Nat := 4983230072969 + 3 ^ 40 * 1509308 * 2
def baseEnd_1509308 : Nat := 258333486558762019736275

theorem tailTrace_1509308 : CollatzResearch.WordTrace tailWord_1509308 prefixEnd_1509308 258333486558762019736275 := by
  unfold tailWord_1509308
  simp only [CollatzResearch.WordTrace]
  refine ⟨27524492608021180064724289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36699323477361573419632385 27524492608021180064724289)
  ·
    refine ⟨20643369456015885048543217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27524492608021180064724289 20643369456015885048543217)
    ·
      refine ⟨15482527092011913786407413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20643369456015885048543217 15482527092011913786407413)
      ·
        refine ⟨1451486914876116917475695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15482527092011913786407413 1451486914876116917475695)
        ·
          refine ⟨2177230372314175376213543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451486914876116917475695 2177230372314175376213543)
          ·
            refine ⟨3265845558471263064320315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177230372314175376213543 3265845558471263064320315)
            ·
              refine ⟨4898768337706894596480473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265845558471263064320315 4898768337706894596480473)
              ·
                refine ⟨3674076253280170947360355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4898768337706894596480473 3674076253280170947360355)
                ·
                  refine ⟨5511114379920256421040533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674076253280170947360355 5511114379920256421040533)
                  ·
                    refine ⟨258333486558762019736275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5511114379920256421040533 258333486558762019736275)
                    ·
                      rfl

theorem cell23_1509308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1509308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509308 prefixEnd_1509308 := by exact prefixLift 1509308
  have htrace : WordTrace (prefixWord ++ tailWord_1509308) baseStart_1509308 baseEnd_1509308 := by
    simpa [prefixWord, tailWord_1509308, baseEnd_1509308] using wordTrace_append hprefix tailTrace_1509308
  have hstable : (prefixWord ++ tailWord_1509308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509308).length < 2 ^ (prefixWord ++ tailWord_1509308).sum := by decide
  have hdescent : baseEnd_1509308 < baseStart_1509308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509332 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_1509332 : Nat := 118140960795 + 1509332 * 2 ^ 59
def prefixEnd_1509332 : Nat := 4983230072969 + 3 ^ 40 * 1509332 * 2
def baseEnd_1509332 : Nat := 775012783211993965308715

theorem tailTrace_1509332 : CollatzResearch.WordTrace tailWord_1509332 prefixEnd_1509332 775012783211993965308715 := by
  unfold tailWord_1509332
  simp only [CollatzResearch.WordTrace]
  refine ⟨27524930283977706114161125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36699907045303608152214833 27524930283977706114161125)
  ·
    refine ⟨5160924428245819896405211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27524930283977706114161125 5160924428245819896405211)
    ·
      refine ⟨7741386642368729844607817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5160924428245819896405211 7741386642368729844607817)
      ·
        refine ⟨5806039981776547383455863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7741386642368729844607817 5806039981776547383455863)
        ·
          refine ⟨8709059972664821075183795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5806039981776547383455863 8709059972664821075183795)
          ·
            refine ⟨13063589958997231612775693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709059972664821075183795 13063589958997231612775693)
            ·
              refine ⟨4898846234623961854790885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13063589958997231612775693 4898846234623961854790885)
              ·
                refine ⟨918533668991992847773291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4898846234623961854790885 918533668991992847773291)
                ·
                  refine ⟨1377800503487989271659937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918533668991992847773291 1377800503487989271659937)
                  ·
                    refine ⟨1033350377615991953744953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1377800503487989271659937 1033350377615991953744953)
                    ·
                      refine ⟨775012783211993965308715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033350377615991953744953 775012783211993965308715)
                      ·
                        rfl

theorem cell23_1509332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_1509332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509332 prefixEnd_1509332 := by exact prefixLift 1509332
  have htrace : WordTrace (prefixWord ++ tailWord_1509332) baseStart_1509332 baseEnd_1509332 := by
    simpa [prefixWord, tailWord_1509332, baseEnd_1509332] using wordTrace_append hprefix tailTrace_1509332
  have hstable : (prefixWord ++ tailWord_1509332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509332).length < 2 ^ (prefixWord ++ tailWord_1509332).sum := by decide
  have hdescent : baseEnd_1509332 < baseStart_1509332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509338 : List Nat := [3, 1, 1, 2, 6, 1, 1, 8]
def baseStart_1509338 : Nat := 118140960795 + 1509338 * 2 ^ 59
def prefixEnd_1509338 : Nat := 4983230072969 + 3 ^ 40 * 1509338 * 2
def baseEnd_1509338 : Nat := 28704291262811886734581

theorem tailTrace_1509338 : CollatzResearch.WordTrace tailWord_1509338 prefixEnd_1509338 28704291262811886734581 := by
  unfold tailWord_1509338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13762519851483418813260167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36700052937289116835360445 13762519851483418813260167)
  ·
    refine ⟨20643779777225128219890251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13762519851483418813260167 20643779777225128219890251)
    ·
      refine ⟨30965669665837692329835377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20643779777225128219890251 30965669665837692329835377)
      ·
        refine ⟨23224252249378269247376533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30965669665837692329835377 23224252249378269247376533)
        ·
          refine ⟨1088636824189606370970775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23224252249378269247376533 1088636824189606370970775)
          ·
            refine ⟨1632955236284409556456163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088636824189606370970775 1632955236284409556456163)
            ·
              refine ⟨2449432854426614334684245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632955236284409556456163 2449432854426614334684245)
              ·
                refine ⟨28704291262811886734581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2449432854426614334684245 28704291262811886734581)
                ·
                  rfl

theorem cell23_1509338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_1509338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509338 prefixEnd_1509338 := by exact prefixLift 1509338
  have htrace : WordTrace (prefixWord ++ tailWord_1509338) baseStart_1509338 baseEnd_1509338 := by
    simpa [prefixWord, tailWord_1509338, baseEnd_1509338] using wordTrace_append hprefix tailTrace_1509338
  have hstable : (prefixWord ++ tailWord_1509338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509338).length < 2 ^ (prefixWord ++ tailWord_1509338).sum := by decide
  have hdescent : baseEnd_1509338 < baseStart_1509338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509348 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_1509348 : Nat := 118140960795 + 1509348 * 2 ^ 59
def prefixEnd_1509348 : Nat := 4983230072969 + 3 ^ 40 * 1509348 * 2
def baseEnd_1509348 : Nat := 775020998902465902708641

theorem tailTrace_1509348 : CollatzResearch.WordTrace tailWord_1509348 prefixEnd_1509348 775020998902465902708641 := by
  unfold tailWord_1509348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27525222067948723480452349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36700296090598297973936465 27525222067948723480452349)
  ·
    refine ⟨10321958275480771305169631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27525222067948723480452349 10321958275480771305169631)
    ·
      refine ⟨15482937413221156957754447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321958275480771305169631 15482937413221156957754447)
      ·
        refine ⟨23224406119831735436631671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15482937413221156957754447 23224406119831735436631671)
        ·
          refine ⟨34836609179747603154947507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23224406119831735436631671 34836609179747603154947507)
          ·
            refine ⟨52254913769621404732421261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34836609179747603154947507 52254913769621404732421261)
            ·
              refine ⟨19595592663608026774657973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52254913769621404732421261 19595592663608026774657973)
              ·
                refine ⟨1837086812213252510124185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19595592663608026774657973 1837086812213252510124185)
                ·
                  refine ⟨1377815109159939382593139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837086812213252510124185 1377815109159939382593139)
                  ·
                    refine ⟨2066722663739909073889709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1377815109159939382593139 2066722663739909073889709)
                    ·
                      refine ⟨775020998902465902708641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2066722663739909073889709 775020998902465902708641)
                      ·
                        rfl

theorem cell23_1509348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_1509348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509348 prefixEnd_1509348 := by exact prefixLift 1509348
  have htrace : WordTrace (prefixWord ++ tailWord_1509348) baseStart_1509348 baseEnd_1509348 := by
    simpa [prefixWord, tailWord_1509348, baseEnd_1509348] using wordTrace_append hprefix tailTrace_1509348
  have hstable : (prefixWord ++ tailWord_1509348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509348).length < 2 ^ (prefixWord ++ tailWord_1509348).sum := by decide
  have hdescent : baseEnd_1509348 < baseStart_1509348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509405 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_1509405 : Nat := 118140960795 + 1509405 * 2 ^ 59
def prefixEnd_1509405 : Nat := 4983230072969 + 3 ^ 40 * 1509405 * 2
def baseEnd_1509405 : Nat := 775050267299772179695879

theorem tailTrace_1509405 : CollatzResearch.WordTrace tailWord_1509405 prefixEnd_1509405 775050267299772179695879 := by
  unfold tailWord_1509405
  simp only [CollatzResearch.WordTrace]
  refine ⟨55052523096690945695729669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36701682064460630463819779 55052523096690945695729669)
  ·
    refine ⟨10322348080629552317949313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55052523096690945695729669 10322348080629552317949313)
    ·
      refine ⟨7741761060472164238461985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10322348080629552317949313 7741761060472164238461985)
      ·
        refine ⟨5806320795354123178846489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7741761060472164238461985 5806320795354123178846489)
        ·
          refine ⟨4354740596515592384134867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5806320795354123178846489 4354740596515592384134867)
          ·
            refine ⟨6532110894773388576202301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354740596515592384134867 6532110894773388576202301)
            ·
              refine ⟨2449541585540020716075863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6532110894773388576202301 2449541585540020716075863)
              ·
                refine ⟨3674312378310031074113795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449541585540020716075863 3674312378310031074113795)
                ·
                  refine ⟨5511468567465046611170693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674312378310031074113795 5511468567465046611170693)
                  ·
                    refine ⟨1033400356399696239594505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5511468567465046611170693 1033400356399696239594505)
                    ·
                      refine ⟨775050267299772179695879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033400356399696239594505 775050267299772179695879)
                      ·
                        rfl

theorem cell23_1509405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_1509405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509405 prefixEnd_1509405 := by exact prefixLift 1509405
  have htrace : WordTrace (prefixWord ++ tailWord_1509405) baseStart_1509405 baseEnd_1509405 := by
    simpa [prefixWord, tailWord_1509405, baseEnd_1509405] using wordTrace_append hprefix tailTrace_1509405
  have hstable : (prefixWord ++ tailWord_1509405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509405).length < 2 ^ (prefixWord ++ tailWord_1509405).sum := by decide
  have hdescent : baseEnd_1509405 < baseStart_1509405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509531 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 3, 5]
def baseStart_1509531 : Nat := 118140960795 + 1509531 * 2 ^ 59
def prefixEnd_1509531 : Nat := 4983230072969 + 3 ^ 40 * 1509531 * 2
def baseEnd_1509531 : Nat := 258371655287412895573433

theorem tailTrace_1509531 : CollatzResearch.WordTrace tailWord_1509531 prefixEnd_1509531 258371655287412895573433 := by
  unfold tailWord_1509531
  simp only [CollatzResearch.WordTrace]
  refine ⟨55057118694234469214816447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36704745796156312809877631 55057118694234469214816447)
  ·
    refine ⟨82585678041351703822224671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55057118694234469214816447 82585678041351703822224671)
    ·
      refine ⟨123878517062027555733337007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82585678041351703822224671 123878517062027555733337007)
      ·
        refine ⟨185817775593041333600005511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123878517062027555733337007 185817775593041333600005511)
        ·
          refine ⟨278726663389562000400008267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185817775593041333600005511 278726663389562000400008267)
          ·
            refine ⟨418089995084343000600012401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278726663389562000400008267 418089995084343000600012401)
            ·
              refine ⟨313567496313257250450009301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418089995084343000600012401 313567496313257250450009301)
              ·
                refine ⟨7349238194841966807422093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 313567496313257250450009301 7349238194841966807422093)
                ·
                  refine ⟨2755964323065737552783285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7349238194841966807422093 2755964323065737552783285)
                  ·
                    refine ⟨258371655287412895573433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2755964323065737552783285 258371655287412895573433)
                    ·
                      rfl

theorem cell23_1509531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 5].length) (baseStart_1509531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509531 prefixEnd_1509531 := by exact prefixLift 1509531
  have htrace : WordTrace (prefixWord ++ tailWord_1509531) baseStart_1509531 baseEnd_1509531 := by
    simpa [prefixWord, tailWord_1509531, baseEnd_1509531] using wordTrace_append hprefix tailTrace_1509531
  have hstable : (prefixWord ++ tailWord_1509531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509531).length < 2 ^ (prefixWord ++ tailWord_1509531).sum := by decide
  have hdescent : baseEnd_1509531 < baseStart_1509531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509556 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1509556 : Nat := 118140960795 + 1509556 * 2 ^ 59
def prefixEnd_1509556 : Nat := 4983230072969 + 3 ^ 40 * 1509556 * 2
def baseEnd_1509556 : Nat := 258375934292867029635895

theorem tailTrace_1509556 : CollatzResearch.WordTrace tailWord_1509556 prefixEnd_1509556 258375934292867029635895 := by
  unfold tailWord_1509556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529015259571949242238261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36705353679429265656317681 27529015259571949242238261)
  ·
    refine ⟨2580845180584870241459837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27529015259571949242238261 2580845180584870241459837)
    ·
      refine ⟨967816942719326340547439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2580845180584870241459837 967816942719326340547439)
      ·
        refine ⟨1451725414078989510821159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967816942719326340547439 1451725414078989510821159)
        ·
          refine ⟨2177588121118484266231739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451725414078989510821159 2177588121118484266231739)
          ·
            refine ⟨3266382181677726399347609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177588121118484266231739 3266382181677726399347609)
            ·
              refine ⟨2449786636258294799510707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266382181677726399347609 2449786636258294799510707)
              ·
                refine ⟨3674679954387442199266061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449786636258294799510707 3674679954387442199266061)
                ·
                  refine ⟨1378004982895290824724773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3674679954387442199266061 1378004982895290824724773)
                  ·
                    refine ⟨258375934292867029635895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378004982895290824724773 258375934292867029635895)
                    ·
                      rfl

theorem cell23_1509556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1509556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509556 prefixEnd_1509556 := by exact prefixLift 1509556
  have htrace : WordTrace (prefixWord ++ tailWord_1509556) baseStart_1509556 baseEnd_1509556 := by
    simpa [prefixWord, tailWord_1509556, baseEnd_1509556] using wordTrace_append hprefix tailTrace_1509556
  have hstable : (prefixWord ++ tailWord_1509556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509556).length < 2 ^ (prefixWord ++ tailWord_1509556).sum := by decide
  have hdescent : baseEnd_1509556 < baseStart_1509556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509562 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3]
def baseStart_1509562 : Nat := 118140960795 + 1509562 * 2 ^ 59
def prefixEnd_1509562 : Nat := 4983230072969 + 3 ^ 40 * 1509562 * 2
def baseEnd_1509562 : Nat := 775130883762528065432657

theorem tailTrace_1509562 : CollatzResearch.WordTrace tailWord_1509562 prefixEnd_1509562 775130883762528065432657 := by
  unfold tailWord_1509562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13764562339280540377298735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36705499571414774339463293 13764562339280540377298735)
  ·
    refine ⟨20646843508920810565948103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13764562339280540377298735 20646843508920810565948103)
    ·
      refine ⟨30970265263381215848922155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20646843508920810565948103 30970265263381215848922155)
      ·
        refine ⟨46455397895071823773383233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30970265263381215848922155 46455397895071823773383233)
        ·
          refine ⟨34841548421303867830037425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46455397895071823773383233 34841548421303867830037425)
          ·
            refine ⟨26131161315977900872528069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34841548421303867830037425 26131161315977900872528069)
            ·
              refine ⟨4899592746745856413599013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26131161315977900872528069 4899592746745856413599013)
              ·
                refine ⟨918673640014848077549815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4899592746745856413599013 918673640014848077549815)
                ·
                  refine ⟨1378010460022272116324723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918673640014848077549815 1378010460022272116324723)
                  ·
                    refine ⟨2067015690033408174487085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1378010460022272116324723 2067015690033408174487085)
                    ·
                      refine ⟨775130883762528065432657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2067015690033408174487085 775130883762528065432657)
                      ·
                        rfl

theorem cell23_1509562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_1509562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509562 prefixEnd_1509562 := by exact prefixLift 1509562
  have htrace : WordTrace (prefixWord ++ tailWord_1509562) baseStart_1509562 baseEnd_1509562 := by
    simpa [prefixWord, tailWord_1509562, baseEnd_1509562] using wordTrace_append hprefix tailTrace_1509562
  have hstable : (prefixWord ++ tailWord_1509562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509562).length < 2 ^ (prefixWord ++ tailWord_1509562).sum := by decide
  have hdescent : baseEnd_1509562 < baseStart_1509562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509605 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1509605 : Nat := 118140960795 + 1509605 * 2 ^ 59
def prefixEnd_1509605 : Nat := 4983230072969 + 3 ^ 40 * 1509605 * 2
def baseEnd_1509605 : Nat := 775152963430671397194959

theorem tailTrace_1509605 : CollatzResearch.WordTrace tailWord_1509605 prefixEnd_1509605 775152963430671397194959 := by
  unfold tailWord_1509605
  simp only [CollatzResearch.WordTrace]
  refine ⟨55059817695966379853010269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36706545130644253235340179 55059817695966379853010269)
  ·
    refine ⟨20647431635987392444878851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55059817695966379853010269 20647431635987392444878851)
    ·
      refine ⟨30971147453981088667318277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20647431635987392444878851 30971147453981088667318277)
      ·
        refine ⟨5807090147621454125122177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30971147453981088667318277 5807090147621454125122177)
        ·
          refine ⟨4355317610716090593841633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5807090147621454125122177 4355317610716090593841633)
          ·
            refine ⟨3266488208037067945381225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4355317610716090593841633 3266488208037067945381225)
            ·
              refine ⟨2449866156027800959035919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266488208037067945381225 2449866156027800959035919)
              ·
                refine ⟨3674799234041701438553879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449866156027800959035919 3674799234041701438553879)
                ·
                  refine ⟨5512198851062552157830819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3674799234041701438553879 5512198851062552157830819)
                  ·
                    refine ⟨8268298276593828236746229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5512198851062552157830819 8268298276593828236746229)
                    ·
                      refine ⟨775152963430671397194959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8268298276593828236746229 775152963430671397194959)
                      ·
                        rfl

theorem cell23_1509605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1509605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509605 prefixEnd_1509605 := by exact prefixLift 1509605
  have htrace : WordTrace (prefixWord ++ tailWord_1509605) baseStart_1509605 baseEnd_1509605 := by
    simpa [prefixWord, tailWord_1509605, baseEnd_1509605] using wordTrace_append hprefix tailTrace_1509605
  have hstable : (prefixWord ++ tailWord_1509605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509605).length < 2 ^ (prefixWord ++ tailWord_1509605).sum := by decide
  have hdescent : baseEnd_1509605 < baseStart_1509605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509608 : List Nat := [2, 1, 4, 1, 2, 4, 9]
def baseStart_1509608 : Nat := 118140960795 + 1509608 * 2 ^ 59
def prefixEnd_1509608 : Nat := 4983230072969 + 3 ^ 40 * 1509608 * 2
def baseEnd_1509608 : Nat := 9569808689785615869845

theorem tailTrace_1509608 : CollatzResearch.WordTrace tailWord_1509608 prefixEnd_1509608 9569808689785615869845 := by
  unfold tailWord_1509608
  simp only [CollatzResearch.WordTrace]
  refine ⟨27529963557477755682684739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36706618076637007576912985 27529963557477755682684739)
  ·
    refine ⟨41294945336216633524027109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27529963557477755682684739 41294945336216633524027109)
    ·
      refine ⟨7742802250540618785755083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41294945336216633524027109 7742802250540618785755083)
      ·
        refine ⟨11614203375810928178632625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7742802250540618785755083 11614203375810928178632625)
        ·
          refine ⟨8710652531858196133974469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11614203375810928178632625 8710652531858196133974469)
          ·
            refine ⟨1633247349723411775120213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8710652531858196133974469 1633247349723411775120213)
            ·
              refine ⟨9569808689785615869845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1633247349723411775120213 9569808689785615869845)
              ·
                rfl

theorem cell23_1509608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 9].length) (baseStart_1509608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509608 prefixEnd_1509608 := by exact prefixLift 1509608
  have htrace : WordTrace (prefixWord ++ tailWord_1509608) baseStart_1509608 baseEnd_1509608 := by
    simpa [prefixWord, tailWord_1509608, baseEnd_1509608] using wordTrace_append hprefix tailTrace_1509608
  have hstable : (prefixWord ++ tailWord_1509608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509608).length < 2 ^ (prefixWord ++ tailWord_1509608).sum := by decide
  have hdescent : baseEnd_1509608 < baseStart_1509608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509669 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_1509669 : Nat := 118140960795 + 1509669 * 2 ^ 59
def prefixEnd_1509669 : Nat := 4983230072969 + 3 ^ 40 * 1509669 * 2
def baseEnd_1509669 : Nat := 775185826192559146794665

theorem tailTrace_1509669 : CollatzResearch.WordTrace tailWord_1509669 prefixEnd_1509669 775185826192559146794665 := by
  unfold tailWord_1509669
  simp only [CollatzResearch.WordTrace]
  refine ⟨55062151967734518783340061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36708101311823012522226707 55062151967734518783340061)
  ·
    refine ⟨20648306987900444543752523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55062151967734518783340061 20648306987900444543752523)
    ·
      refine ⟨30972460481850666815628785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20648306987900444543752523 30972460481850666815628785)
      ·
        refine ⟨23229345361388000111721589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30972460481850666815628785 23229345361388000111721589)
        ·
          refine ⟨2177751127630125010473899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23229345361388000111721589 2177751127630125010473899)
          ·
            refine ⟨3266626691445187515710849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177751127630125010473899 3266626691445187515710849)
            ·
              refine ⟨2449970018583890636783137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266626691445187515710849 2449970018583890636783137)
              ·
                refine ⟨1837477513937917977587353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2449970018583890636783137 1837477513937917977587353)
                ·
                  refine ⟨1378108135453438483190515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837477513937917977587353 1378108135453438483190515)
                  ·
                    refine ⟨2067162203180157724785773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1378108135453438483190515 2067162203180157724785773)
                    ·
                      refine ⟨775185826192559146794665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2067162203180157724785773 775185826192559146794665)
                      ·
                        rfl

theorem cell23_1509669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_1509669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509669 prefixEnd_1509669 := by exact prefixLift 1509669
  have htrace : WordTrace (prefixWord ++ tailWord_1509669) baseStart_1509669 baseEnd_1509669 := by
    simpa [prefixWord, tailWord_1509669, baseEnd_1509669] using wordTrace_append hprefix tailTrace_1509669
  have hstable : (prefixWord ++ tailWord_1509669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509669).length < 2 ^ (prefixWord ++ tailWord_1509669).sum := by decide
  have hdescent : baseEnd_1509669 < baseStart_1509669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509688 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1509688 : Nat := 118140960795 + 1509688 * 2 ^ 59
def prefixEnd_1509688 : Nat := 4983230072969 + 3 ^ 40 * 1509688 * 2
def baseEnd_1509688 : Nat := 775195582324994572457077

theorem tailTrace_1509688 : CollatzResearch.WordTrace tailWord_1509688 prefixEnd_1509688 775195582324994572457077 := by
  unfold tailWord_1509688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27531422477332842514140859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36708563303110456685521145 27531422477332842514140859)
  ·
    refine ⟨41297133715999263771211289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27531422477332842514140859 41297133715999263771211289)
    ·
      refine ⟨30972850286999447828408467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41297133715999263771211289 30972850286999447828408467)
      ·
        refine ⟨46459275430499171742612701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30972850286999447828408467 46459275430499171742612701)
        ·
          refine ⟨17422228286437189403479763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46459275430499171742612701 17422228286437189403479763)
          ·
            refine ⟨26133342429655784105219645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17422228286437189403479763 26133342429655784105219645)
            ·
              refine ⟨9800003411120919039457367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26133342429655784105219645 9800003411120919039457367)
              ·
                refine ⟨14700005116681378559186051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800003411120919039457367 14700005116681378559186051)
                ·
                  refine ⟨22050007675022067838779077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14700005116681378559186051 22050007675022067838779077)
                  ·
                    refine ⟨4134376439066637719771077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22050007675022067838779077 4134376439066637719771077)
                    ·
                      refine ⟨775195582324994572457077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4134376439066637719771077 775195582324994572457077)
                      ·
                        rfl

theorem cell23_1509688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1509688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509688 prefixEnd_1509688 := by exact prefixLift 1509688
  have htrace : WordTrace (prefixWord ++ tailWord_1509688) baseStart_1509688 baseEnd_1509688 := by
    simpa [prefixWord, tailWord_1509688, baseEnd_1509688] using wordTrace_append hprefix tailTrace_1509688
  have hstable : (prefixWord ++ tailWord_1509688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509688).length < 2 ^ (prefixWord ++ tailWord_1509688).sum := by decide
  have hdescent : baseEnd_1509688 < baseStart_1509688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509692 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_1509692 : Nat := 118140960795 + 1509692 * 2 ^ 59
def prefixEnd_1509692 : Nat := 4983230072969 + 3 ^ 40 * 1509692 * 2
def baseEnd_1509692 : Nat := 775197636247612556807059

theorem tailTrace_1509692 : CollatzResearch.WordTrace tailWord_1509692 prefixEnd_1509692 775197636247612556807059 := by
  unfold tailWord_1509692
  simp only [CollatzResearch.WordTrace]
  refine ⟨27531495423325596855713665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36708660564434129140951553 27531495423325596855713665)
  ·
    refine ⟨20648621567494197641785249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27531495423325596855713665 20648621567494197641785249)
    ·
      refine ⟨15486466175620648231338937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20648621567494197641785249 15486466175620648231338937)
      ·
        refine ⟨11614849631715486173504203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15486466175620648231338937 11614849631715486173504203)
        ·
          refine ⟨17422274447573229260256305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11614849631715486173504203 17422274447573229260256305)
          ·
            refine ⟨13066705835679921945192229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17422274447573229260256305 13066705835679921945192229)
            ·
              refine ⟨2450007344189985364723543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13066705835679921945192229 2450007344189985364723543)
              ·
                refine ⟨3675011016284978047085315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450007344189985364723543 3675011016284978047085315)
                ·
                  refine ⟨5512516524427467070627973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675011016284978047085315 5512516524427467070627973)
                  ·
                    refine ⟨1033596848330150075742745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512516524427467070627973 1033596848330150075742745)
                    ·
                      refine ⟨775197636247612556807059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033596848330150075742745 775197636247612556807059)
                      ·
                        rfl

theorem cell23_1509692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_1509692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509692 prefixEnd_1509692 := by exact prefixLift 1509692
  have htrace : WordTrace (prefixWord ++ tailWord_1509692) baseStart_1509692 baseEnd_1509692 := by
    simpa [prefixWord, tailWord_1509692, baseEnd_1509692] using wordTrace_append hprefix tailTrace_1509692
  have hstable : (prefixWord ++ tailWord_1509692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509692).length < 2 ^ (prefixWord ++ tailWord_1509692).sum := by decide
  have hdescent : baseEnd_1509692 < baseStart_1509692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509765 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_1509765 : Nat := 118140960795 + 1509765 * 2 ^ 59
def prefixEnd_1509765 : Nat := 4983230072969 + 3 ^ 40 * 1509765 * 2
def baseEnd_1509765 : Nat := 775235120335390771194223

theorem tailTrace_1509765 : CollatzResearch.WordTrace tailWord_1509765 prefixEnd_1509765 775235120335390771194223 := by
  unfold tailWord_1509765
  simp only [CollatzResearch.WordTrace]
  refine ⟨55065653375386727178834749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36710435583591151452556499 55065653375386727178834749)
  ·
    refine ⟨20649620015770022692063031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55065653375386727178834749 20649620015770022692063031)
    ·
      refine ⟨30974430023655034038094547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20649620015770022692063031 30974430023655034038094547)
      ·
        refine ⟨46461645035482551057141821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30974430023655034038094547 46461645035482551057141821)
        ·
          refine ⟨17423116888305956646428183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46461645035482551057141821 17423116888305956646428183)
          ·
            refine ⟨26134675332458934969642275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17423116888305956646428183 26134675332458934969642275)
            ·
              refine ⟨39202012998688402454463413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26134675332458934969642275 39202012998688402454463413)
              ·
                refine ⟨3675188718627037730105945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39202012998688402454463413 3675188718627037730105945)
                ·
                  refine ⟨2756391538970278297579459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675188718627037730105945 2756391538970278297579459)
                  ·
                    refine ⟨4134587308455417446369189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756391538970278297579459 4134587308455417446369189)
                    ·
                      refine ⟨775235120335390771194223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4134587308455417446369189 775235120335390771194223)
                      ·
                        rfl

theorem cell23_1509765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_1509765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509765 prefixEnd_1509765 := by exact prefixLift 1509765
  have htrace : WordTrace (prefixWord ++ tailWord_1509765) baseStart_1509765 baseEnd_1509765 := by
    simpa [prefixWord, tailWord_1509765, baseEnd_1509765] using wordTrace_append hprefix tailTrace_1509765
  have hstable : (prefixWord ++ tailWord_1509765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509765).length < 2 ^ (prefixWord ++ tailWord_1509765).sum := by decide
  have hdescent : baseEnd_1509765 < baseStart_1509765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509792 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_1509792 : Nat := 118140960795 + 1509792 * 2 ^ 59
def prefixEnd_1509792 : Nat := 4983230072969 + 3 ^ 40 * 1509792 * 2
def baseEnd_1509792 : Nat := 258416328104354055185533

theorem tailTrace_1509792 : CollatzResearch.WordTrace tailWord_1509792 prefixEnd_1509792 258416328104354055185533 := by
  unfold tailWord_1509792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27533319073144455395033815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36711092097525940526711753 27533319073144455395033815)
  ·
    refine ⟨41299978609716683092550723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27533319073144455395033815 41299978609716683092550723)
    ·
      refine ⟨61949967914575024638826085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41299978609716683092550723 61949967914575024638826085)
      ·
        refine ⟨11615618983982817119779891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61949967914575024638826085 11615618983982817119779891)
        ·
          refine ⟨17423428475974225679669837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11615618983982817119779891 17423428475974225679669837)
          ·
            refine ⟨6533785678490334629876189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17423428475974225679669837 6533785678490334629876189)
            ·
              refine ⟨2450169629433875486203571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6533785678490334629876189 2450169629433875486203571)
              ·
                refine ⟨3675254444150813229305357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450169629433875486203571 3675254444150813229305357)
                ·
                  refine ⟨1378220416556554960989509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3675254444150813229305357 1378220416556554960989509)
                  ·
                    refine ⟨258416328104354055185533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378220416556554960989509 258416328104354055185533)
                    ·
                      rfl

theorem cell23_1509792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_1509792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509792 prefixEnd_1509792 := by exact prefixLift 1509792
  have htrace : WordTrace (prefixWord ++ tailWord_1509792) baseStart_1509792 baseEnd_1509792 := by
    simpa [prefixWord, tailWord_1509792, baseEnd_1509792] using wordTrace_append hprefix tailTrace_1509792
  have hstable : (prefixWord ++ tailWord_1509792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509792).length < 2 ^ (prefixWord ++ tailWord_1509792).sum := by decide
  have hdescent : baseEnd_1509792 < baseStart_1509792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509808 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_1509808 : Nat := 118140960795 + 1509808 * 2 ^ 59
def prefixEnd_1509808 : Nat := 4983230072969 + 3 ^ 40 * 1509808 * 2
def baseEnd_1509808 : Nat := 775257200003534102956525

theorem tailTrace_1509808 : CollatzResearch.WordTrace tailWord_1509808 prefixEnd_1509808 775257200003534102956525 := by
  unfold tailWord_1509808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27533610857115472761325039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36711481142820630348433385 27533610857115472761325039)
  ·
    refine ⟨41300416285673209141987559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27533610857115472761325039 41300416285673209141987559)
    ·
      refine ⟨61950624428509813712981339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41300416285673209141987559 61950624428509813712981339)
      ·
        refine ⟨92925936642764720569472009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61950624428509813712981339 92925936642764720569472009)
        ·
          refine ⟨69694452482073540427104007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92925936642764720569472009 69694452482073540427104007)
          ·
            refine ⟨104541678723110310640656011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69694452482073540427104007 104541678723110310640656011)
            ·
              refine ⟨156812518084665465960984017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104541678723110310640656011 156812518084665465960984017)
              ·
                refine ⟨117609388563499099470738013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156812518084665465960984017 117609388563499099470738013)
                ·
                  refine ⟨44103520711312162301526755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117609388563499099470738013 44103520711312162301526755)
                  ·
                    refine ⟨66155281066968243452290133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44103520711312162301526755 66155281066968243452290133)
                    ·
                      refine ⟨775257200003534102956525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66155281066968243452290133 775257200003534102956525)
                      ·
                        rfl

theorem cell23_1509808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_1509808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509808 prefixEnd_1509808 := by exact prefixLift 1509808
  have htrace : WordTrace (prefixWord ++ tailWord_1509808) baseStart_1509808 baseEnd_1509808 := by
    simpa [prefixWord, tailWord_1509808, baseEnd_1509808] using wordTrace_append hprefix tailTrace_1509808
  have hstable : (prefixWord ++ tailWord_1509808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509808).length < 2 ^ (prefixWord ++ tailWord_1509808).sum := by decide
  have hdescent : baseEnd_1509808 < baseStart_1509808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509872 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_1509872 : Nat := 118140960795 + 1509872 * 2 ^ 59
def prefixEnd_1509872 : Nat := 4983230072969 + 3 ^ 40 * 1509872 * 2
def baseEnd_1509872 : Nat := 775290062765421852556231

theorem tailTrace_1509872 : CollatzResearch.WordTrace tailWord_1509872 prefixEnd_1509872 775290062765421852556231 := by
  unfold tailWord_1509872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27534777992999542226489935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36713037323999389635319913 27534777992999542226489935)
  ·
    refine ⟨41302166989499313339734903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27534777992999542226489935 41302166989499313339734903)
    ·
      refine ⟨61953250484248970009602355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41302166989499313339734903 61953250484248970009602355)
      ·
        refine ⟨92929875726373455014403533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61953250484248970009602355 92929875726373455014403533)
        ·
          refine ⟨34848703397390045630401325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92929875726373455014403533 34848703397390045630401325)
          ·
            refine ⟨13068263774021267111400497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34848703397390045630401325 13068263774021267111400497)
            ·
              refine ⟨9801197830515950333550373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13068263774021267111400497 9801197830515950333550373)
              ·
                refine ⟨1837724593221740687540695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9801197830515950333550373 1837724593221740687540695)
                ·
                  refine ⟨2756586889832611031311043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837724593221740687540695 2756586889832611031311043)
                  ·
                    refine ⟨4134880334748916546966565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756586889832611031311043 4134880334748916546966565)
                    ·
                      refine ⟨775290062765421852556231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4134880334748916546966565 775290062765421852556231)
                      ·
                        rfl

theorem cell23_1509872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_1509872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509872 prefixEnd_1509872 := by exact prefixLift 1509872
  have htrace : WordTrace (prefixWord ++ tailWord_1509872) baseStart_1509872 baseEnd_1509872 := by
    simpa [prefixWord, tailWord_1509872, baseEnd_1509872] using wordTrace_append hprefix tailTrace_1509872
  have hstable : (prefixWord ++ tailWord_1509872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509872).length < 2 ^ (prefixWord ++ tailWord_1509872).sum := by decide
  have hdescent : baseEnd_1509872 < baseStart_1509872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509889 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1509889 : Nat := 118140960795 + 1509889 * 2 ^ 59
def prefixEnd_1509889 : Nat := 4983230072969 + 3 ^ 40 * 1509889 * 2
def baseEnd_1509889 : Nat := 775298791936548286043653

theorem tailTrace_1509889 : CollatzResearch.WordTrace tailWord_1509889 prefixEnd_1509889 775298791936548286043653 := by
  unfold tailWord_1509889
  simp only [CollatzResearch.WordTrace]
  refine ⟨55070176026937496356348721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36713450684624997570899147 55070176026937496356348721)
  ·
    refine ⟨41302632020203122267261541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55070176026937496356348721 41302632020203122267261541)
    ·
      refine ⟨7744243503788085425111539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41302632020203122267261541 7744243503788085425111539)
      ·
        refine ⟨11616365255682128137667309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744243503788085425111539 11616365255682128137667309)
        ·
          refine ⟨4356136970880798051625241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11616365255682128137667309 4356136970880798051625241)
          ·
            refine ⟨3267102728160598538718931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4356136970880798051625241 3267102728160598538718931)
            ·
              refine ⟨4900654092240897808078397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267102728160598538718931 4900654092240897808078397)
              ·
                refine ⟨1837745284590336678029399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4900654092240897808078397 1837745284590336678029399)
                ·
                  refine ⟨2756617926885505017044099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837745284590336678029399 2756617926885505017044099)
                  ·
                    refine ⟨4134926890328257525566149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2756617926885505017044099 4134926890328257525566149)
                    ·
                      refine ⟨775298791936548286043653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4134926890328257525566149 775298791936548286043653)
                      ·
                        rfl

theorem cell23_1509889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1509889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509889 prefixEnd_1509889 := by exact prefixLift 1509889
  have htrace : WordTrace (prefixWord ++ tailWord_1509889) baseStart_1509889 baseEnd_1509889 := by
    simpa [prefixWord, tailWord_1509889, baseEnd_1509889] using wordTrace_append hprefix tailTrace_1509889
  have hstable : (prefixWord ++ tailWord_1509889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509889).length < 2 ^ (prefixWord ++ tailWord_1509889).sum := by decide
  have hdescent : baseEnd_1509889 < baseStart_1509889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509899 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 2, 4]
def baseStart_1509899 : Nat := 118140960795 + 1509899 * 2 ^ 59
def prefixEnd_1509899 : Nat := 4983230072969 + 3 ^ 40 * 1509899 * 2
def baseEnd_1509899 : Nat := 258434642247697748972869

theorem tailTrace_1509899 : CollatzResearch.WordTrace tailWord_1509899 prefixEnd_1509899 258434642247697748972869 := by
  unfold tailWord_1509899
  simp only [CollatzResearch.WordTrace]
  refine ⟨55070540756901268064212751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36713693837934178709475167 55070540756901268064212751)
  ·
    refine ⟨82605811135351902096319127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55070540756901268064212751 82605811135351902096319127)
    ·
      refine ⟨123908716703027853144478691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82605811135351902096319127 123908716703027853144478691)
      ·
        refine ⟨185863075054541779716718037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123908716703027853144478691 185863075054541779716718037)
        ·
          refine ⟨4356165821590822962110579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 185863075054541779716718037 4356165821590822962110579)
          ·
            refine ⟨6534248732386234443165869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356165821590822962110579 6534248732386234443165869)
            ·
              refine ⟨2450343274644837916187201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6534248732386234443165869 2450343274644837916187201)
              ·
                refine ⟨1837757455983628437140401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2450343274644837916187201 1837757455983628437140401)
                ·
                  refine ⟨1378318091987721327855301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837757455983628437140401 1378318091987721327855301)
                  ·
                    refine ⟨258434642247697748972869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378318091987721327855301 258434642247697748972869)
                    ·
                      rfl

theorem cell23_1509899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 4].length) (baseStart_1509899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509899 prefixEnd_1509899 := by exact prefixLift 1509899
  have htrace : WordTrace (prefixWord ++ tailWord_1509899) baseStart_1509899 baseEnd_1509899 := by
    simpa [prefixWord, tailWord_1509899, baseEnd_1509899] using wordTrace_append hprefix tailTrace_1509899
  have hstable : (prefixWord ++ tailWord_1509899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509899).length < 2 ^ (prefixWord ++ tailWord_1509899).sum := by decide
  have hdescent : baseEnd_1509899 < baseStart_1509899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509916 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1509916 : Nat := 118140960795 + 1509916 * 2 ^ 59
def prefixEnd_1509916 : Nat := 4983230072969 + 3 ^ 40 * 1509916 * 2
def baseEnd_1509916 : Nat := 258437551971406560135343

theorem tailTrace_1509916 : CollatzResearch.WordTrace tailWord_1509916 prefixEnd_1509916 258437551971406560135343 := by
  unfold tailWord_1509916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27535580398919839983790801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36714107198559786645054401 27535580398919839983790801)
  ·
    refine ⟨20651685299189879987843101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27535580398919839983790801 20651685299189879987843101)
    ·
      refine ⟨7744381987196204995441163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20651685299189879987843101 7744381987196204995441163)
      ·
        refine ⟨11616572980794307493161745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744381987196204995441163 11616572980794307493161745)
        ·
          refine ⟨8712429735595730619871309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11616572980794307493161745 8712429735595730619871309)
          ·
            refine ⟨3267161150848398982451741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8712429735595730619871309 3267161150848398982451741)
            ·
              refine ⟨1225185431568149618419403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3267161150848398982451741 1225185431568149618419403)
              ·
                refine ⟨1837778147352224427629105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225185431568149618419403 1837778147352224427629105)
                ·
                  refine ⟨1378333610514168320721829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837778147352224427629105 1378333610514168320721829)
                  ·
                    refine ⟨258437551971406560135343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378333610514168320721829 258437551971406560135343)
                    ·
                      rfl

theorem cell23_1509916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1509916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509916 prefixEnd_1509916 := by exact prefixLift 1509916
  have htrace : WordTrace (prefixWord ++ tailWord_1509916) baseStart_1509916 baseEnd_1509916 := by
    simpa [prefixWord, tailWord_1509916, baseEnd_1509916] using wordTrace_append hprefix tailTrace_1509916
  have hstable : (prefixWord ++ tailWord_1509916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509916).length < 2 ^ (prefixWord ++ tailWord_1509916).sum := by decide
  have hdescent : baseEnd_1509916 < baseStart_1509916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509925 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1509925 : Nat := 118140960795 + 1509925 * 2 ^ 59
def prefixEnd_1509925 : Nat := 4983230072969 + 3 ^ 40 * 1509925 * 2
def baseEnd_1509925 : Nat := 258439092413370048397829

theorem tailTrace_1509925 : CollatzResearch.WordTrace tailWord_1509925 prefixEnd_1509925 258439092413370048397829 := by
  unfold tailWord_1509925
  simp only [CollatzResearch.WordTrace]
  refine ⟨55071489054807074504659229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36714326036538049669772819 55071489054807074504659229)
  ·
    refine ⟨20651808395552652939247211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55071489054807074504659229 20651808395552652939247211)
    ·
      refine ⟨30977712593328979408870817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20651808395552652939247211 30977712593328979408870817)
      ·
        refine ⟨23233284444996734556653113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30977712593328979408870817 23233284444996734556653113)
        ·
          refine ⟨17424963333747550917489835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23233284444996734556653113 17424963333747550917489835)
          ·
            refine ⟨26137445000621326376234753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17424963333747550917489835 26137445000621326376234753)
            ·
              refine ⟨19603083750465994782176065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26137445000621326376234753 19603083750465994782176065)
              ·
                refine ⟨14702312812849496086632049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19603083750465994782176065 14702312812849496086632049)
                ·
                  refine ⟨11026734609637122064974037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14702312812849496086632049 11026734609637122064974037)
                  ·
                    refine ⟨258439092413370048397829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11026734609637122064974037 258439092413370048397829)
                    ·
                      rfl

theorem cell23_1509925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1509925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509925 prefixEnd_1509925 := by exact prefixLift 1509925
  have htrace : WordTrace (prefixWord ++ tailWord_1509925) baseStart_1509925 baseEnd_1509925 := by
    simpa [prefixWord, tailWord_1509925, baseEnd_1509925] using wordTrace_append hprefix tailTrace_1509925
  have hstable : (prefixWord ++ tailWord_1509925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509925).length < 2 ^ (prefixWord ++ tailWord_1509925).sum := by decide
  have hdescent : baseEnd_1509925 < baseStart_1509925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509932 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_1509932 : Nat := 118140960795 + 1509932 * 2 ^ 59
def prefixEnd_1509932 : Nat := 4983230072969 + 3 ^ 40 * 1509932 * 2
def baseEnd_1509932 : Nat := 775320871604691617805955

theorem tailTrace_1509932 : CollatzResearch.WordTrace tailWord_1509932 prefixEnd_1509932 775320871604691617805955 := by
  unfold tailWord_1509932
  simp only [CollatzResearch.WordTrace]
  refine ⟨27535872182890857350082025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36714496243854476466776033 27535872182890857350082025)
  ·
    refine ⟨20651904137168143012561519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27535872182890857350082025 20651904137168143012561519)
    ·
      refine ⟨30977856205752214518842279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20651904137168143012561519 30977856205752214518842279)
      ·
        refine ⟨46466784308628321778263419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30977856205752214518842279 46466784308628321778263419)
        ·
          refine ⟨69700176462942482667395129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46466784308628321778263419 69700176462942482667395129)
          ·
            refine ⟨52275132347206862000546347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69700176462942482667395129 52275132347206862000546347)
            ·
              refine ⟨78412698520810293000819521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52275132347206862000546347 78412698520810293000819521)
              ·
                refine ⟨58809523890607719750614641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78412698520810293000819521 58809523890607719750614641)
                ·
                  refine ⟨44107142917955789812960981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58809523890607719750614641 44107142917955789812960981)
                  ·
                    refine ⟨1033761162139588823741273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44107142917955789812960981 1033761162139588823741273)
                    ·
                      refine ⟨775320871604691617805955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033761162139588823741273 775320871604691617805955)
                      ·
                        rfl

theorem cell23_1509932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_1509932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509932 prefixEnd_1509932 := by exact prefixLift 1509932
  have htrace : WordTrace (prefixWord ++ tailWord_1509932) baseStart_1509932 baseEnd_1509932 := by
    simpa [prefixWord, tailWord_1509932, baseEnd_1509932] using wordTrace_append hprefix tailTrace_1509932
  have hstable : (prefixWord ++ tailWord_1509932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509932).length < 2 ^ (prefixWord ++ tailWord_1509932).sum := by decide
  have hdescent : baseEnd_1509932 < baseStart_1509932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509955 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 4, 6]
def baseStart_1509955 : Nat := 118140960795 + 1509955 * 2 ^ 59
def prefixEnd_1509955 : Nat := 4983230072969 + 3 ^ 40 * 1509955 * 2
def baseEnd_1509955 : Nat := 258444227219915009272783

theorem tailTrace_1509955 : CollatzResearch.WordTrace tailWord_1509955 prefixEnd_1509955 258444227219915009272783 := by
  unfold tailWord_1509955
  simp only [CollatzResearch.WordTrace]
  refine ⟨55072583244698389628251319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36715055496465593085500879 55072583244698389628251319)
  ·
    refine ⟨82608874867047584442376979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55072583244698389628251319 82608874867047584442376979)
    ·
      refine ⟨123913312300571376663565469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82608874867047584442376979 123913312300571376663565469)
      ·
        refine ⟨46467492112714266248837051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123913312300571376663565469 46467492112714266248837051)
        ·
          refine ⟨69701238169071399373255577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46467492112714266248837051 69701238169071399373255577)
          ·
            refine ⟨52275928626803549529941683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69701238169071399373255577 52275928626803549529941683)
            ·
              refine ⟨78413892940205324294912525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52275928626803549529941683 78413892940205324294912525)
              ·
                refine ⟨29405209852576996610592197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78413892940205324294912525 29405209852576996610592197)
                ·
                  refine ⟨5513476847358186864486037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29405209852576996610592197 5513476847358186864486037)
                  ·
                    refine ⟨258444227219915009272783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5513476847358186864486037 258444227219915009272783)
                    ·
                      rfl

theorem cell23_1509955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_1509955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509955 prefixEnd_1509955 := by exact prefixLift 1509955
  have htrace : WordTrace (prefixWord ++ tailWord_1509955) baseStart_1509955 baseEnd_1509955 := by
    simpa [prefixWord, tailWord_1509955, baseEnd_1509955] using wordTrace_append hprefix tailTrace_1509955
  have hstable : (prefixWord ++ tailWord_1509955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509955).length < 2 ^ (prefixWord ++ tailWord_1509955).sum := by decide
  have hdescent : baseEnd_1509955 < baseStart_1509955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509995 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_1509995 : Nat := 118140960795 + 1509995 * 2 ^ 59
def prefixEnd_1509995 : Nat := 4983230072969 + 3 ^ 40 * 1509995 * 2
def baseEnd_1509995 : Nat := 775353220885924871318165

theorem tailTrace_1509995 : CollatzResearch.WordTrace tailWord_1509995 prefixEnd_1509995 775353220885924871318165 := by
  unfold tailWord_1509995
  simp only [CollatzResearch.WordTrace]
  refine ⟨55074042164553476459707439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36716028109702317639804959 55074042164553476459707439)
  ·
    refine ⟨82611063246830214689561159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55074042164553476459707439 82611063246830214689561159)
    ·
      refine ⟨123916594870245322034341739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82611063246830214689561159 123916594870245322034341739)
      ·
        refine ⟨185874892305367983051512609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123916594870245322034341739 185874892305367983051512609)
        ·
          refine ⟨139406169229025987288634457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185874892305367983051512609 139406169229025987288634457)
          ·
            refine ⟨104554626921769490466475843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139406169229025987288634457 104554626921769490466475843)
            ·
              refine ⟨156831940382654235699713765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104554626921769490466475843 156831940382654235699713765)
              ·
                refine ⟨29405988821747669193696331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156831940382654235699713765 29405988821747669193696331)
                ·
                  refine ⟨44108983232621503790544497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29405988821747669193696331 44108983232621503790544497)
                  ·
                    refine ⟨33081737424466127842908373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44108983232621503790544497 33081737424466127842908373)
                    ·
                      refine ⟨775353220885924871318165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33081737424466127842908373 775353220885924871318165)
                      ·
                        rfl

theorem cell23_1509995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_1509995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1509995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1509995 prefixEnd_1509995 := by exact prefixLift 1509995
  have htrace : WordTrace (prefixWord ++ tailWord_1509995) baseStart_1509995 baseEnd_1509995 := by
    simpa [prefixWord, tailWord_1509995, baseEnd_1509995] using wordTrace_append hprefix tailTrace_1509995
  have hstable : (prefixWord ++ tailWord_1509995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509995).length < 2 ^ (prefixWord ++ tailWord_1509995).sum := by decide
  have hdescent : baseEnd_1509995 < baseStart_1509995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510039 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_1510039 : Nat := 118140960795 + 1510039 * 2 ^ 59
def prefixEnd_1510039 : Nat := 4983230072969 + 3 ^ 40 * 1510039 * 2
def baseEnd_1510039 : Nat := 775375814034722699167963

theorem tailTrace_1510039 : CollatzResearch.WordTrace tailWord_1510039 prefixEnd_1510039 775375814034722699167963 := by
  unfold tailWord_1510039
  simp only [CollatzResearch.WordTrace]
  refine ⟨55075646976394071974309171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36717097984262714649539447 55075646976394071974309171)
  ·
    refine ⟨82613470464591107961463757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55075646976394071974309171 82613470464591107961463757)
    ·
      refine ⟨30980051424221665485548909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82613470464591107961463757 30980051424221665485548909)
      ·
        refine ⟨11617519284083124557080841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30980051424221665485548909 11617519284083124557080841)
        ·
          refine ⟨8713139463062343417810631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11617519284083124557080841 8713139463062343417810631)
          ·
            refine ⟨13069709194593515126715947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713139463062343417810631 13069709194593515126715947)
            ·
              refine ⟨19604563791890272690073921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069709194593515126715947 19604563791890272690073921)
              ·
                refine ⟨14703422843917704517555441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19604563791890272690073921 14703422843917704517555441)
                ·
                  refine ⟨11027567132938278388166581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14703422843917704517555441 11027567132938278388166581)
                  ·
                    refine ⟨1033834418712963598890617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11027567132938278388166581 1033834418712963598890617)
                    ·
                      refine ⟨775375814034722699167963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033834418712963598890617 775375814034722699167963)
                      ·
                        rfl

theorem cell23_1510039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_1510039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510039 prefixEnd_1510039 := by exact prefixLift 1510039
  have htrace : WordTrace (prefixWord ++ tailWord_1510039) baseStart_1510039 baseEnd_1510039 := by
    simpa [prefixWord, tailWord_1510039, baseEnd_1510039] using wordTrace_append hprefix tailTrace_1510039
  have hstable : (prefixWord ++ tailWord_1510039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510039).length < 2 ^ (prefixWord ++ tailWord_1510039).sum := by decide
  have hdescent : baseEnd_1510039 < baseStart_1510039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510049 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_1510049 : Nat := 118140960795 + 1510049 * 2 ^ 59
def prefixEnd_1510049 : Nat := 4983230072969 + 3 ^ 40 * 1510049 * 2
def baseEnd_1510049 : Nat := 258460316280422553347639

theorem tailTrace_1510049 : CollatzResearch.WordTrace tailWord_1510049 prefixEnd_1510049 258460316280422553347639 := by
  unfold tailWord_1510049
  simp only [CollatzResearch.WordTrace]
  refine ⟨55076011706357843682173201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36717341137571895788115467 55076011706357843682173201)
  ·
    refine ⟨41307008779768382761629901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55076011706357843682173201 41307008779768382761629901)
    ·
      refine ⟨15490128292413143535611213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41307008779768382761629901 15490128292413143535611213)
      ·
        refine ⟨5808798109654928825854205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15490128292413143535611213 5808798109654928825854205)
        ·
          refine ⟨2178299291120598309695327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5808798109654928825854205 2178299291120598309695327)
          ·
            refine ⟨3267448936680897464542991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178299291120598309695327 3267448936680897464542991)
            ·
              refine ⟨4901173405021346196814487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267448936680897464542991 4901173405021346196814487)
              ·
                refine ⟨7351760107532019295221731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901173405021346196814487 7351760107532019295221731)
                ·
                  refine ⟨11027640161298028942832597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7351760107532019295221731 11027640161298028942832597)
                  ·
                    refine ⟨258460316280422553347639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11027640161298028942832597 258460316280422553347639)
                    ·
                      rfl

theorem cell23_1510049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_1510049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510049 prefixEnd_1510049 := by exact prefixLift 1510049
  have htrace : WordTrace (prefixWord ++ tailWord_1510049) baseStart_1510049 baseEnd_1510049 := by
    simpa [prefixWord, tailWord_1510049, baseEnd_1510049] using wordTrace_append hprefix tailTrace_1510049
  have hstable : (prefixWord ++ tailWord_1510049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510049).length < 2 ^ (prefixWord ++ tailWord_1510049).sum := by decide
  have hdescent : baseEnd_1510049 < baseStart_1510049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510079 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 3, 4]
def baseStart_1510079 : Nat := 118140960795 + 1510079 * 2 ^ 59
def prefixEnd_1510079 : Nat := 4983230072969 + 3 ^ 40 * 1510079 * 2
def baseEnd_1510079 : Nat := 258465451086967514222593

theorem tailTrace_1510079 : CollatzResearch.WordTrace tailWord_1510079 prefixEnd_1510079 258465451086967514222593 := by
  unfold tailWord_1510079
  simp only [CollatzResearch.WordTrace]
  refine ⟨55077105896249158805765291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36718070597499439203843527 55077105896249158805765291)
  ·
    refine ⟨82615658844373738208647937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55077105896249158805765291 82615658844373738208647937)
    ·
      refine ⟨61961744133280303656485953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82615658844373738208647937 61961744133280303656485953)
      ·
        refine ⟨46471308099960227742364465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61961744133280303656485953 46471308099960227742364465)
        ·
          refine ⟨34853481074970170806773349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46471308099960227742364465 34853481074970170806773349)
          ·
            refine ⟨6535027701556907026270003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34853481074970170806773349 6535027701556907026270003)
            ·
              refine ⟨9802541552335360539405005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535027701556907026270003 9802541552335360539405005)
              ·
                refine ⟨3675953082125760202276877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9802541552335360539405005 3675953082125760202276877)
                ·
                  refine ⟨1378482405797160075853829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3675953082125760202276877 1378482405797160075853829)
                  ·
                    refine ⟨258465451086967514222593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378482405797160075853829 258465451086967514222593)
                    ·
                      rfl

theorem cell23_1510079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_1510079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510079 prefixEnd_1510079 := by exact prefixLift 1510079
  have htrace : WordTrace (prefixWord ++ tailWord_1510079) baseStart_1510079 baseEnd_1510079 := by
    simpa [prefixWord, tailWord_1510079, baseEnd_1510079] using wordTrace_append hprefix tailTrace_1510079
  have hstable : (prefixWord ++ tailWord_1510079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510079).length < 2 ^ (prefixWord ++ tailWord_1510079).sum := by decide
  have hdescent : baseEnd_1510079 < baseStart_1510079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510113 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1510113 : Nat := 118140960795 + 1510113 * 2 ^ 59
def prefixEnd_1510113 : Nat := 4983230072969 + 3 ^ 40 * 1510113 * 2
def baseEnd_1510113 : Nat := 258471270534385136547541

theorem tailTrace_1510113 : CollatzResearch.WordTrace tailWord_1510113 prefixEnd_1510113 258471270534385136547541 := by
  unfold tailWord_1510113
  simp only [CollatzResearch.WordTrace]
  refine ⟨55078345978125982612502993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36718897318750655075001995 55078345978125982612502993)
  ·
    refine ⟨41308759483594486959377245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55078345978125982612502993 41308759483594486959377245)
    ·
      refine ⟨15490784806347932609766467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41308759483594486959377245 15490784806347932609766467)
      ·
        refine ⟨23236177209521898914649701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490784806347932609766467 23236177209521898914649701)
        ·
          refine ⟨4356783226785356046496819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23236177209521898914649701 4356783226785356046496819)
          ·
            refine ⟨6535174840178034069745229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356783226785356046496819 6535174840178034069745229)
            ·
              refine ⟨2450690565066762776154461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6535174840178034069745229 2450690565066762776154461)
              ·
                refine ⟨919008961900036041057923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2450690565066762776154461 919008961900036041057923)
                ·
                  refine ⟨1378513442850054061586885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919008961900036041057923 1378513442850054061586885)
                  ·
                    refine ⟨258471270534385136547541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378513442850054061586885 258471270534385136547541)
                    ·
                      rfl

theorem cell23_1510113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1510113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510113 prefixEnd_1510113 := by exact prefixLift 1510113
  have htrace : WordTrace (prefixWord ++ tailWord_1510113) baseStart_1510113 baseEnd_1510113 := by
    simpa [prefixWord, tailWord_1510113, baseEnd_1510113] using wordTrace_append hprefix tailTrace_1510113
  have hstable : (prefixWord ++ tailWord_1510113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510113).length < 2 ^ (prefixWord ++ tailWord_1510113).sum := by decide
  have hdescent : baseEnd_1510113 < baseStart_1510113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510130 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_1510130 : Nat := 118140960795 + 1510130 * 2 ^ 59
def prefixEnd_1510130 : Nat := 4983230072969 + 3 ^ 40 * 1510130 * 2
def baseEnd_1510130 : Nat := 258474180258093947710015

theorem tailTrace_1510130 : CollatzResearch.WordTrace tailWord_1510130 prefixEnd_1510130 258474180258093947710015 := by
  unfold tailWord_1510130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769741504766098628967961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36719310679376263010581229 13769741504766098628967961)
  ·
    refine ⟨10327306128574573971725971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13769741504766098628967961 10327306128574573971725971)
    ·
      refine ⟨15490959192861860957588957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10327306128574573971725971 15490959192861860957588957)
      ·
        refine ⟨5809109697323197859095859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15490959192861860957588957 5809109697323197859095859)
        ·
          refine ⟨8713664545984796788643789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809109697323197859095859 8713664545984796788643789)
          ·
            refine ⟨3267624204744298795741421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8713664545984796788643789 3267624204744298795741421)
            ·
              refine ⟨1225359076779112048403033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3267624204744298795741421 1225359076779112048403033)
              ·
                refine ⟨919019307584334036302275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225359076779112048403033 919019307584334036302275)
                ·
                  refine ⟨1378528961376501054453413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919019307584334036302275 1378528961376501054453413)
                  ·
                    refine ⟨258474180258093947710015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378528961376501054453413 258474180258093947710015)
                    ·
                      rfl

theorem cell23_1510130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_1510130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510130 prefixEnd_1510130 := by exact prefixLift 1510130
  have htrace : WordTrace (prefixWord ++ tailWord_1510130) baseStart_1510130 baseEnd_1510130 := by
    simpa [prefixWord, tailWord_1510130, baseEnd_1510130] using wordTrace_append hprefix tailTrace_1510130
  have hstable : (prefixWord ++ tailWord_1510130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510130).length < 2 ^ (prefixWord ++ tailWord_1510130).sum := by decide
  have hdescent : baseEnd_1510130 < baseStart_1510130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510159 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_1510159 : Nat := 118140960795 + 1510159 * 2 ^ 59
def prefixEnd_1510159 : Nat := 4983230072969 + 3 ^ 40 * 1510159 * 2
def baseEnd_1510159 : Nat := 775437431713262229667411

theorem tailTrace_1510159 : CollatzResearch.WordTrace tailWord_1510159 prefixEnd_1510159 775437431713262229667411 := by
  unfold tailWord_1510159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55080023735959332468677531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36720015823972888312451687 55080023735959332468677531)
  ·
    refine ⟨82620035603938998703016297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55080023735959332468677531 82620035603938998703016297)
    ·
      refine ⟨61965026702954249027262223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82620035603938998703016297 61965026702954249027262223)
      ·
        refine ⟨92947540054431373540893335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61965026702954249027262223 92947540054431373540893335)
        ·
          refine ⟨139421310081647060311340003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92947540054431373540893335 139421310081647060311340003)
          ·
            refine ⟨209131965122470590467010005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139421310081647060311340003 209131965122470590467010005)
            ·
              refine ⟨4901530432557904464070547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 209131965122470590467010005 4901530432557904464070547)
              ·
                refine ⟨7352295648836856696105821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901530432557904464070547 7352295648836856696105821)
                ·
                  refine ⟨2757110868313821261039683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7352295648836856696105821 2757110868313821261039683)
                  ·
                    refine ⟨4135666302470731891559525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2757110868313821261039683 4135666302470731891559525)
                    ·
                      refine ⟨775437431713262229667411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4135666302470731891559525 775437431713262229667411)
                      ·
                        rfl

theorem cell23_1510159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_1510159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510159 prefixEnd_1510159 := by exact prefixLift 1510159
  have htrace : WordTrace (prefixWord ++ tailWord_1510159) baseStart_1510159 baseEnd_1510159 := by
    simpa [prefixWord, tailWord_1510159, baseEnd_1510159] using wordTrace_append hprefix tailTrace_1510159
  have hstable : (prefixWord ++ tailWord_1510159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510159).length < 2 ^ (prefixWord ++ tailWord_1510159).sum := by decide
  have hdescent : baseEnd_1510159 < baseStart_1510159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510169 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_1510169 : Nat := 118140960795 + 1510169 * 2 ^ 59
def prefixEnd_1510169 : Nat := 4983230072969 + 3 ^ 40 * 1510169 * 2
def baseEnd_1510169 : Nat := 258480855506602396847455

theorem tailTrace_1510169 : CollatzResearch.WordTrace tailWord_1510169 prefixEnd_1510169 258480855506602396847455 := by
  unfold tailWord_1510169
  simp only [CollatzResearch.WordTrace]
  refine ⟨55080388465923104176541561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36720258977282069451027707 55080388465923104176541561)
  ·
    refine ⟨41310291349442328132406171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55080388465923104176541561 41310291349442328132406171)
    ·
      refine ⟨61965437024163492198609257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41310291349442328132406171 61965437024163492198609257)
      ·
        refine ⟨46474077768122619148956943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61965437024163492198609257 46474077768122619148956943)
        ·
          refine ⟨69711116652183928723435415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46474077768122619148956943 69711116652183928723435415)
          ·
            refine ⟨104566674978275893085153123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69711116652183928723435415 104566674978275893085153123)
            ·
              refine ⟨156850012467413839627729685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104566674978275893085153123 156850012467413839627729685)
              ·
                refine ⟨7352344334410023732549829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156850012467413839627729685 7352344334410023732549829)
                ·
                  refine ⟨1378564562701879449853093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7352344334410023732549829 1378564562701879449853093)
                  ·
                    refine ⟨258480855506602396847455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378564562701879449853093 258480855506602396847455)
                    ·
                      rfl

theorem cell23_1510169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_1510169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510169 prefixEnd_1510169 := by exact prefixLift 1510169
  have htrace : WordTrace (prefixWord ++ tailWord_1510169) baseStart_1510169 baseEnd_1510169 := by
    simpa [prefixWord, tailWord_1510169, baseEnd_1510169] using wordTrace_append hprefix tailTrace_1510169
  have hstable : (prefixWord ++ tailWord_1510169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510169).length < 2 ^ (prefixWord ++ tailWord_1510169).sum := by decide
  have hdescent : baseEnd_1510169 < baseStart_1510169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510193 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 3, 2, 2]
def baseStart_1510193 : Nat := 118140960795 + 1510193 * 2 ^ 59
def prefixEnd_1510193 : Nat := 4983230072969 + 3 ^ 40 * 1510193 * 2
def baseEnd_1510193 : Nat := 775454890055515096642255

theorem tailTrace_1510193 : CollatzResearch.WordTrace tailWord_1510193 prefixEnd_1510193 775454890055515096642255 := by
  unfold tailWord_1510193
  simp only [CollatzResearch.WordTrace]
  refine ⟨55081263817836156275415233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36720842545224104183610155 55081263817836156275415233)
  ·
    refine ⟨41310947863377117206561425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55081263817836156275415233 41310947863377117206561425)
    ·
      refine ⟨30983210897532837904921069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41310947863377117206561425 30983210897532837904921069)
      ·
        refine ⟨11618704086574814214345401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30983210897532837904921069 11618704086574814214345401)
        ·
          refine ⟨8714028064931110660759051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11618704086574814214345401 8714028064931110660759051)
          ·
            refine ⟨13071042097396665991138577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8714028064931110660759051 13071042097396665991138577)
            ·
              refine ⟨9803281573047499493353933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13071042097396665991138577 9803281573047499493353933)
              ·
                refine ⟨3676230589892812310007725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9803281573047499493353933 3676230589892812310007725)
                ·
                  refine ⟨1378586471209804616252897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3676230589892812310007725 1378586471209804616252897)
                  ·
                    refine ⟨1033939853407353462189673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1378586471209804616252897 1033939853407353462189673)
                    ·
                      refine ⟨775454890055515096642255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033939853407353462189673 775454890055515096642255)
                      ·
                        rfl

theorem cell23_1510193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_1510193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510193 prefixEnd_1510193 := by exact prefixLift 1510193
  have htrace : WordTrace (prefixWord ++ tailWord_1510193) baseStart_1510193 baseEnd_1510193 := by
    simpa [prefixWord, tailWord_1510193, baseEnd_1510193] using wordTrace_append hprefix tailTrace_1510193
  have hstable : (prefixWord ++ tailWord_1510193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510193).length < 2 ^ (prefixWord ++ tailWord_1510193).sum := by decide
  have hdescent : baseEnd_1510193 < baseStart_1510193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510214 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1510214 : Nat := 118140960795 + 1510214 * 2 ^ 59
def prefixEnd_1510214 : Nat := 4983230072969 + 3 ^ 40 * 1510214 * 2
def baseEnd_1510214 : Nat := 775465673149259514479659

theorem tailTrace_1510214 : CollatzResearch.WordTrace tailWord_1510214 prefixEnd_1510214 775465673149259514479659 := by
  unfold tailWord_1510214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721313429711252401935303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36721353167173384574619797 1721313429711252401935303)
  ·
    refine ⟨2581970144566878602902955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721313429711252401935303 2581970144566878602902955)
    ·
      refine ⟨3872955216850317904354433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581970144566878602902955 3872955216850317904354433)
      ·
        refine ⟨2904716412637738428265825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3872955216850317904354433 2904716412637738428265825)
        ·
          refine ⟨2178537309478303821199369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2904716412637738428265825 2178537309478303821199369)
          ·
            refine ⟨1633902982108727865899527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2178537309478303821199369 1633902982108727865899527)
            ·
              refine ⟨2450854473163091798849291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633902982108727865899527 2450854473163091798849291)
              ·
                refine ⟨3676281709744637698273937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450854473163091798849291 3676281709744637698273937)
                ·
                  refine ⟨2757211282308478273705453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676281709744637698273937 2757211282308478273705453)
                  ·
                    refine ⟨1033954230865679352639545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757211282308478273705453 1033954230865679352639545)
                    ·
                      refine ⟨775465673149259514479659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1033954230865679352639545 775465673149259514479659)
                      ·
                        rfl

theorem cell23_1510214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1510214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510214 prefixEnd_1510214 := by exact prefixLift 1510214
  have htrace : WordTrace (prefixWord ++ tailWord_1510214) baseStart_1510214 baseEnd_1510214 := by
    simpa [prefixWord, tailWord_1510214, baseEnd_1510214] using wordTrace_append hprefix tailTrace_1510214
  have hstable : (prefixWord ++ tailWord_1510214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510214).length < 2 ^ (prefixWord ++ tailWord_1510214).sum := by decide
  have hdescent : baseEnd_1510214 < baseStart_1510214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510226 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1510226 : Nat := 118140960795 + 1510226 * 2 ^ 59
def prefixEnd_1510226 : Nat := 4983230072969 + 3 ^ 40 * 1510226 * 2
def baseEnd_1510226 : Nat := 775471834917113467529603

theorem tailTrace_1510226 : CollatzResearch.WordTrace tailWord_1510226 prefixEnd_1510226 775471834917113467529603 := by
  unfold tailWord_1510226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13770616856679150727841633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36721644951144401940911021 13770616856679150727841633)
  ·
    refine ⟨10327962642509363045881225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13770616856679150727841633 10327962642509363045881225)
    ·
      refine ⟨7745971981882022284410919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10327962642509363045881225 7745971981882022284410919)
      ·
        refine ⟨11618957972823033426616379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745971981882022284410919 11618957972823033426616379)
        ·
          refine ⟨17428436959234550139924569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11618957972823033426616379 17428436959234550139924569)
          ·
            refine ⟨13071327719425912604943427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17428436959234550139924569 13071327719425912604943427)
            ·
              refine ⟨19606991579138868907415141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071327719425912604943427 19606991579138868907415141)
              ·
                refine ⟨3676310921088537920140339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19606991579138868907415141 3676310921088537920140339)
                ·
                  refine ⟨5514466381632806880210509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676310921088537920140339 5514466381632806880210509)
                  ·
                    refine ⟨2067924893112302580078941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5514466381632806880210509 2067924893112302580078941)
                    ·
                      refine ⟨775471834917113467529603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2067924893112302580078941 775471834917113467529603)
                      ·
                        rfl

theorem cell23_1510226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1510226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510226 prefixEnd_1510226 := by exact prefixLift 1510226
  have htrace : WordTrace (prefixWord ++ tailWord_1510226) baseStart_1510226 baseEnd_1510226 := by
    simpa [prefixWord, tailWord_1510226, baseEnd_1510226] using wordTrace_append hprefix tailTrace_1510226
  have hstable : (prefixWord ++ tailWord_1510226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510226).length < 2 ^ (prefixWord ++ tailWord_1510226).sum := by decide
  have hdescent : baseEnd_1510226 < baseStart_1510226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510243 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1510243 : Nat := 118140960795 + 1510243 * 2 ^ 59
def prefixEnd_1510243 : Nat := 4983230072969 + 3 ^ 40 * 1510243 * 2
def baseEnd_1510243 : Nat := 775480564088239901017025

theorem tailTrace_1510243 : CollatzResearch.WordTrace tailWord_1510243 prefixEnd_1510243 775480564088239901017025 := by
  unfold tailWord_1510243
  simp only [CollatzResearch.WordTrace]
  refine ⟨55083087467655014814735383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36722058311770009876490255 55083087467655014814735383)
  ·
    refine ⟨82624631201482522222103075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55083087467655014814735383 82624631201482522222103075)
    ·
      refine ⟨123936946802223783333154613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82624631201482522222103075 123936946802223783333154613)
      ·
        refine ⟨11619088762708479687483245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123936946802223783333154613 11619088762708479687483245)
        ·
          refine ⟨4357158286015679882806217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11619088762708479687483245 4357158286015679882806217)
          ·
            refine ⟨3267868714511759912104663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4357158286015679882806217 3267868714511759912104663)
            ·
              refine ⟨4901803071767639868156995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3267868714511759912104663 4901803071767639868156995)
              ·
                refine ⟨7352704607651459802235493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901803071767639868156995 7352704607651459802235493)
                ·
                  refine ⟨1378632113934648712919155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7352704607651459802235493 1378632113934648712919155)
                  ·
                    refine ⟨2067948170901973069378733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1378632113934648712919155 2067948170901973069378733)
                    ·
                      refine ⟨775480564088239901017025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2067948170901973069378733 775480564088239901017025)
                      ·
                        rfl

theorem cell23_1510243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1510243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510243 prefixEnd_1510243 := by exact prefixLift 1510243
  have htrace : WordTrace (prefixWord ++ tailWord_1510243) baseStart_1510243 baseEnd_1510243 := by
    simpa [prefixWord, tailWord_1510243, baseEnd_1510243] using wordTrace_append hprefix tailTrace_1510243
  have hstable : (prefixWord ++ tailWord_1510243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510243).length < 2 ^ (prefixWord ++ tailWord_1510243).sum := by decide
  have hdescent : baseEnd_1510243 < baseStart_1510243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510259 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 2, 6]
def baseStart_1510259 : Nat := 118140960795 + 1510259 * 2 ^ 59
def prefixEnd_1510259 : Nat := 4983230072969 + 3 ^ 40 * 1510259 * 2
def baseEnd_1510259 : Nat := 258496259926237279472317

theorem tailTrace_1510259 : CollatzResearch.WordTrace tailWord_1510259 prefixEnd_1510259 258496259926237279472317 := by
  unfold tailWord_1510259
  simp only [CollatzResearch.WordTrace]
  refine ⟨55083671035597049547317831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36722447357064699698211887 55083671035597049547317831)
  ·
    refine ⟨82625506553395574320976747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55083671035597049547317831 82625506553395574320976747)
    ·
      refine ⟨123938259830093361481465121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82625506553395574320976747 123938259830093361481465121)
      ·
        refine ⟨92953694872570021111098841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123938259830093361481465121 92953694872570021111098841)
        ·
          refine ⟨69715271154427515833324131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92953694872570021111098841 69715271154427515833324131)
          ·
            refine ⟨104572906731641273749986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69715271154427515833324131 104572906731641273749986197)
            ·
              refine ⟨4901855003045684707030603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104572906731641273749986197 4901855003045684707030603)
              ·
                refine ⟨7352782504568527060545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901855003045684707030603 7352782504568527060545905)
                ·
                  refine ⟨5514586878426395295409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7352782504568527060545905 5514586878426395295409429)
                  ·
                    refine ⟨258496259926237279472317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5514586878426395295409429 258496259926237279472317)
                    ·
                      rfl

theorem cell23_1510259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_1510259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510259 prefixEnd_1510259 := by exact prefixLift 1510259
  have htrace : WordTrace (prefixWord ++ tailWord_1510259) baseStart_1510259 baseEnd_1510259 := by
    simpa [prefixWord, tailWord_1510259, baseEnd_1510259] using wordTrace_append hprefix tailTrace_1510259
  have hstable : (prefixWord ++ tailWord_1510259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510259).length < 2 ^ (prefixWord ++ tailWord_1510259).sum := by decide
  have hdescent : baseEnd_1510259 < baseStart_1510259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510283 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 4, 2, 2]
def baseStart_1510283 : Nat := 118140960795 + 1510283 * 2 ^ 59
def prefixEnd_1510283 : Nat := 4983230072969 + 3 ^ 40 * 1510283 * 2
def baseEnd_1510283 : Nat := 775501103314419744516841

theorem tailTrace_1510283 : CollatzResearch.WordTrace tailWord_1510283 prefixEnd_1510283 775501103314419744516841 := by
  unfold tailWord_1510283
  simp only [CollatzResearch.WordTrace]
  refine ⟨55084546387510101646191503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36723030925006734430794335 55084546387510101646191503)
  ·
    refine ⟨82626819581265152469287255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55084546387510101646191503 82626819581265152469287255)
    ·
      refine ⟨123940229371897728703930883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82626819581265152469287255 123940229371897728703930883)
      ·
        refine ⟨185910344057846593055896325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123940229371897728703930883 185910344057846593055896325)
        ·
          refine ⟨34858189510846236197980561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185910344057846593055896325 34858189510846236197980561)
          ·
            refine ⟨26143642133134677148485421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34858189510846236197980561 26143642133134677148485421)
            ·
              refine ⟨9803865799925503930682033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26143642133134677148485421 9803865799925503930682033)
              ·
                refine ⟨7352899349944127948011525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9803865799925503930682033 7352899349944127948011525)
                ·
                  refine ⟨1378668628114523990252161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7352899349944127948011525 1378668628114523990252161)
                  ·
                    refine ⟨1034001471085892992689121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1378668628114523990252161 1034001471085892992689121)
                    ·
                      refine ⟨775501103314419744516841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034001471085892992689121 775501103314419744516841)
                      ·
                        rfl

theorem cell23_1510283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 2, 2].length) (baseStart_1510283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510283 prefixEnd_1510283 := by exact prefixLift 1510283
  have htrace : WordTrace (prefixWord ++ tailWord_1510283) baseStart_1510283 baseEnd_1510283 := by
    simpa [prefixWord, tailWord_1510283, baseEnd_1510283] using wordTrace_append hprefix tailTrace_1510283
  have hstable : (prefixWord ++ tailWord_1510283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510283).length < 2 ^ (prefixWord ++ tailWord_1510283).sum := by decide
  have hdescent : baseEnd_1510283 < baseStart_1510283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510319 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 7]
def baseStart_1510319 : Nat := 118140960795 + 1510319 * 2 ^ 59
def prefixEnd_1510319 : Nat := 4983230072969 + 3 ^ 40 * 1510319 * 2
def baseEnd_1510319 : Nat := 258506529539327201222225

theorem tailTrace_1510319 : CollatzResearch.WordTrace tailWord_1510319 prefixEnd_1510319 258506529539327201222225 := by
  unfold tailWord_1510319
  simp only [CollatzResearch.WordTrace]
  refine ⟨55085859415379679794502011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36723906276919786529668007 55085859415379679794502011)
  ·
    refine ⟨82628789123069519691753017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55085859415379679794502011 82628789123069519691753017)
    ·
      refine ⟨61971591842302139768814763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82628789123069519691753017 61971591842302139768814763)
      ·
        refine ⟨92957387763453209653222145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61971591842302139768814763 92957387763453209653222145)
        ·
          refine ⟨69718040822589907239916609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92957387763453209653222145 69718040822589907239916609)
          ·
            refine ⟨52288530616942430429937457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69718040822589907239916609 52288530616942430429937457)
            ·
              refine ⟨39216397962706822822453093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52288530616942430429937457 39216397962706822822453093)
              ·
                refine ⟨7353074618007529279209955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39216397962706822822453093 7353074618007529279209955)
                ·
                  refine ⟨11029611927011293918814933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353074618007529279209955 11029611927011293918814933)
                  ·
                    refine ⟨258506529539327201222225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11029611927011293918814933 258506529539327201222225)
                    ·
                      rfl

theorem cell23_1510319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_1510319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510319 prefixEnd_1510319 := by exact prefixLift 1510319
  have htrace : WordTrace (prefixWord ++ tailWord_1510319) baseStart_1510319 baseEnd_1510319 := by
    simpa [prefixWord, tailWord_1510319, baseEnd_1510319] using wordTrace_append hprefix tailTrace_1510319
  have hstable : (prefixWord ++ tailWord_1510319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510319).length < 2 ^ (prefixWord ++ tailWord_1510319).sum := by decide
  have hdescent : baseEnd_1510319 < baseStart_1510319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510336 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_1510336 : Nat := 118140960795 + 1510336 * 2 ^ 59
def prefixEnd_1510336 : Nat := 4983230072969 + 3 ^ 40 * 1510336 * 2
def baseEnd_1510336 : Nat := 258509439263036012384699

theorem tailTrace_1510336 : CollatzResearch.WordTrace tailWord_1510336 prefixEnd_1510336 258509439263036012384699 := by
  unfold tailWord_1510336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27543239728159045848935431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36724319637545394465247241 27543239728159045848935431)
  ·
    refine ⟨41314859592238568773403147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27543239728159045848935431 41314859592238568773403147)
    ·
      refine ⟨61972289388357853160104721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41314859592238568773403147 61972289388357853160104721)
      ·
        refine ⟨46479217041268389870078541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61972289388357853160104721 46479217041268389870078541)
        ·
          refine ⟨17429706390475646201279453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46479217041268389870078541 17429706390475646201279453)
          ·
            refine ⟨6536139896428367325479795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17429706390475646201279453 6536139896428367325479795)
            ·
              refine ⟨9804209844642550988219693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536139896428367325479795 9804209844642550988219693)
              ·
                refine ⟨3676578691740956620582385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9804209844642550988219693 3676578691740956620582385)
                ·
                  refine ⟨2757434018805717465436789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676578691740956620582385 2757434018805717465436789)
                  ·
                    refine ⟨258509439263036012384699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2757434018805717465436789 258509439263036012384699)
                    ·
                      rfl

theorem cell23_1510336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_1510336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510336 prefixEnd_1510336 := by exact prefixLift 1510336
  have htrace : WordTrace (prefixWord ++ tailWord_1510336) baseStart_1510336 baseEnd_1510336 := by
    simpa [prefixWord, tailWord_1510336, baseEnd_1510336] using wordTrace_append hprefix tailTrace_1510336
  have hstable : (prefixWord ++ tailWord_1510336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510336).length < 2 ^ (prefixWord ++ tailWord_1510336).sum := by decide
  have hdescent : baseEnd_1510336 < baseStart_1510336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510357 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 5]
def baseStart_1510357 : Nat := 118140960795 + 1510357 * 2 ^ 59
def prefixEnd_1510357 : Nat := 4983230072969 + 3 ^ 40 * 1510357 * 2
def baseEnd_1510357 : Nat := 86171011209205828332389

theorem tailTrace_1510357 : CollatzResearch.WordTrace tailWord_1510357 prefixEnd_1510357 86171011209205828332389 := by
  unfold tailWord_1510357
  simp only [CollatzResearch.WordTrace]
  refine ⟨55087245389242012284385325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36724830259494674856256883 55087245389242012284385325)
  ·
    refine ⟨20657717020965754606644497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55087245389242012284385325 20657717020965754606644497)
    ·
      refine ⟨15493287765724315954983373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20657717020965754606644497 15493287765724315954983373)
      ·
        refine ⟨5809982912146618483118765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15493287765724315954983373 5809982912146618483118765)
        ·
          refine ⟨2178743592054981931169537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5809982912146618483118765 2178743592054981931169537)
          ·
            refine ⟨1634057694041236448377153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2178743592054981931169537 1634057694041236448377153)
            ·
              refine ⟨1225543270530927336282865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634057694041236448377153 1225543270530927336282865)
              ·
                refine ⟨919157452898195502212149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225543270530927336282865 919157452898195502212149)
                ·
                  refine ⟨86171011209205828332389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 919157452898195502212149 86171011209205828332389)
                  ·
                    rfl

theorem cell23_1510357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_1510357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510357 prefixEnd_1510357 := by exact prefixLift 1510357
  have htrace : WordTrace (prefixWord ++ tailWord_1510357) baseStart_1510357 baseEnd_1510357 := by
    simpa [prefixWord, tailWord_1510357, baseEnd_1510357] using wordTrace_append hprefix tailTrace_1510357
  have hstable : (prefixWord ++ tailWord_1510357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510357).length < 2 ^ (prefixWord ++ tailWord_1510357).sum := by decide
  have hdescent : baseEnd_1510357 < baseStart_1510357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510379 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 12]
def baseStart_1510379 : Nat := 118140960795 + 1510379 * 2 ^ 59
def prefixEnd_1510379 : Nat := 4983230072969 + 3 ^ 40 * 1510379 * 2
def baseEnd_1510379 : Nat := 86172266384139040990711

theorem tailTrace_1510379 : CollatzResearch.WordTrace tailWord_1510379 prefixEnd_1510379 86172266384139040990711 := by
  unfold tailWord_1510379
  simp only [CollatzResearch.WordTrace]
  refine ⟨55088047795162310041686191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36725365196774873361124127 55088047795162310041686191)
  ·
    refine ⟨82632071692743465062529287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55088047795162310041686191 82632071692743465062529287)
    ·
      refine ⟨123948107539115197593793931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82632071692743465062529287 123948107539115197593793931)
      ·
        refine ⟨185922161308672796390690897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123948107539115197593793931 185922161308672796390690897)
        ·
          refine ⟨139441620981504597293018173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185922161308672796390690897 139441620981504597293018173)
          ·
            refine ⟨52290607868064223984881815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139441620981504597293018173 52290607868064223984881815)
            ·
              refine ⟨78435911802096335977322723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52290607868064223984881815 78435911802096335977322723)
              ·
                refine ⟨117653867703144503965984085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78435911802096335977322723 117653867703144503965984085)
                ·
                  refine ⟨86172266384139040990711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 117653867703144503965984085 86172266384139040990711)
                  ·
                    rfl

theorem cell23_1510379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 12].length) (baseStart_1510379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510379 prefixEnd_1510379 := by exact prefixLift 1510379
  have htrace : WordTrace (prefixWord ++ tailWord_1510379) baseStart_1510379 baseEnd_1510379 := by
    simpa [prefixWord, tailWord_1510379, baseEnd_1510379] using wordTrace_append hprefix tailTrace_1510379
  have hstable : (prefixWord ++ tailWord_1510379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510379).length < 2 ^ (prefixWord ++ tailWord_1510379).sum := by decide
  have hdescent : baseEnd_1510379 < baseStart_1510379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510383 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 3, 4]
def baseStart_1510383 : Nat := 118140960795 + 1510383 * 2 ^ 59
def prefixEnd_1510383 : Nat := 4983230072969 + 3 ^ 40 * 1510383 * 2
def baseEnd_1510383 : Nat := 258517483793289784422127

theorem tailTrace_1510383 : CollatzResearch.WordTrace tailWord_1510383 prefixEnd_1510383 258517483793289784422127 := by
  unfold tailWord_1510383
  simp only [CollatzResearch.WordTrace]
  refine ⟨55088193687147818724831803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36725462458098545816554535 55088193687147818724831803)
  ·
    refine ⟨82632290530721728087247705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55088193687147818724831803 82632290530721728087247705)
    ·
      refine ⟨61974217898041296065435779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82632290530721728087247705 61974217898041296065435779)
      ·
        refine ⟨92961326847061944098153669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61974217898041296065435779 92961326847061944098153669)
        ·
          refine ⟨17430248783824114518403813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92961326847061944098153669 17430248783824114518403813)
          ·
            refine ⟨3268171646967021472200715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17430248783824114518403813 3268171646967021472200715)
            ·
              refine ⟨4902257470450532208301073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268171646967021472200715 4902257470450532208301073)
              ·
                refine ⟨3676693102837899156225805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4902257470450532208301073 3676693102837899156225805)
                ·
                  refine ⟨1378759913564212183584677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3676693102837899156225805 1378759913564212183584677)
                  ·
                    refine ⟨258517483793289784422127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378759913564212183584677 258517483793289784422127)
                    ·
                      rfl

theorem cell23_1510383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_1510383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510383 prefixEnd_1510383 := by exact prefixLift 1510383
  have htrace : WordTrace (prefixWord ++ tailWord_1510383) baseStart_1510383 baseEnd_1510383 := by
    simpa [prefixWord, tailWord_1510383, baseEnd_1510383] using wordTrace_append hprefix tailTrace_1510383
  have hstable : (prefixWord ++ tailWord_1510383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510383).length < 2 ^ (prefixWord ++ tailWord_1510383).sum := by decide
  have hdescent : baseEnd_1510383 < baseStart_1510383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510390 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1510390 : Nat := 118140960795 + 1510390 * 2 ^ 59
def prefixEnd_1510390 : Nat := 4983230072969 + 3 ^ 40 * 1510390 * 2
def baseEnd_1510390 : Nat := 775556045744450825878849

theorem tailTrace_1510390 : CollatzResearch.WordTrace tailWord_1510390 prefixEnd_1510390 775556045744450825878849 := by
  unfold tailWord_1510390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3443028062382653682521039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36725632665414972613557749 3443028062382653682521039)
  ·
    refine ⟨5164542093573980523781559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3443028062382653682521039 5164542093573980523781559)
    ·
      refine ⟨7746813140360970785672339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5164542093573980523781559 7746813140360970785672339)
      ·
        refine ⟨11620219710541456178508509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746813140360970785672339 11620219710541456178508509)
        ·
          refine ⟨4357582391453046066940691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11620219710541456178508509 4357582391453046066940691)
          ·
            refine ⟨6536373587179569100411037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357582391453046066940691 6536373587179569100411037)
            ·
              refine ⟨2451140095192338412654139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6536373587179569100411037 2451140095192338412654139)
              ·
                refine ⟨3676710142788507618981209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451140095192338412654139 3676710142788507618981209)
                ·
                  refine ⟨2757532607091380714235907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676710142788507618981209 2757532607091380714235907)
                  ·
                    refine ⟨4136298910637071071353861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2757532607091380714235907 4136298910637071071353861)
                    ·
                      refine ⟨775556045744450825878849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4136298910637071071353861 775556045744450825878849)
                      ·
                        rfl

theorem cell23_1510390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1510390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510390 prefixEnd_1510390 := by exact prefixLift 1510390
  have htrace : WordTrace (prefixWord ++ tailWord_1510390) baseStart_1510390 baseEnd_1510390 := by
    simpa [prefixWord, tailWord_1510390, baseEnd_1510390] using wordTrace_append hprefix tailTrace_1510390
  have hstable : (prefixWord ++ tailWord_1510390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510390).length < 2 ^ (prefixWord ++ tailWord_1510390).sum := by decide
  have hdescent : baseEnd_1510390 < baseStart_1510390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510443 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 1, 5]
def baseStart_1510443 : Nat := 118140960795 + 1510443 * 2 ^ 59
def prefixEnd_1510443 : Nat := 4983230072969 + 3 ^ 40 * 1510443 * 2
def baseEnd_1510443 : Nat := 258527753406379706172035

theorem tailTrace_1510443 : CollatzResearch.WordTrace tailWord_1510443 prefixEnd_1510443 258527753406379706172035 := by
  unfold tailWord_1510443
  simp only [CollatzResearch.WordTrace]
  refine ⟨55090382066930448972015983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36726921377953632648010655 55090382066930448972015983)
  ·
    refine ⟨82635573100395673458023975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55090382066930448972015983 82635573100395673458023975)
    ·
      refine ⟨123953359650593510187035963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82635573100395673458023975 123953359650593510187035963)
      ·
        refine ⟨185930039475890265280553945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123953359650593510187035963 185930039475890265280553945)
        ·
          refine ⟨139447529606917698960415459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185930039475890265280553945 139447529606917698960415459)
          ·
            refine ⟨209171294410376548440623189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139447529606917698960415459 209171294410376548440623189)
            ·
              refine ⟨2451226106371600177038553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 209171294410376548440623189 2451226106371600177038553)
              ·
                refine ⟨1838419579778700132778915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451226106371600177038553 1838419579778700132778915)
                ·
                  refine ⟨2757629369668050199168373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838419579778700132778915 2757629369668050199168373)
                  ·
                    refine ⟨258527753406379706172035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2757629369668050199168373 258527753406379706172035)
                    ·
                      rfl

theorem cell23_1510443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 5].length) (baseStart_1510443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510443 prefixEnd_1510443 := by exact prefixLift 1510443
  have htrace : WordTrace (prefixWord ++ tailWord_1510443) baseStart_1510443 baseEnd_1510443 := by
    simpa [prefixWord, tailWord_1510443, baseEnd_1510443] using wordTrace_append hprefix tailTrace_1510443
  have hstable : (prefixWord ++ tailWord_1510443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510443).length < 2 ^ (prefixWord ++ tailWord_1510443).sum := by decide
  have hdescent : baseEnd_1510443 < baseStart_1510443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510450 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_1510450 : Nat := 118140960795 + 1510450 * 2 ^ 59
def prefixEnd_1510450 : Nat := 4983230072969 + 3 ^ 40 * 1510450 * 2
def baseEnd_1510450 : Nat := 775586854583720591128573

theorem tailTrace_1510450 : CollatzResearch.WordTrace tailWord_1510450 prefixEnd_1510450 775586854583720591128573 := by
  unfold tailWord_1510450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13772659344476272291880201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36727091585270059445013869 13772659344476272291880201)
  ·
    refine ⟨10329494508357204218910151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13772659344476272291880201 10329494508357204218910151)
    ·
      refine ⟨15494241762535806328365227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10329494508357204218910151 15494241762535806328365227)
      ·
        refine ⟨23241362643803709492547841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15494241762535806328365227 23241362643803709492547841)
        ·
          refine ⟨17431021982852782119410881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23241362643803709492547841 17431021982852782119410881)
          ·
            refine ⟨13073266487139586589558161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17431021982852782119410881 13073266487139586589558161)
            ·
              refine ⟨9804949865354689942168621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13073266487139586589558161 9804949865354689942168621)
              ·
                refine ⟨3676856199508008728313233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9804949865354689942168621 3676856199508008728313233)
                ·
                  refine ⟨2757642149631006546234925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676856199508008728313233 2757642149631006546234925)
                  ·
                    refine ⟨1034115806111627454838097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757642149631006546234925 1034115806111627454838097)
                    ·
                      refine ⟨775586854583720591128573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034115806111627454838097 775586854583720591128573)
                      ·
                        rfl

theorem cell23_1510450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_1510450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510450 prefixEnd_1510450 := by exact prefixLift 1510450
  have htrace : WordTrace (prefixWord ++ tailWord_1510450) baseStart_1510450 baseEnd_1510450 := by
    simpa [prefixWord, tailWord_1510450, baseEnd_1510450] using wordTrace_append hprefix tailTrace_1510450
  have hstable : (prefixWord ++ tailWord_1510450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510450).length < 2 ^ (prefixWord ++ tailWord_1510450).sum := by decide
  have hdescent : baseEnd_1510450 < baseStart_1510450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510494 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1510494 : Nat := 118140960795 + 1510494 * 2 ^ 59
def prefixEnd_1510494 : Nat := 4983230072969 + 3 ^ 40 * 1510494 * 2
def baseEnd_1510494 : Nat := 258536482577506139659457

theorem tailTrace_1510494 : CollatzResearch.WordTrace tailWord_1510494 prefixEnd_1510494 258536482577506139659457 := by
  unfold tailWord_1510494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886530273718210585265317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36728161459830456454748357 6886530273718210585265317)
  ·
    refine ⟨1291224426322164484737247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6886530273718210585265317 1291224426322164484737247)
    ·
      refine ⟨1936836639483246727105871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291224426322164484737247 1936836639483246727105871)
      ·
        refine ⟨2905254959224870090658807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936836639483246727105871 2905254959224870090658807)
        ·
          refine ⟨4357882438837305135988211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905254959224870090658807 4357882438837305135988211)
          ·
            refine ⟨6536823658255957703982317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357882438837305135988211 6536823658255957703982317)
            ·
              refine ⟨2451308871845984138993369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6536823658255957703982317 2451308871845984138993369)
              ·
                refine ⟨1838481653884488104245027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451308871845984138993369 1838481653884488104245027)
                ·
                  refine ⟨2757722480826732156367541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838481653884488104245027 2757722480826732156367541)
                  ·
                    refine ⟨258536482577506139659457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2757722480826732156367541 258536482577506139659457)
                    ·
                      rfl

theorem cell23_1510494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1510494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510494 prefixEnd_1510494 := by exact prefixLift 1510494
  have htrace : WordTrace (prefixWord ++ tailWord_1510494) baseStart_1510494 baseEnd_1510494 := by
    simpa [prefixWord, tailWord_1510494, baseEnd_1510494] using wordTrace_append hprefix tailTrace_1510494
  have hstable : (prefixWord ++ tailWord_1510494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510494).length < 2 ^ (prefixWord ++ tailWord_1510494).sum := by decide
  have hdescent : baseEnd_1510494 < baseStart_1510494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510510 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1510510 : Nat := 118140960795 + 1510510 * 2 ^ 59
def prefixEnd_1510510 : Nat := 4983230072969 + 3 ^ 40 * 1510510 * 2
def baseEnd_1510510 : Nat := 775617663422990356378297

theorem tailTrace_1510510 : CollatzResearch.WordTrace tailWord_1510510 prefixEnd_1510510 775617663422990356378297 := by
  unfold tailWord_1510510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886603219710964926838123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36728550505125146276469989 6886603219710964926838123)
  ·
    refine ⟨10329904829566447390257185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6886603219710964926838123 10329904829566447390257185)
    ·
      refine ⟨7747428622174835542692889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10329904829566447390257185 7747428622174835542692889)
      ·
        refine ⟨5810571466631126657019667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7747428622174835542692889 5810571466631126657019667)
        ·
          refine ⟨8715857199946689985529501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5810571466631126657019667 8715857199946689985529501)
          ·
            refine ⟨3268446449980008744573563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8715857199946689985529501 3268446449980008744573563)
            ·
              refine ⟨4902669674970013116860345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268446449980008744573563 4902669674970013116860345)
              ·
                refine ⟨3677002256227509837645259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4902669674970013116860345 3677002256227509837645259)
                ·
                  refine ⟨5515503384341264756467889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677002256227509837645259 5515503384341264756467889)
                  ·
                    refine ⟨4136627538255948567350917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515503384341264756467889 4136627538255948567350917)
                    ·
                      refine ⟨775617663422990356378297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4136627538255948567350917 775617663422990356378297)
                      ·
                        rfl

theorem cell23_1510510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1510510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510510 prefixEnd_1510510 := by exact prefixLift 1510510
  have htrace : WordTrace (prefixWord ++ tailWord_1510510) baseStart_1510510 baseEnd_1510510 := by
    simpa [prefixWord, tailWord_1510510, baseEnd_1510510] using wordTrace_append hprefix tailTrace_1510510
  have hstable : (prefixWord ++ tailWord_1510510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510510).length < 2 ^ (prefixWord ++ tailWord_1510510).sum := by decide
  have hdescent : baseEnd_1510510 < baseStart_1510510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510514 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_1510514 : Nat := 118140960795 + 1510514 * 2 ^ 59
def prefixEnd_1510514 : Nat := 4983230072969 + 3 ^ 40 * 1510514 * 2
def baseEnd_1510514 : Nat := 775619717345608340728279

theorem tailTrace_1510514 : CollatzResearch.WordTrace tailWord_1510514 prefixEnd_1510514 775619717345608340728279 := by
  unfold tailWord_1510514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13773242912418307024462649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36728647766448818731900397 13773242912418307024462649)
  ·
    refine ⟨10329932184313730268346987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13773242912418307024462649 10329932184313730268346987)
    ·
      refine ⟨15494898276470595402520481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10329932184313730268346987 15494898276470595402520481)
      ·
        refine ⟨11621173707352946551890361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15494898276470595402520481 11621173707352946551890361)
        ·
          refine ⟨8715880280514709913917771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11621173707352946551890361 8715880280514709913917771)
          ·
            refine ⟨13073820420772064870876657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715880280514709913917771 13073820420772064870876657)
            ·
              refine ⟨9805365315579048653157493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13073820420772064870876657 9805365315579048653157493)
              ·
                refine ⟨919252998335535811233515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9805365315579048653157493 919252998335535811233515)
                ·
                  refine ⟨1378879497503303716850273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919252998335535811233515 1378879497503303716850273)
                  ·
                    refine ⟨1034159623127477787637705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1378879497503303716850273 1034159623127477787637705)
                    ·
                      refine ⟨775619717345608340728279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034159623127477787637705 775619717345608340728279)
                      ·
                        rfl

theorem cell23_1510514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_1510514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510514 prefixEnd_1510514 := by exact prefixLift 1510514
  have htrace : WordTrace (prefixWord ++ tailWord_1510514) baseStart_1510514 baseEnd_1510514 := by
    simpa [prefixWord, tailWord_1510514, baseEnd_1510514] using wordTrace_append hprefix tailTrace_1510514
  have hstable : (prefixWord ++ tailWord_1510514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510514).length < 2 ^ (prefixWord ++ tailWord_1510514).sum := by decide
  have hdescent : baseEnd_1510514 < baseStart_1510514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510557 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_1510557 : Nat := 118140960795 + 1510557 * 2 ^ 59
def prefixEnd_1510557 : Nat := 4983230072969 + 3 ^ 40 * 1510557 * 2
def baseEnd_1510557 : Nat := 775641797013751672490581

theorem tailTrace_1510557 : CollatzResearch.WordTrace tailWord_1510557 prefixEnd_1510557 775641797013751672490581 := by
  unfold tailWord_1510557
  simp only [CollatzResearch.WordTrace]
  refine ⟨55094539988517446441665925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36729693325678297627777283 55094539988517446441665925)
  ·
    refine ⟨10330226247847021207812361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55094539988517446441665925 10330226247847021207812361)
    ·
      refine ⟨7747669685885265905859271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10330226247847021207812361 7747669685885265905859271)
      ·
        refine ⟨11621504528827898858788907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7747669685885265905859271 11621504528827898858788907)
        ·
          refine ⟨17432256793241848288183361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11621504528827898858788907 17432256793241848288183361)
          ·
            refine ⟨13074192594931386216137521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17432256793241848288183361 13074192594931386216137521)
            ·
              refine ⟨9805644446198539662103141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13074192594931386216137521 9805644446198539662103141)
              ·
                refine ⟨1838558333662226186644339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9805644446198539662103141 1838558333662226186644339)
                ·
                  refine ⟨2757837500493339279966509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838558333662226186644339 2757837500493339279966509)
                  ·
                    refine ⟨1034189062685002229987441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2757837500493339279966509 1034189062685002229987441)
                    ·
                      refine ⟨775641797013751672490581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034189062685002229987441 775641797013751672490581)
                      ·
                        rfl

theorem cell23_1510557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_1510557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510557 prefixEnd_1510557 := by exact prefixLift 1510557
  have htrace : WordTrace (prefixWord ++ tailWord_1510557) baseStart_1510557 baseEnd_1510557 := by
    simpa [prefixWord, tailWord_1510557, baseEnd_1510557] using wordTrace_append hprefix tailTrace_1510557
  have hstable : (prefixWord ++ tailWord_1510557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510557).length < 2 ^ (prefixWord ++ tailWord_1510557).sum := by decide
  have hdescent : baseEnd_1510557 < baseStart_1510557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510583 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_1510583 : Nat := 118140960795 + 1510583 * 2 ^ 59
def prefixEnd_1510583 : Nat := 4983230072969 + 3 ^ 40 * 1510583 * 2
def baseEnd_1510583 : Nat := 775655147510768570765461

theorem tailTrace_1510583 : CollatzResearch.WordTrace tailWord_1510583 prefixEnd_1510583 775655147510768570765461 := by
  unfold tailWord_1510583
  simp only [CollatzResearch.WordTrace]
  refine ⟨55095488286423252882112403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36730325524282168588074935 55095488286423252882112403)
  ·
    refine ⟨82643232429634879323168605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55095488286423252882112403 82643232429634879323168605)
    ·
      refine ⟨30991212161113079746188227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82643232429634879323168605 30991212161113079746188227)
      ·
        refine ⟨46486818241669619619282341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30991212161113079746188227 46486818241669619619282341)
        ·
          refine ⟨8716278420313053678615439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46486818241669619619282341 8716278420313053678615439)
          ·
            refine ⟨13074417630469580517923159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716278420313053678615439 13074417630469580517923159)
            ·
              refine ⟨19611626445704370776884739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13074417630469580517923159 19611626445704370776884739)
              ·
                refine ⟨29417439668556556165327109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19611626445704370776884739 29417439668556556165327109)
                ·
                  refine ⟨5515769937854354280998833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29417439668556556165327109 5515769937854354280998833)
                  ·
                    refine ⟨4136827453390765710749125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515769937854354280998833 4136827453390765710749125)
                    ·
                      refine ⟨775655147510768570765461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4136827453390765710749125 775655147510768570765461)
                      ·
                        rfl

theorem cell23_1510583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_1510583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510583 prefixEnd_1510583 := by exact prefixLift 1510583
  have htrace : WordTrace (prefixWord ++ tailWord_1510583) baseStart_1510583 baseEnd_1510583 := by
    simpa [prefixWord, tailWord_1510583, baseEnd_1510583] using wordTrace_append hprefix tailTrace_1510583
  have hstable : (prefixWord ++ tailWord_1510583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510583).length < 2 ^ (prefixWord ++ tailWord_1510583).sum := by decide
  have hdescent : baseEnd_1510583 < baseStart_1510583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510587 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 2, 2, 2]
def baseStart_1510587 : Nat := 118140960795 + 1510587 * 2 ^ 59
def prefixEnd_1510587 : Nat := 4983230072969 + 3 ^ 40 * 1510587 * 2
def baseEnd_1510587 : Nat := 775657201433386555115443

theorem tailTrace_1510587 : CollatzResearch.WordTrace tailWord_1510587 prefixEnd_1510587 775657201433386555115443 := by
  unfold tailWord_1510587
  simp only [CollatzResearch.WordTrace]
  refine ⟨55095634178408761565258015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36730422785605841043505343 55095634178408761565258015)
  ·
    refine ⟨82643451267613142347887023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55095634178408761565258015 82643451267613142347887023)
    ·
      refine ⟨123965176901419713521830535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82643451267613142347887023 123965176901419713521830535)
      ·
        refine ⟨185947765352129570282745803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123965176901419713521830535 185947765352129570282745803)
        ·
          refine ⟨278921648028194355424118705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185947765352129570282745803 278921648028194355424118705)
          ·
            refine ⟨209191236021145766568089029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278921648028194355424118705 209191236021145766568089029)
            ·
              refine ⟨39223356753964831231516693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209191236021145766568089029 39223356753964831231516693)
              ·
                refine ⟨1838594847842101463977345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39223356753964831231516693 1838594847842101463977345)
                ·
                  refine ⟨1378946135881576097983009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838594847842101463977345 1378946135881576097983009)
                  ·
                    refine ⟨1034209601911182073487257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1378946135881576097983009 1034209601911182073487257)
                    ·
                      refine ⟨775657201433386555115443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034209601911182073487257 775657201433386555115443)
                      ·
                        rfl

theorem cell23_1510587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2, 2].length) (baseStart_1510587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510587 prefixEnd_1510587 := by exact prefixLift 1510587
  have htrace : WordTrace (prefixWord ++ tailWord_1510587) baseStart_1510587 baseEnd_1510587 := by
    simpa [prefixWord, tailWord_1510587, baseEnd_1510587] using wordTrace_append hprefix tailTrace_1510587
  have hstable : (prefixWord ++ tailWord_1510587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510587).length < 2 ^ (prefixWord ++ tailWord_1510587).sum := by decide
  have hdescent : baseEnd_1510587 < baseStart_1510587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510598 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1510598 : Nat := 118140960795 + 1510598 * 2 ^ 59
def prefixEnd_1510598 : Nat := 4983230072969 + 3 ^ 40 * 1510598 * 2
def baseEnd_1510598 : Nat := 775662849720586012077893

theorem tailTrace_1510598 : CollatzResearch.WordTrace tailWord_1510598 prefixEnd_1510598 775662849720586012077893 := by
  unfold tailWord_1510598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721751105667778451372139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36730690254245940295938965 1721751105667778451372139)
  ·
    refine ⟨2582626658501667677058209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721751105667778451372139 2582626658501667677058209)
    ·
      refine ⟨1936969993876250757793657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2582626658501667677058209 1936969993876250757793657)
      ·
        refine ⟨1452727495407188068345243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936969993876250757793657 1452727495407188068345243)
        ·
          refine ⟨2179091243110782102517865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452727495407188068345243 2179091243110782102517865)
          ·
            refine ⟨1634318432333086576888399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179091243110782102517865 1634318432333086576888399)
            ·
              refine ⟨2451477648499629865332599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634318432333086576888399 2451477648499629865332599)
              ·
                refine ⟨3677216472749444797998899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451477648499629865332599 3677216472749444797998899)
                ·
                  refine ⟨5515824709124167196998349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677216472749444797998899 5515824709124167196998349)
                  ·
                    refine ⟨2068434265921562698874381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5515824709124167196998349 2068434265921562698874381)
                    ·
                      refine ⟨775662849720586012077893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2068434265921562698874381 775662849720586012077893)
                      ·
                        rfl

theorem cell23_1510598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1510598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510598 prefixEnd_1510598 := by exact prefixLift 1510598
  have htrace : WordTrace (prefixWord ++ tailWord_1510598) baseStart_1510598 baseEnd_1510598 := by
    simpa [prefixWord, tailWord_1510598, baseEnd_1510598] using wordTrace_append hprefix tailTrace_1510598
  have hstable : (prefixWord ++ tailWord_1510598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510598).length < 2 ^ (prefixWord ++ tailWord_1510598).sum := by decide
  have hdescent : baseEnd_1510598 < baseStart_1510598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510603 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3]
def baseStart_1510603 : Nat := 118140960795 + 1510603 * 2 ^ 59
def prefixEnd_1510603 : Nat := 4983230072969 + 3 ^ 40 * 1510603 * 2
def baseEnd_1510603 : Nat := 775665417123858492515369

theorem tailTrace_1510603 : CollatzResearch.WordTrace tailWord_1510603 prefixEnd_1510603 775665417123858492515369 := by
  unfold tailWord_1510603
  simp only [CollatzResearch.WordTrace]
  refine ⟨55096217746350796297840463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36730811830900530865226975 55096217746350796297840463)
  ·
    refine ⟨82644326619526194446760695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55096217746350796297840463 82644326619526194446760695)
    ·
      refine ⟨123966489929289291670141043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82644326619526194446760695 123966489929289291670141043)
      ·
        refine ⟨185949734893933937505211565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123966489929289291670141043 185949734893933937505211565)
        ·
          refine ⟨69731150585225226564454337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185949734893933937505211565 69731150585225226564454337)
          ·
            refine ⟨52298362938918919923340753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69731150585225226564454337 52298362938918919923340753)
            ·
              refine ⟨39223772204189189942505565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52298362938918919923340753 39223772204189189942505565)
              ·
                refine ⟨14708914576570946228439587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39223772204189189942505565 14708914576570946228439587)
                ·
                  refine ⟨22063371864856419342659381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14708914576570946228439587 22063371864856419342659381)
                  ·
                    refine ⟨2068441112330289313374317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22063371864856419342659381 2068441112330289313374317)
                    ·
                      refine ⟨775665417123858492515369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2068441112330289313374317 775665417123858492515369)
                      ·
                        rfl

theorem cell23_1510603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3].length) (baseStart_1510603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510603 prefixEnd_1510603 := by exact prefixLift 1510603
  have htrace : WordTrace (prefixWord ++ tailWord_1510603) baseStart_1510603 baseEnd_1510603 := by
    simpa [prefixWord, tailWord_1510603, baseEnd_1510603] using wordTrace_append hprefix tailTrace_1510603
  have hstable : (prefixWord ++ tailWord_1510603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510603).length < 2 ^ (prefixWord ++ tailWord_1510603).sum := by decide
  have hdescent : baseEnd_1510603 < baseStart_1510603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510623 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 7]
def baseStart_1510623 : Nat := 118140960795 + 1510623 * 2 ^ 59
def prefixEnd_1510623 : Nat := 4983230072969 + 3 ^ 40 * 1510623 * 2
def baseEnd_1510623 : Nat := 258558562245649471421759

theorem tailTrace_1510623 : CollatzResearch.WordTrace tailWord_1510623 prefixEnd_1510623 258558562245649471421759 := by
  unfold tailWord_1510623
  simp only [CollatzResearch.WordTrace]
  refine ⟨55096947206278339713568523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36731298137518893142379015 55096947206278339713568523)
  ·
    refine ⟨82645420809417509570352785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55096947206278339713568523 82645420809417509570352785)
    ·
      refine ⟨61984065607063132177764589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82645420809417509570352785 61984065607063132177764589)
      ·
        refine ⟨23244024602648674566661721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61984065607063132177764589 23244024602648674566661721)
        ·
          refine ⟨17433018451986505924996291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23244024602648674566661721 17433018451986505924996291)
          ·
            refine ⟨26149527677979758887494437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433018451986505924996291 26149527677979758887494437)
            ·
              refine ⟨4903036439621204791405207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26149527677979758887494437 4903036439621204791405207)
              ·
                refine ⟨7354554659431807187107811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903036439621204791405207 7354554659431807187107811)
                ·
                  refine ⟨11031831989147710780661717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354554659431807187107811 11031831989147710780661717)
                  ·
                    refine ⟨258558562245649471421759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11031831989147710780661717 258558562245649471421759)
                    ·
                      rfl

theorem cell23_1510623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_1510623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510623 prefixEnd_1510623 := by exact prefixLift 1510623
  have htrace : WordTrace (prefixWord ++ tailWord_1510623) baseStart_1510623 baseEnd_1510623 := by
    simpa [prefixWord, tailWord_1510623, baseEnd_1510623] using wordTrace_append hprefix tailTrace_1510623
  have hstable : (prefixWord ++ tailWord_1510623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510623).length < 2 ^ (prefixWord ++ tailWord_1510623).sum := by decide
  have hdescent : baseEnd_1510623 < baseStart_1510623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510703 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_1510703 : Nat := 118140960795 + 1510703 * 2 ^ 59
def prefixEnd_1510703 : Nat := 4983230072969 + 3 ^ 40 * 1510703 * 2
def baseEnd_1510703 : Nat := 775716765189308101264909

theorem tailTrace_1510703 : CollatzResearch.WordTrace tailWord_1510703 prefixEnd_1510703 775716765189308101264909 := by
  unfold tailWord_1510703
  simp only [CollatzResearch.WordTrace]
  refine ⟨55099865045988513376480763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36733243363992342250987175 55099865045988513376480763)
  ·
    refine ⟨82649797568982770064721145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55099865045988513376480763 82649797568982770064721145)
    ·
      refine ⟨61987348176737077548540859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82649797568982770064721145 61987348176737077548540859)
      ·
        refine ⟨92981022265105616322811289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61987348176737077548540859 92981022265105616322811289)
        ·
          refine ⟨69735766698829212242108467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92981022265105616322811289 69735766698829212242108467)
          ·
            refine ⟨104603650048243818363162701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69735766698829212242108467 104603650048243818363162701)
            ·
              refine ⟨39226368768091431886186013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104603650048243818363162701 39226368768091431886186013)
              ·
                refine ⟨14709888288034286957319755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39226368768091431886186013 14709888288034286957319755)
                ·
                  refine ⟨22064832432051430435979633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14709888288034286957319755 22064832432051430435979633)
                  ·
                    refine ⟨16548624324038572826984725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22064832432051430435979633 16548624324038572826984725)
                    ·
                      refine ⟨775716765189308101264909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16548624324038572826984725 775716765189308101264909)
                      ·
                        rfl

theorem cell23_1510703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_1510703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510703 prefixEnd_1510703 := by exact prefixLift 1510703
  have htrace : WordTrace (prefixWord ++ tailWord_1510703) baseStart_1510703 baseEnd_1510703 := by
    simpa [prefixWord, tailWord_1510703, baseEnd_1510703] using wordTrace_append hprefix tailTrace_1510703
  have hstable : (prefixWord ++ tailWord_1510703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510703).length < 2 ^ (prefixWord ++ tailWord_1510703).sum := by decide
  have hdescent : baseEnd_1510703 < baseStart_1510703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510723 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1510723 : Nat := 118140960795 + 1510723 * 2 ^ 59
def prefixEnd_1510723 : Nat := 4983230072969 + 3 ^ 40 * 1510723 * 2
def baseEnd_1510723 : Nat := 775727034802398023014817

theorem tailTrace_1510723 : CollatzResearch.WordTrace tailWord_1510723 prefixEnd_1510723 775727034802398023014817 := by
  unfold tailWord_1510723
  simp only [CollatzResearch.WordTrace]
  refine ⟨55100594505916056792208823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36733729670610704528139215 55100594505916056792208823)
  ·
    refine ⟨82650891758874085188313235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55100594505916056792208823 82650891758874085188313235)
    ·
      refine ⟨123976337638311127782469853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82650891758874085188313235 123976337638311127782469853)
      ·
        refine ⟨46491126614366672918426195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123976337638311127782469853 46491126614366672918426195)
        ·
          refine ⟨69736689921550009377639293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46491126614366672918426195 69736689921550009377639293)
          ·
            refine ⟨26151258720581253516614735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69736689921550009377639293 26151258720581253516614735)
            ·
              refine ⟨39226888080871880274922103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26151258720581253516614735 39226888080871880274922103)
              ·
                refine ⟨58840332121307820412383155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39226888080871880274922103 58840332121307820412383155)
                ·
                  refine ⟨88260498181961730618574733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58840332121307820412383155 88260498181961730618574733)
                  ·
                    refine ⟨33097686818235648981965525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88260498181961730618574733 33097686818235648981965525)
                    ·
                      refine ⟨775727034802398023014817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33097686818235648981965525 775727034802398023014817)
                      ·
                        rfl

theorem cell23_1510723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1510723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510723 prefixEnd_1510723 := by exact prefixLift 1510723
  have htrace : WordTrace (prefixWord ++ tailWord_1510723) baseStart_1510723 baseEnd_1510723 := by
    simpa [prefixWord, tailWord_1510723, baseEnd_1510723] using wordTrace_append hprefix tailTrace_1510723
  have hstable : (prefixWord ++ tailWord_1510723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510723).length < 2 ^ (prefixWord ++ tailWord_1510723).sum := by decide
  have hdescent : baseEnd_1510723 < baseStart_1510723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510727 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_1510727 : Nat := 118140960795 + 1510727 * 2 ^ 59
def prefixEnd_1510727 : Nat := 4983230072969 + 3 ^ 40 * 1510727 * 2
def baseEnd_1510727 : Nat := 775729088725016007364799

theorem tailTrace_1510727 : CollatzResearch.WordTrace tailWord_1510727 prefixEnd_1510727 775729088725016007364799 := by
  unfold tailWord_1510727
  simp only [CollatzResearch.WordTrace]
  refine ⟨55100740397901565475354435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36733826931934376983569623 55100740397901565475354435)
  ·
    refine ⟨82651110596852348213031653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55100740397901565475354435 82651110596852348213031653)
    ·
      refine ⟨15497083236909815289943435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82651110596852348213031653 15497083236909815289943435)
      ·
        refine ⟨23245624855364722934915153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497083236909815289943435 23245624855364722934915153)
        ·
          refine ⟨17434218641523542201186365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23245624855364722934915153 17434218641523542201186365)
          ·
            refine ⟨6537831990571328325444887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17434218641523542201186365 6537831990571328325444887)
            ·
              refine ⟨9806747985856992488167331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537831990571328325444887 9806747985856992488167331)
              ·
                refine ⟨14710121978785488732250997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806747985856992488167331 14710121978785488732250997)
                ·
                  refine ⟨1379073935511139568648531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14710121978785488732250997 1379073935511139568648531)
                  ·
                    refine ⟨2068610903266709352972797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379073935511139568648531 2068610903266709352972797)
                    ·
                      refine ⟨775729088725016007364799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2068610903266709352972797 775729088725016007364799)
                      ·
                        rfl

theorem cell23_1510727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_1510727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510727 prefixEnd_1510727 := by exact prefixLift 1510727
  have htrace : WordTrace (prefixWord ++ tailWord_1510727) baseStart_1510727 baseEnd_1510727 := by
    simpa [prefixWord, tailWord_1510727, baseEnd_1510727] using wordTrace_append hprefix tailTrace_1510727
  have hstable : (prefixWord ++ tailWord_1510727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510727).length < 2 ^ (prefixWord ++ tailWord_1510727).sum := by decide
  have hdescent : baseEnd_1510727 < baseStart_1510727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510737 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 5, 2]
def baseStart_1510737 : Nat := 118140960795 + 1510737 * 2 ^ 59
def prefixEnd_1510737 : Nat := 4983230072969 + 3 ^ 40 * 1510737 * 2
def baseEnd_1510737 : Nat := 775734223531560968239753

theorem tailTrace_1510737 : CollatzResearch.WordTrace tailWord_1510737 prefixEnd_1510737 775734223531560968239753 := by
  unfold tailWord_1510737
  simp only [CollatzResearch.WordTrace]
  refine ⟨55101105127865337183218465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36734070085243558122145643 55101105127865337183218465)
  ·
    refine ⟨41325828845899002887413849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55101105127865337183218465 41325828845899002887413849)
    ·
      refine ⟨30994371634424252165560387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41325828845899002887413849 30994371634424252165560387)
      ·
        refine ⟨46491557451636378248340581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30994371634424252165560387 46491557451636378248340581)
        ·
          refine ⟨8717167022181820921563859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46491557451636378248340581 8717167022181820921563859)
          ·
            refine ⟨13075750533272731382345789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8717167022181820921563859 13075750533272731382345789)
            ·
              refine ⟨4903406449977274268379671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13075750533272731382345789 4903406449977274268379671)
              ·
                refine ⟨7355109674965911402569507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903406449977274268379671 7355109674965911402569507)
                ·
                  refine ⟨11032664512448867103854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355109674965911402569507 11032664512448867103854261)
                  ·
                    refine ⟨1034312298042081290986337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11032664512448867103854261 1034312298042081290986337)
                    ·
                      refine ⟨775734223531560968239753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034312298042081290986337 775734223531560968239753)
                      ·
                        rfl

theorem cell23_1510737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_1510737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510737 prefixEnd_1510737 := by exact prefixLift 1510737
  have htrace : WordTrace (prefixWord ++ tailWord_1510737) baseStart_1510737 baseEnd_1510737 := by
    simpa [prefixWord, tailWord_1510737, baseEnd_1510737] using wordTrace_append hprefix tailTrace_1510737
  have hstable : (prefixWord ++ tailWord_1510737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510737).length < 2 ^ (prefixWord ++ tailWord_1510737).sum := by decide
  have hdescent : baseEnd_1510737 < baseStart_1510737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510754 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1510754 : Nat := 118140960795 + 1510754 * 2 ^ 59
def prefixEnd_1510754 : Nat := 4983230072969 + 3 ^ 40 * 1510754 * 2
def baseEnd_1510754 : Nat := 775742952702687401727175

theorem tailTrace_1510754 : CollatzResearch.WordTrace tailWord_1510754 prefixEnd_1510754 775742952702687401727175 := by
  unfold tailWord_1510754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775431292200937271646829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36734483445869166057724877 13775431292200937271646829)
  ·
    refine ⟨5165786734575351476867561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13775431292200937271646829 5165786734575351476867561)
    ·
      refine ⟨3874340050931513607650671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5165786734575351476867561 3874340050931513607650671)
      ·
        refine ⟨5811510076397270411476007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874340050931513607650671 5811510076397270411476007)
        ·
          refine ⟨8717265114595905617214011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811510076397270411476007 8717265114595905617214011)
          ·
            refine ⟨13075897671893858425821017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8717265114595905617214011 13075897671893858425821017)
            ·
              refine ⟨9806923253920393819365763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13075897671893858425821017 9806923253920393819365763)
              ·
                refine ⟨14710384880880590729048645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806923253920393819365763 14710384880880590729048645)
                ·
                  refine ⟨2758197165165110761696621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14710384880880590729048645 2758197165165110761696621)
                  ·
                    refine ⟨1034323936936916535636233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758197165165110761696621 1034323936936916535636233)
                    ·
                      refine ⟨775742952702687401727175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034323936936916535636233 775742952702687401727175)
                      ·
                        rfl

theorem cell23_1510754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1510754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510754 prefixEnd_1510754 := by exact prefixLift 1510754
  have htrace : WordTrace (prefixWord ++ tailWord_1510754) baseStart_1510754 baseEnd_1510754 := by
    simpa [prefixWord, tailWord_1510754, baseEnd_1510754] using wordTrace_append hprefix tailTrace_1510754
  have hstable : (prefixWord ++ tailWord_1510754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510754).length < 2 ^ (prefixWord ++ tailWord_1510754).sum := by decide
  have hdescent : baseEnd_1510754 < baseStart_1510754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510777 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_1510777 : Nat := 118140960795 + 1510777 * 2 ^ 59
def prefixEnd_1510777 : Nat := 4983230072969 + 3 ^ 40 * 1510777 * 2
def baseEnd_1510777 : Nat := 258584920919246937246523

theorem tailTrace_1510777 : CollatzResearch.WordTrace tailWord_1510777 prefixEnd_1510777 258584920919246937246523 := by
  unfold tailWord_1510777
  simp only [CollatzResearch.WordTrace]
  refine ⟨55102564047720424014674585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36735042698480282676449723 55102564047720424014674585)
  ·
    refine ⟨41326923035790318011005939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55102564047720424014674585 41326923035790318011005939)
    ·
      refine ⟨61990384553685477016508909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41326923035790318011005939 61990384553685477016508909)
      ·
        refine ⟨23246394207632053881190841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61990384553685477016508909 23246394207632053881190841)
        ·
          refine ⟨17434795655724040410893131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23246394207632053881190841 17434795655724040410893131)
          ·
            refine ⟨26152193483586060616339697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17434795655724040410893131 26152193483586060616339697)
            ·
              refine ⟨19614145112689545462254773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26152193483586060616339697 19614145112689545462254773)
              ·
                refine ⟨1838826104314644887086385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19614145112689545462254773 1838826104314644887086385)
                ·
                  refine ⟨1379119578235983665314789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838826104314644887086385 1379119578235983665314789)
                  ·
                    refine ⟨258584920919246937246523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379119578235983665314789 258584920919246937246523)
                    ·
                      rfl

theorem cell23_1510777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_1510777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510777 prefixEnd_1510777 := by exact prefixLift 1510777
  have htrace : WordTrace (prefixWord ++ tailWord_1510777) baseStart_1510777 baseEnd_1510777 := by
    simpa [prefixWord, tailWord_1510777, baseEnd_1510777] using wordTrace_append hprefix tailTrace_1510777
  have hstable : (prefixWord ++ tailWord_1510777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510777).length < 2 ^ (prefixWord ++ tailWord_1510777).sum := by decide
  have hdescent : baseEnd_1510777 < baseStart_1510777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510780 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_1510780 : Nat := 118140960795 + 1510780 * 2 ^ 59
def prefixEnd_1510780 : Nat := 4983230072969 + 3 ^ 40 * 1510780 * 2
def baseEnd_1510780 : Nat := 775756303199704300002055

theorem tailTrace_1510780 : CollatzResearch.WordTrace tailWord_1510780 prefixEnd_1510780 775756303199704300002055 := by
  unfold tailWord_1510780
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551336733354777763516897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36735115644473037018022529 27551336733354777763516897)
  ·
    refine ⟨20663502550016083322637673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27551336733354777763516897 20663502550016083322637673)
    ·
      refine ⟨15497626912512062491978255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20663502550016083322637673 15497626912512062491978255)
      ·
        refine ⟨23246440368768093737967383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497626912512062491978255 23246440368768093737967383)
        ·
          refine ⟨34869660553152140606951075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23246440368768093737967383 34869660553152140606951075)
          ·
            refine ⟨52304490829728210910426613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34869660553152140606951075 52304490829728210910426613)
            ·
              refine ⟨4903546015287019772852495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52304490829728210910426613 4903546015287019772852495)
              ·
                refine ⟨7355319022930529659278743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903546015287019772852495 7355319022930529659278743)
                ·
                  refine ⟨11032978534395794488918115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355319022930529659278743 11032978534395794488918115)
                  ·
                    refine ⟨16549467801593691733377173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11032978534395794488918115 16549467801593691733377173)
                    ·
                      refine ⟨775756303199704300002055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16549467801593691733377173 775756303199704300002055)
                      ·
                        rfl

theorem cell23_1510780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_1510780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510780 prefixEnd_1510780 := by exact prefixLift 1510780
  have htrace : WordTrace (prefixWord ++ tailWord_1510780) baseStart_1510780 baseEnd_1510780 := by
    simpa [prefixWord, tailWord_1510780, baseEnd_1510780] using wordTrace_append hprefix tailTrace_1510780
  have hstable : (prefixWord ++ tailWord_1510780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510780).length < 2 ^ (prefixWord ++ tailWord_1510780).sum := by decide
  have hdescent : baseEnd_1510780 < baseStart_1510780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510804 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1510804 : Nat := 118140960795 + 1510804 * 2 ^ 59
def prefixEnd_1510804 : Nat := 4983230072969 + 3 ^ 40 * 1510804 * 2
def baseEnd_1510804 : Nat := 775768626735412206101945

theorem tailTrace_1510804 : CollatzResearch.WordTrace tailWord_1510804 prefixEnd_1510804 775768626735412206101945 := by
  unfold tailWord_1510804
  simp only [CollatzResearch.WordTrace]
  refine ⟨27551774409311303812953733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36735699212415071750604977 27551774409311303812953733)
  ·
    refine ⟨5165957701745869464928825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27551774409311303812953733 5165957701745869464928825)
    ·
      refine ⟨3874468276309402098696619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5165957701745869464928825 3874468276309402098696619)
      ·
        refine ⟨5811702414464103148044929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874468276309402098696619 5811702414464103148044929)
        ·
          refine ⟨4358776810848077361033697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811702414464103148044929 4358776810848077361033697)
          ·
            refine ⟨3269082608136058020775273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358776810848077361033697 3269082608136058020775273)
            ·
              refine ⟨2451811956102043515581455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269082608136058020775273 2451811956102043515581455)
              ·
                refine ⟨3677717934153065273372183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451811956102043515581455 3677717934153065273372183)
                ·
                  refine ⟨5516576901229597910058275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677717934153065273372183 5516576901229597910058275)
                  ·
                    refine ⟨8274865351844396865087413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516576901229597910058275 8274865351844396865087413)
                    ·
                      refine ⟨775768626735412206101945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8274865351844396865087413 775768626735412206101945)
                      ·
                        rfl

theorem cell23_1510804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1510804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510804 prefixEnd_1510804 := by exact prefixLift 1510804
  have htrace : WordTrace (prefixWord ++ tailWord_1510804) baseStart_1510804 baseEnd_1510804 := by
    simpa [prefixWord, tailWord_1510804, baseEnd_1510804] using wordTrace_append hprefix tailTrace_1510804
  have hstable : (prefixWord ++ tailWord_1510804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510804).length < 2 ^ (prefixWord ++ tailWord_1510804).sum := by decide
  have hdescent : baseEnd_1510804 < baseStart_1510804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510818 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_1510818 : Nat := 118140960795 + 1510818 * 2 ^ 59
def prefixEnd_1510818 : Nat := 4983230072969 + 3 ^ 40 * 1510818 * 2
def baseEnd_1510818 : Nat := 775775815464575151326881

theorem tailTrace_1510818 : CollatzResearch.WordTrace tailWord_1510818 prefixEnd_1510818 775775815464575151326881 := by
  unfold tailWord_1510818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13776014860142972004229277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36736039627047925344611405 13776014860142972004229277)
  ·
    refine ⟨5166005572553614501585979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13776014860142972004229277 5166005572553614501585979)
    ·
      refine ⟨7749008358830421752378969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5166005572553614501585979 7749008358830421752378969)
      ·
        refine ⟨5811756269122816314284227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7749008358830421752378969 5811756269122816314284227)
        ·
          refine ⟨8717634403684224471426341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811756269122816314284227 8717634403684224471426341)
          ·
            refine ⟨1634556450690792088392439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8717634403684224471426341 1634556450690792088392439)
            ·
              refine ⟨2451834676036188132588659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634556450690792088392439 2451834676036188132588659)
              ·
                refine ⟨3677752014054282198882989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451834676036188132588659 3677752014054282198882989)
                ·
                  refine ⟨1379157005270355824581121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3677752014054282198882989 1379157005270355824581121)
                  ·
                    refine ⟨1034367753952766868435841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1379157005270355824581121 1034367753952766868435841)
                    ·
                      refine ⟨775775815464575151326881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034367753952766868435841 775775815464575151326881)
                      ·
                        rfl

theorem cell23_1510818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_1510818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510818 prefixEnd_1510818 := by exact prefixLift 1510818
  have htrace : WordTrace (prefixWord ++ tailWord_1510818) baseStart_1510818 baseEnd_1510818 := by
    simpa [prefixWord, tailWord_1510818, baseEnd_1510818] using wordTrace_append hprefix tailTrace_1510818
  have hstable : (prefixWord ++ tailWord_1510818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510818).length < 2 ^ (prefixWord ++ tailWord_1510818).sum := by decide
  have hdescent : baseEnd_1510818 < baseStart_1510818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510820 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1510820 : Nat := 118140960795 + 1510820 * 2 ^ 59
def prefixEnd_1510820 : Nat := 4983230072969 + 3 ^ 40 * 1510820 * 2
def baseEnd_1510820 : Nat := 258592280808628047833957

theorem tailTrace_1510820 : CollatzResearch.WordTrace tailWord_1510820 prefixEnd_1510820 258592280808628047833957 := by
  unfold tailWord_1510820
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552066193282321179244957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36736088257709761572326609 27552066193282321179244957)
  ·
    refine ⟨10332024822480870442216859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27552066193282321179244957 10332024822480870442216859)
    ·
      refine ⟨15498037233721305663325289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10332024822480870442216859 15498037233721305663325289)
      ·
        refine ⟨11623527925290979247493967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15498037233721305663325289 11623527925290979247493967)
        ·
          refine ⟨17435291887936468871240951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623527925290979247493967 17435291887936468871240951)
          ·
            refine ⟨26152937831904703306861427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17435291887936468871240951 26152937831904703306861427)
            ·
              refine ⟨39229406747857054960292141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26152937831904703306861427 39229406747857054960292141)
              ·
                refine ⟨14711027530446395610109553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39229406747857054960292141 14711027530446395610109553)
                ·
                  refine ⟨11033270647834796707582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14711027530446395610109553 11033270647834796707582165)
                  ·
                    refine ⟨258592280808628047833957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11033270647834796707582165 258592280808628047833957)
                    ·
                      rfl

theorem cell23_1510820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1510820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510820 prefixEnd_1510820 := by exact prefixLift 1510820
  have htrace : WordTrace (prefixWord ++ tailWord_1510820) baseStart_1510820 baseEnd_1510820 := by
    simpa [prefixWord, tailWord_1510820, baseEnd_1510820] using wordTrace_append hprefix tailTrace_1510820
  have hstable : (prefixWord ++ tailWord_1510820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510820).length < 2 ^ (prefixWord ++ tailWord_1510820).sum := by decide
  have hdescent : baseEnd_1510820 < baseStart_1510820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510824 : List Nat := [2, 1, 6, 1, 2, 1, 2, 8]
def baseStart_1510824 : Nat := 118140960795 + 1510824 * 2 ^ 59
def prefixEnd_1510824 : Nat := 4983230072969 + 3 ^ 40 * 1510824 * 2
def baseEnd_1510824 : Nat := 28732551716611189920439

theorem tailTrace_1510824 : CollatzResearch.WordTrace tailWord_1510824 prefixEnd_1510824 28732551716611189920439 := by
  unfold tailWord_1510824
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552139139275075520817763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36736185519033434027757017 27552139139275075520817763)
  ·
    refine ⟨41328208708912613281226645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27552139139275075520817763 41328208708912613281226645)
    ·
      refine ⟨1937259783230278747557499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41328208708912613281226645 1937259783230278747557499)
      ·
        refine ⟨2905889674845418121336249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937259783230278747557499 2905889674845418121336249)
        ·
          refine ⟨2179417256134063591002187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2905889674845418121336249 2179417256134063591002187)
          ·
            refine ⟨3269125884201095386503281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179417256134063591002187 3269125884201095386503281)
            ·
              refine ⟨2451844413150821539877461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269125884201095386503281 2451844413150821539877461)
              ·
                refine ⟨28732551716611189920439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2451844413150821539877461 28732551716611189920439)
                ·
                  rfl

theorem cell23_1510824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 8].length) (baseStart_1510824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510824 prefixEnd_1510824 := by exact prefixLift 1510824
  have htrace : WordTrace (prefixWord ++ tailWord_1510824) baseStart_1510824 baseEnd_1510824 := by
    simpa [prefixWord, tailWord_1510824, baseEnd_1510824] using wordTrace_append hprefix tailTrace_1510824
  have hstable : (prefixWord ++ tailWord_1510824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510824).length < 2 ^ (prefixWord ++ tailWord_1510824).sum := by decide
  have hdescent : baseEnd_1510824 < baseStart_1510824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510868 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1510868 : Nat := 118140960795 + 1510868 * 2 ^ 59
def prefixEnd_1510868 : Nat := 4983230072969 + 3 ^ 40 * 1510868 * 2
def baseEnd_1510868 : Nat := 775801489497299955701651

theorem tailTrace_1510868 : CollatzResearch.WordTrace tailWord_1510868 prefixEnd_1510868 775801489497299955701651 := by
  unfold tailWord_1510868
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552941545195373278118629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36737255393593831037491505 27552941545195373278118629)
  ·
    refine ⟨5166176539724132489647243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27552941545195373278118629 5166176539724132489647243)
    ·
      refine ⟨7749264809586198734470865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5166176539724132489647243 7749264809586198734470865)
      ·
        refine ⟨5811948607189649050853149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7749264809586198734470865 5811948607189649050853149)
        ·
          refine ⟨2179480727696118394069931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5811948607189649050853149 2179480727696118394069931)
          ·
            refine ⟨3269221091544177591104897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179480727696118394069931 3269221091544177591104897)
            ·
              refine ⟨2451915818658133193328673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3269221091544177591104897 2451915818658133193328673)
              ·
                refine ⟨1838936863993599894996505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451915818658133193328673 1838936863993599894996505)
                ·
                  refine ⟨1379202647995199921247379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838936863993599894996505 1379202647995199921247379)
                  ·
                    refine ⟨2068803971992799881871069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379202647995199921247379 2068803971992799881871069)
                    ·
                      refine ⟨775801489497299955701651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2068803971992799881871069 775801489497299955701651)
                      ·
                        rfl

theorem cell23_1510868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1510868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510868 prefixEnd_1510868 := by exact prefixLift 1510868
  have htrace : WordTrace (prefixWord ++ tailWord_1510868) baseStart_1510868 baseEnd_1510868 := by
    simpa [prefixWord, tailWord_1510868, baseEnd_1510868] using wordTrace_append hprefix tailTrace_1510868
  have hstable : (prefixWord ++ tailWord_1510868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510868).length < 2 ^ (prefixWord ++ tailWord_1510868).sum := by decide
  have hdescent : baseEnd_1510868 < baseStart_1510868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510887 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1510887 : Nat := 118140960795 + 1510887 * 2 ^ 59
def prefixEnd_1510887 : Nat := 4983230072969 + 3 ^ 40 * 1510887 * 2
def baseEnd_1510887 : Nat := 775811245629735381364063

theorem tailTrace_1510887 : CollatzResearch.WordTrace tailWord_1510887 prefixEnd_1510887 775811245629735381364063 := by
  unfold tailWord_1510887
  simp only [CollatzResearch.WordTrace]
  refine ⟨55106576077321912801178915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36737717384881275200785943 55106576077321912801178915)
  ·
    refine ⟨82659864115982869201768373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55106576077321912801178915 82659864115982869201768373)
    ·
      refine ⟨7749362260873393987665785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82659864115982869201768373 7749362260873393987665785)
      ·
        refine ⟨5812021695655045490749339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7749362260873393987665785 5812021695655045490749339)
        ·
          refine ⟨8718032543482568236124009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812021695655045490749339 8718032543482568236124009)
          ·
            refine ⟨6538524407611926177093007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8718032543482568236124009 6538524407611926177093007)
            ·
              refine ⟨9807786611417889265639511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538524407611926177093007 9807786611417889265639511)
              ·
                refine ⟨14711679917126833898459267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807786611417889265639511 14711679917126833898459267)
                ·
                  refine ⟨22067519875690250847688901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14711679917126833898459267 22067519875690250847688901)
                  ·
                    refine ⟨4137659976691922033941669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22067519875690250847688901 4137659976691922033941669)
                    ·
                      refine ⟨775811245629735381364063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4137659976691922033941669 775811245629735381364063)
                      ·
                        rfl

theorem cell23_1510887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1510887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510887 prefixEnd_1510887 := by exact prefixLift 1510887
  have htrace : WordTrace (prefixWord ++ tailWord_1510887) baseStart_1510887 baseEnd_1510887 := by
    simpa [prefixWord, tailWord_1510887, baseEnd_1510887] using wordTrace_append hprefix tailTrace_1510887
  have hstable : (prefixWord ++ tailWord_1510887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510887).length < 2 ^ (prefixWord ++ tailWord_1510887).sum := by decide
  have hdescent : baseEnd_1510887 < baseStart_1510887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510897 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 7]
def baseStart_1510897 : Nat := 118140960795 + 1510897 * 2 ^ 59
def prefixEnd_1510897 : Nat := 4983230072969 + 3 ^ 40 * 1510897 * 2
def baseEnd_1510897 : Nat := 86201820048475593582113

theorem tailTrace_1510897 : CollatzResearch.WordTrace tailWord_1510897 prefixEnd_1510897 86201820048475593582113 := by
  unfold tailWord_1510897
  simp only [CollatzResearch.WordTrace]
  refine ⟨55106940807285684509042945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36737960538190456339361963 55106940807285684509042945)
  ·
    refine ⟨41330205605464263381782209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55106940807285684509042945 41330205605464263381782209)
    ·
      refine ⟨30997654204098197536336657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41330205605464263381782209 30997654204098197536336657)
      ·
        refine ⟨23248240653073648152252493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30997654204098197536336657 23248240653073648152252493)
        ·
          refine ⟨8718090244902618057094685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23248240653073648152252493 8718090244902618057094685)
          ·
            refine ⟨3269283841838481771410507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8718090244902618057094685 3269283841838481771410507)
            ·
              refine ⟨4903925762757722657115761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269283841838481771410507 4903925762757722657115761)
              ·
                refine ⟨3677944322068291992836821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903925762757722657115761 3677944322068291992836821)
                ·
                  refine ⟨86201820048475593582113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3677944322068291992836821 86201820048475593582113)
                  ·
                    rfl

theorem cell23_1510897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_1510897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510897 prefixEnd_1510897 := by exact prefixLift 1510897
  have htrace : WordTrace (prefixWord ++ tailWord_1510897) baseStart_1510897 baseEnd_1510897 := by
    simpa [prefixWord, tailWord_1510897, baseEnd_1510897] using wordTrace_append hprefix tailTrace_1510897
  have hstable : (prefixWord ++ tailWord_1510897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510897).length < 2 ^ (prefixWord ++ tailWord_1510897).sum := by decide
  have hdescent : baseEnd_1510897 < baseStart_1510897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510987 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 6]
def baseStart_1510987 : Nat := 118140960795 + 1510987 * 2 ^ 59
def prefixEnd_1510987 : Nat := 4983230072969 + 3 ^ 40 * 1510987 * 2
def baseEnd_1510987 : Nat := 86206954855020554457067

theorem tailTrace_1510987 : CollatzResearch.WordTrace tailWord_1510987 prefixEnd_1510987 86206954855020554457067 := by
  unfold tailWord_1510987
  simp only [CollatzResearch.WordTrace]
  refine ⟨55110223376959629879819215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36740148917973086586546143 55110223376959629879819215)
  ·
    refine ⟨82665335065439444819728823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55110223376959629879819215 82665335065439444819728823)
    ·
      refine ⟨123998002598159167229593235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82665335065439444819728823 123998002598159167229593235)
      ·
        refine ⟨185997003897238750844389853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123998002598159167229593235 185997003897238750844389853)
        ·
          refine ⟨69748876461464531566646195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185997003897238750844389853 69748876461464531566646195)
          ·
            refine ⟨104623314692196797349969293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69748876461464531566646195 104623314692196797349969293)
            ·
              refine ⟨39233743009573799006238485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104623314692196797349969293 39233743009573799006238485)
              ·
                refine ⟨1839081703573771828417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39233743009573799006238485 1839081703573771828417429)
                ·
                  refine ⟨86206954855020554457067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1839081703573771828417429 86206954855020554457067)
                  ·
                    rfl

theorem cell23_1510987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 6].length) (baseStart_1510987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1510987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1510987 prefixEnd_1510987 := by exact prefixLift 1510987
  have htrace : WordTrace (prefixWord ++ tailWord_1510987) baseStart_1510987 baseEnd_1510987 := by
    simpa [prefixWord, tailWord_1510987, baseEnd_1510987] using wordTrace_append hprefix tailTrace_1510987
  have hstable : (prefixWord ++ tailWord_1510987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510987).length < 2 ^ (prefixWord ++ tailWord_1510987).sum := by decide
  have hdescent : baseEnd_1510987 < baseStart_1510987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511064 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_1511064 : Nat := 118140960795 + 1511064 * 2 ^ 59
def prefixEnd_1511064 : Nat := 4983230072969 + 3 ^ 40 * 1511064 * 2
def baseEnd_1511064 : Nat := 258634043901860396283583

theorem tailTrace_1511064 : CollatzResearch.WordTrace tailWord_1511064 prefixEnd_1511064 258634043901860396283583 := by
  unfold tailWord_1511064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27556515898840336015186123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36742021198453781353581497 27556515898840336015186123)
  ·
    refine ⟨41334773848260504022779185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27556515898840336015186123 41334773848260504022779185)
    ·
      refine ⟨31001080386195378017084389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41334773848260504022779185 31001080386195378017084389)
      ·
        refine ⟨5812702572411633378203323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31001080386195378017084389 5812702572411633378203323)
        ·
          refine ⟨8719053858617450067304985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812702572411633378203323 8719053858617450067304985)
          ·
            refine ⟨6539290393963087550478739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8719053858617450067304985 6539290393963087550478739)
            ·
              refine ⟨9808935590944631325718109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539290393963087550478739 9808935590944631325718109)
              ·
                refine ⟨3678350846604236747144291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9808935590944631325718109 3678350846604236747144291)
                ·
                  refine ⟨5517526269906355120716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678350846604236747144291 5517526269906355120716437)
                  ·
                    refine ⟨258634043901860396283583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5517526269906355120716437 258634043901860396283583)
                    ·
                      rfl

theorem cell23_1511064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_1511064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511064 prefixEnd_1511064 := by exact prefixLift 1511064
  have htrace : WordTrace (prefixWord ++ tailWord_1511064) baseStart_1511064 baseEnd_1511064 := by
    simpa [prefixWord, tailWord_1511064, baseEnd_1511064] using wordTrace_append hprefix tailTrace_1511064
  have hstable : (prefixWord ++ tailWord_1511064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511064).length < 2 ^ (prefixWord ++ tailWord_1511064).sum := by decide
  have hdescent : baseEnd_1511064 < baseStart_1511064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511067 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_1511067 : Nat := 118140960795 + 1511067 * 2 ^ 59
def prefixEnd_1511067 : Nat := 4983230072969 + 3 ^ 40 * 1511067 * 2
def baseEnd_1511067 : Nat := 775903672147544677113235

theorem tailTrace_1511067 : CollatzResearch.WordTrace tailWord_1511067 prefixEnd_1511067 775903672147544677113235 := by
  unfold tailWord_1511067
  simp only [CollatzResearch.WordTrace]
  refine ⟨55113141216669803542731455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36742094144446535695154303 55113141216669803542731455)
  ·
    refine ⟨82669711825004705314097183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55113141216669803542731455 82669711825004705314097183)
    ·
      refine ⟨124004567737507057971145775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82669711825004705314097183 124004567737507057971145775)
      ·
        refine ⟨186006851606260586956718663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124004567737507057971145775 186006851606260586956718663)
        ·
          refine ⟨279010277409390880435077995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186006851606260586956718663 279010277409390880435077995)
          ·
            refine ⟨418515416114086320652616993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279010277409390880435077995 418515416114086320652616993)
            ·
              refine ⟨313886562085564740489462745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418515416114086320652616993 313886562085564740489462745)
              ·
                refine ⟨235414921564173555367097059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313886562085564740489462745 235414921564173555367097059)
                ·
                  refine ⟨353122382346260333050645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235414921564173555367097059 353122382346260333050645589)
                  ·
                    refine ⟨4138152918120238277937253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 353122382346260333050645589 4138152918120238277937253)
                    ·
                      refine ⟨775903672147544677113235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4138152918120238277937253 775903672147544677113235)
                      ·
                        rfl

theorem cell23_1511067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_1511067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511067 prefixEnd_1511067 := by exact prefixLift 1511067
  have htrace : WordTrace (prefixWord ++ tailWord_1511067) baseStart_1511067 baseEnd_1511067 := by
    simpa [prefixWord, tailWord_1511067, baseEnd_1511067] using wordTrace_append hprefix tailTrace_1511067
  have hstable : (prefixWord ++ tailWord_1511067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511067).length < 2 ^ (prefixWord ++ tailWord_1511067).sum := by decide
  have hdescent : baseEnd_1511067 < baseStart_1511067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511077 : List Nat := [1, 3, 1, 2, 1, 2, 2, 11]
def baseStart_1511077 : Nat := 118140960795 + 1511077 * 2 ^ 59
def prefixEnd_1511077 : Nat := 4983230072969 + 3 ^ 40 * 1511077 * 2
def baseEnd_1511077 : Nat := 28737363220521838444007

theorem tailTrace_1511077 : CollatzResearch.WordTrace tailWord_1511077 prefixEnd_1511077 28737363220521838444007 := by
  unfold tailWord_1511077
  simp only [CollatzResearch.WordTrace]
  refine ⟨55113505946633575250595485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36742337297755716833730323 55113505946633575250595485)
  ·
    refine ⟨20667564729987590718973307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55113505946633575250595485 20667564729987590718973307)
    ·
      refine ⟨31001347094981386078459961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20667564729987590718973307 31001347094981386078459961)
      ·
        refine ⟨23251010321236039558844971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31001347094981386078459961 23251010321236039558844971)
        ·
          refine ⟨34876515481854059338267457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23251010321236039558844971 34876515481854059338267457)
          ·
            refine ⟨26157386611390544503700593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34876515481854059338267457 26157386611390544503700593)
            ·
              refine ⟨19618039958542908377775445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26157386611390544503700593 19618039958542908377775445)
              ·
                refine ⟨28737363220521838444007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 19618039958542908377775445 28737363220521838444007)
                ·
                  rfl

theorem cell23_1511077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 11].length) (baseStart_1511077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511077 prefixEnd_1511077 := by exact prefixLift 1511077
  have htrace : WordTrace (prefixWord ++ tailWord_1511077) baseStart_1511077 baseEnd_1511077 := by
    simpa [prefixWord, tailWord_1511077, baseEnd_1511077] using wordTrace_append hprefix tailTrace_1511077
  have hstable : (prefixWord ++ tailWord_1511077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511077).length < 2 ^ (prefixWord ++ tailWord_1511077).sum := by decide
  have hdescent : baseEnd_1511077 < baseStart_1511077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511091 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 3]
def baseStart_1511091 : Nat := 118140960795 + 1511091 * 2 ^ 59
def prefixEnd_1511091 : Nat := 4983230072969 + 3 ^ 40 * 1511091 * 2
def baseEnd_1511091 : Nat := 775915995683252583213125

theorem tailTrace_1511091 : CollatzResearch.WordTrace tailWord_1511091 prefixEnd_1511091 775915995683252583213125 := by
  unfold tailWord_1511091
  simp only [CollatzResearch.WordTrace]
  refine ⟨55114016568582855641605127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36742677712388570427736751 55114016568582855641605127)
  ·
    refine ⟨82671024852874283462407691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55114016568582855641605127 82671024852874283462407691)
    ·
      refine ⟨124006537279311425193611537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82671024852874283462407691 124006537279311425193611537)
      ·
        refine ⟨93004902959483568895208653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124006537279311425193611537 93004902959483568895208653)
        ·
          refine ⟨34876838609806338335703245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93004902959483568895208653 34876838609806338335703245)
          ·
            refine ⟨13078814478677376875888717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34876838609806338335703245 13078814478677376875888717)
            ·
              refine ⟨4904555429504016328458269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13078814478677376875888717 4904555429504016328458269)
              ·
                refine ⟨1839208286064006123171851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904555429504016328458269 1839208286064006123171851)
                ·
                  refine ⟨2758812429096009184757777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839208286064006123171851 2758812429096009184757777)
                  ·
                    refine ⟨2069109321822006888568333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2758812429096009184757777 2069109321822006888568333)
                    ·
                      refine ⟨775915995683252583213125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069109321822006888568333 775915995683252583213125)
                      ·
                        rfl

theorem cell23_1511091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_1511091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511091 prefixEnd_1511091 := by exact prefixLift 1511091
  have htrace : WordTrace (prefixWord ++ tailWord_1511091) baseStart_1511091 baseEnd_1511091 := by
    simpa [prefixWord, tailWord_1511091, baseEnd_1511091] using wordTrace_append hprefix tailTrace_1511091
  have hstable : (prefixWord ++ tailWord_1511091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511091).length < 2 ^ (prefixWord ++ tailWord_1511091).sum := by decide
  have hdescent : baseEnd_1511091 < baseStart_1511091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511098 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_1511098 : Nat := 118140960795 + 1511098 * 2 ^ 59
def prefixEnd_1511098 : Nat := 4983230072969 + 3 ^ 40 * 1511098 * 2
def baseEnd_1511098 : Nat := 258639863349278018608531

theorem tailTrace_1511098 : CollatzResearch.WordTrace tailWord_1511098 prefixEnd_1511098 258639863349278018608531 := by
  unfold tailWord_1511098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13778567969889373959277487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36742847919704997224739965 13778567969889373959277487)
  ·
    refine ⟨20667851954834060938916231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13778567969889373959277487 20667851954834060938916231)
    ·
      refine ⟨31001777932251091408374347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20667851954834060938916231 31001777932251091408374347)
      ·
        refine ⟨46502666898376637112561521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31001777932251091408374347 46502666898376637112561521)
        ·
          refine ⟨34877000173782477834421141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46502666898376637112561521 34877000173782477834421141)
          ·
            refine ⟨1634859383146053648488491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34877000173782477834421141 1634859383146053648488491)
            ·
              refine ⟨2452289074719080472732737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634859383146053648488491 2452289074719080472732737)
              ·
                refine ⟨1839216806039310354549553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2452289074719080472732737 1839216806039310354549553)
                ·
                  refine ⟨1379412604529482765912165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1839216806039310354549553 1379412604529482765912165)
                  ·
                    refine ⟨258639863349278018608531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379412604529482765912165 258639863349278018608531)
                    ·
                      rfl

theorem cell23_1511098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_1511098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511098 prefixEnd_1511098 := by exact prefixLift 1511098
  have htrace : WordTrace (prefixWord ++ tailWord_1511098) baseStart_1511098 baseEnd_1511098 := by
    simpa [prefixWord, tailWord_1511098, baseEnd_1511098] using wordTrace_append hprefix tailTrace_1511098
  have hstable : (prefixWord ++ tailWord_1511098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511098).length < 2 ^ (prefixWord ++ tailWord_1511098).sum := by decide
  have hdescent : baseEnd_1511098 < baseStart_1511098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511121 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_1511121 : Nat := 118140960795 + 1511121 * 2 ^ 59
def prefixEnd_1511121 : Nat := 4983230072969 + 3 ^ 40 * 1511121 * 2
def baseEnd_1511121 : Nat := 775931400102887465837987

theorem tailTrace_1511121 : CollatzResearch.WordTrace tailWord_1511121 prefixEnd_1511121 775931400102887465837987 := by
  unfold tailWord_1511121
  simp only [CollatzResearch.WordTrace]
  refine ⟨55115110758474170765197217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36743407172316113843464811 55115110758474170765197217)
  ·
    refine ⟨41336333068855628073897913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55115110758474170765197217 41336333068855628073897913)
    ·
      refine ⟨31002249801641721055423435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41336333068855628073897913 31002249801641721055423435)
      ·
        refine ⟨46503374702462581583135153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31002249801641721055423435 46503374702462581583135153)
        ·
          refine ⟨34877531026846936187351365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46503374702462581583135153 34877531026846936187351365)
          ·
            refine ⟨6539537067533800535128381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34877531026846936187351365 6539537067533800535128381)
            ·
              refine ⟨2452326400325175200673143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6539537067533800535128381 2452326400325175200673143)
              ·
                refine ⟨3678489600487762801009715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452326400325175200673143 3678489600487762801009715)
                ·
                  refine ⟨5517734400731644201514573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678489600487762801009715 5517734400731644201514573)
                  ·
                    refine ⟨2069150400274366575567965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5517734400731644201514573 2069150400274366575567965)
                    ·
                      refine ⟨775931400102887465837987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069150400274366575567965 775931400102887465837987)
                      ·
                        rfl

theorem cell23_1511121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_1511121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511121 prefixEnd_1511121 := by exact prefixLift 1511121
  have htrace : WordTrace (prefixWord ++ tailWord_1511121) baseStart_1511121 baseEnd_1511121 := by
    simpa [prefixWord, tailWord_1511121, baseEnd_1511121] using wordTrace_append hprefix tailTrace_1511121
  have hstable : (prefixWord ++ tailWord_1511121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511121).length < 2 ^ (prefixWord ++ tailWord_1511121).sum := by decide
  have hdescent : baseEnd_1511121 < baseStart_1511121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511139 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1511139 : Nat := 118140960795 + 1511139 * 2 ^ 59
def prefixEnd_1511139 : Nat := 4983230072969 + 3 ^ 40 * 1511139 * 2
def baseEnd_1511139 : Nat := 775940642754668395412905

theorem tailTrace_1511139 : CollatzResearch.WordTrace tailWord_1511139 prefixEnd_1511139 775940642754668395412905 := by
  unfold tailWord_1511139
  simp only [CollatzResearch.WordTrace]
  refine ⟨55115767272408959839352471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36743844848272639892901647 55115767272408959839352471)
  ·
    refine ⟨82673650908613439759028707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55115767272408959839352471 82673650908613439759028707)
    ·
      refine ⟨124010476362920159638543061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82673650908613439759028707 124010476362920159638543061)
      ·
        refine ⟨2906495539755941241528353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 124010476362920159638543061 2906495539755941241528353)
        ·
          refine ⟨2179871654816955931146265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2906495539755941241528353 2179871654816955931146265)
          ·
            refine ⟨1634903741112716948359699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179871654816955931146265 1634903741112716948359699)
            ·
              refine ⟨2452355611669075422539549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634903741112716948359699 2452355611669075422539549)
              ·
                refine ⟨919633354375903283452331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2452355611669075422539549 919633354375903283452331)
                ·
                  refine ⟨1379450031563854925178497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919633354375903283452331 1379450031563854925178497)
                  ·
                    refine ⟨1034587523672891193883873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1379450031563854925178497 1034587523672891193883873)
                    ·
                      refine ⟨775940642754668395412905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034587523672891193883873 775940642754668395412905)
                      ·
                        rfl

theorem cell23_1511139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1511139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511139 prefixEnd_1511139 := by exact prefixLift 1511139
  have htrace : WordTrace (prefixWord ++ tailWord_1511139) baseStart_1511139 baseEnd_1511139 := by
    simpa [prefixWord, tailWord_1511139, baseEnd_1511139] using wordTrace_append hprefix tailTrace_1511139
  have hstable : (prefixWord ++ tailWord_1511139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511139).length < 2 ^ (prefixWord ++ tailWord_1511139).sum := by decide
  have hdescent : baseEnd_1511139 < baseStart_1511139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511148 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_1511148 : Nat := 118140960795 + 1511148 * 2 ^ 59
def prefixEnd_1511148 : Nat := 4983230072969 + 3 ^ 40 * 1511148 * 2
def baseEnd_1511148 : Nat := 775945264080558860200363

theorem tailTrace_1511148 : CollatzResearch.WordTrace tailWord_1511148 prefixEnd_1511148 775945264080558860200363 := by
  unfold tailWord_1511148
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558047764688177188215049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36744063686250902917620065 27558047764688177188215049)
  ·
    refine ⟨20668535823516132891161287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27558047764688177188215049 20668535823516132891161287)
    ·
      refine ⟨31002803735274199336741931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20668535823516132891161287 31002803735274199336741931)
      ·
        refine ⟨46504205602911299005112897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31002803735274199336741931 46504205602911299005112897)
        ·
          refine ⟨34878154202183474253834673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46504205602911299005112897 34878154202183474253834673)
          ·
            refine ⟨26158615651637605690376005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34878154202183474253834673 26158615651637605690376005)
            ·
              refine ⟨4904740434682051066945501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26158615651637605690376005 4904740434682051066945501)
              ·
                refine ⟨1839277663005769150104563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4904740434682051066945501 1839277663005769150104563)
                ·
                  refine ⟨2758916494508653725156845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839277663005769150104563 2758916494508653725156845)
                  ·
                    refine ⟨1034593685440745146933817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2758916494508653725156845 1034593685440745146933817)
                    ·
                      refine ⟨775945264080558860200363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034593685440745146933817 775945264080558860200363)
                      ·
                        rfl

theorem cell23_1511148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_1511148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511148 prefixEnd_1511148 := by exact prefixLift 1511148
  have htrace : WordTrace (prefixWord ++ tailWord_1511148) baseStart_1511148 baseEnd_1511148 := by
    simpa [prefixWord, tailWord_1511148, baseEnd_1511148] using wordTrace_append hprefix tailTrace_1511148
  have hstable : (prefixWord ++ tailWord_1511148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511148).length < 2 ^ (prefixWord ++ tailWord_1511148).sum := by decide
  have hdescent : baseEnd_1511148 < baseStart_1511148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511164 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_1511164 : Nat := 118140960795 + 1511164 * 2 ^ 59
def prefixEnd_1511164 : Nat := 4983230072969 + 3 ^ 40 * 1511164 * 2
def baseEnd_1511164 : Nat := 775953479771030797600289

theorem tailTrace_1511164 : CollatzResearch.WordTrace tailWord_1511164 prefixEnd_1511164 775953479771030797600289 := by
  unfold tailWord_1511164
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558339548659194554506273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36744452731545592739341697 27558339548659194554506273)
  ·
    refine ⟨20668754661494395915879705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27558339548659194554506273 20668754661494395915879705)
    ·
      refine ⟨15501565996120796936909779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20668754661494395915879705 15501565996120796936909779)
      ·
        refine ⟨23252348994181195405364669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15501565996120796936909779 23252348994181195405364669)
        ·
          refine ⟨8719630872817948277011751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23252348994181195405364669 8719630872817948277011751)
          ·
            refine ⟨13079446309226922415517627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8719630872817948277011751 13079446309226922415517627)
            ·
              refine ⟨19619169463840383623276441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13079446309226922415517627 19619169463840383623276441)
              ·
                refine ⟨14714377097880287717457331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19619169463840383623276441 14714377097880287717457331)
                ·
                  refine ⟨22071565646820431576185997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14714377097880287717457331 22071565646820431576185997)
                  ·
                    refine ⟨8276837117557661841069749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22071565646820431576185997 8276837117557661841069749)
                    ·
                      refine ⟨775953479771030797600289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8276837117557661841069749 775953479771030797600289)
                      ·
                        rfl

theorem cell23_1511164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_1511164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511164 prefixEnd_1511164 := by exact prefixLift 1511164
  have htrace : WordTrace (prefixWord ++ tailWord_1511164) baseStart_1511164 baseEnd_1511164 := by
    simpa [prefixWord, tailWord_1511164, baseEnd_1511164] using wordTrace_append hprefix tailTrace_1511164
  have hstable : (prefixWord ++ tailWord_1511164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511164).length < 2 ^ (prefixWord ++ tailWord_1511164).sum := by decide
  have hdescent : baseEnd_1511164 < baseStart_1511164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511172 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_1511172 : Nat := 118140960795 + 1511172 * 2 ^ 59
def prefixEnd_1511172 : Nat := 4983230072969 + 3 ^ 40 * 1511172 * 2
def baseEnd_1511172 : Nat := 775957587616266766300253

theorem tailTrace_1511172 : CollatzResearch.WordTrace tailWord_1511172 prefixEnd_1511172 775957587616266766300253 := by
  unfold tailWord_1511172
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558485440644703237651885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36744647254192937650202513 27558485440644703237651885)
  ·
    refine ⟨10334432040241763714119457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27558485440644703237651885 10334432040241763714119457)
    ·
      refine ⟨7750824030181322785589593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10334432040241763714119457 7750824030181322785589593)
      ·
        refine ⟨5813118022635992089192195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7750824030181322785589593 5813118022635992089192195)
        ·
          refine ⟨8719677033953988133788293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5813118022635992089192195 8719677033953988133788293)
          ·
            refine ⟨1634939443866372775085305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8719677033953988133788293 1634939443866372775085305)
            ·
              refine ⟨1226204582899779581313979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634939443866372775085305 1226204582899779581313979)
              ·
                refine ⟨1839306874349669371970969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226204582899779581313979 1839306874349669371970969)
                ·
                  refine ⟨1379480155762252028978227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1839306874349669371970969 1379480155762252028978227)
                  ·
                    refine ⟨2069220233643378043467341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379480155762252028978227 2069220233643378043467341)
                    ·
                      refine ⟨775957587616266766300253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069220233643378043467341 775957587616266766300253)
                      ·
                        rfl

theorem cell23_1511172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_1511172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511172 prefixEnd_1511172 := by exact prefixLift 1511172
  have htrace : WordTrace (prefixWord ++ tailWord_1511172) baseStart_1511172 baseEnd_1511172 := by
    simpa [prefixWord, tailWord_1511172, baseEnd_1511172] using wordTrace_append hprefix tailTrace_1511172
  have hstable : (prefixWord ++ tailWord_1511172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511172).length < 2 ^ (prefixWord ++ tailWord_1511172).sum := by decide
  have hdescent : baseEnd_1511172 < baseStart_1511172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511218 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_1511218 : Nat := 118140960795 + 1511218 * 2 ^ 59
def prefixEnd_1511218 : Nat := 4983230072969 + 3 ^ 40 * 1511218 * 2
def baseEnd_1511218 : Nat := 86220134191819287369449

theorem tailTrace_1511218 : CollatzResearch.WordTrace tailWord_1511218 prefixEnd_1511218 86220134191819287369449 := by
  unfold tailWord_1511218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13779662159780689082869577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36745765759415170887652205 13779662159780689082869577)
  ·
    refine ⟨10334746619835516812152183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13779662159780689082869577 10334746619835516812152183)
    ·
      refine ⟨15502119929753275218228275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334746619835516812152183 15502119929753275218228275)
      ·
        refine ⟨23253179894629912827342413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15502119929753275218228275 23253179894629912827342413)
        ·
          refine ⟨8719942460486217310253405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23253179894629912827342413 8719942460486217310253405)
          ·
            refine ⟨3269978422682331491345027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8719942460486217310253405 3269978422682331491345027)
            ·
              refine ⟨4904967634023497237017541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269978422682331491345027 4904967634023497237017541)
              ·
                refine ⟨919681431379405731940789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4904967634023497237017541 919681431379405731940789)
                ·
                  refine ⟨86220134191819287369449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 919681431379405731940789 86220134191819287369449)
                  ·
                    rfl

theorem cell23_1511218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_1511218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511218 prefixEnd_1511218 := by exact prefixLift 1511218
  have htrace : WordTrace (prefixWord ++ tailWord_1511218) baseStart_1511218 baseEnd_1511218 := by
    simpa [prefixWord, tailWord_1511218, baseEnd_1511218] using wordTrace_append hprefix tailTrace_1511218
  have hstable : (prefixWord ++ tailWord_1511218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511218).length < 2 ^ (prefixWord ++ tailWord_1511218).sum := by decide
  have hdescent : baseEnd_1511218 < baseStart_1511218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511301 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_1511301 : Nat := 118140960795 + 1511301 * 2 ^ 59
def prefixEnd_1511301 : Nat := 4983230072969 + 3 ^ 40 * 1511301 * 2
def baseEnd_1511301 : Nat := 776023826620696761587159

theorem tailTrace_1511301 : CollatzResearch.WordTrace tailWord_1511301 prefixEnd_1511301 776023826620696761587159 := by
  unfold tailWord_1511301
  simp only [CollatzResearch.WordTrace]
  refine ⟨55121675897822061506749757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36747783931881374337833171 55121675897822061506749757)
  ·
    refine ⟨20670628461683273065031159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55121675897822061506749757 20670628461683273065031159)
    ·
      refine ⟨31005942692524909597546739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20670628461683273065031159 31005942692524909597546739)
      ·
        refine ⟨46508914038787364396320109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31005942692524909597546739 46508914038787364396320109)
        ·
          refine ⟨17440842764545261648620041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46508914038787364396320109 17440842764545261648620041)
          ·
            refine ⟨13080632073408946236465031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17440842764545261648620041 13080632073408946236465031)
            ·
              refine ⟨19620948110113419354697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13080632073408946236465031 19620948110113419354697547)
              ·
                refine ⟨29431422165170129032046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19620948110113419354697547 29431422165170129032046321)
                ·
                  refine ⟨22073566623877596774034741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29431422165170129032046321 22073566623877596774034741)
                  ·
                    refine ⟨2069396870988524697565757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22073566623877596774034741 2069396870988524697565757)
                    ·
                      refine ⟨776023826620696761587159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069396870988524697565757 776023826620696761587159)
                      ·
                        rfl

theorem cell23_1511301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_1511301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511301 prefixEnd_1511301 := by exact prefixLift 1511301
  have htrace : WordTrace (prefixWord ++ tailWord_1511301) baseStart_1511301 baseEnd_1511301 := by
    simpa [prefixWord, tailWord_1511301, baseEnd_1511301] using wordTrace_append hprefix tailTrace_1511301
  have hstable : (prefixWord ++ tailWord_1511301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511301).length < 2 ^ (prefixWord ++ tailWord_1511301).sum := by decide
  have hdescent : baseEnd_1511301 < baseStart_1511301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511329 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 1, 4]
def baseStart_1511329 : Nat := 118140960795 + 1511329 * 2 ^ 59
def prefixEnd_1511329 : Nat := 4983230072969 + 3 ^ 40 * 1511329 * 2
def baseEnd_1511329 : Nat := 258679401359674217345677

theorem tailTrace_1511329 : CollatzResearch.WordTrace tailWord_1511329 prefixEnd_1511329 258679401359674217345677 := by
  unfold tailWord_1511329
  simp only [CollatzResearch.WordTrace]
  refine ⟨55122697141720622288769041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36748464761147081525846027 55122697141720622288769041)
  ·
    refine ⟨41342022856290466716576781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55122697141720622288769041 41342022856290466716576781)
    ·
      refine ⟨15503258571108925018716293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41342022856290466716576781 15503258571108925018716293)
      ·
        refine ⟨2906860982082923441009305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15503258571108925018716293 2906860982082923441009305)
        ·
          refine ⟨2180145736562192580756979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2906860982082923441009305 2180145736562192580756979)
          ·
            refine ⟨3270218604843288871135469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180145736562192580756979 3270218604843288871135469)
            ·
              refine ⟨1226331976816233326675801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3270218604843288871135469 1226331976816233326675801)
              ·
                refine ⟨919748982612174995006851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226331976816233326675801 919748982612174995006851)
                ·
                  refine ⟨1379623473918262492510277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919748982612174995006851 1379623473918262492510277)
                  ·
                    refine ⟨258679401359674217345677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379623473918262492510277 258679401359674217345677)
                    ·
                      rfl

theorem cell23_1511329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_1511329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511329 prefixEnd_1511329 := by exact prefixLift 1511329
  have htrace : WordTrace (prefixWord ++ tailWord_1511329) baseStart_1511329 baseEnd_1511329 := by
    simpa [prefixWord, tailWord_1511329, baseEnd_1511329] using wordTrace_append hprefix tailTrace_1511329
  have hstable : (prefixWord ++ tailWord_1511329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511329).length < 2 ^ (prefixWord ++ tailWord_1511329).sum := by decide
  have hdescent : baseEnd_1511329 < baseStart_1511329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511351 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 1, 6]
def baseStart_1511351 : Nat := 118140960795 + 1511351 * 2 ^ 59
def prefixEnd_1511351 : Nat := 4983230072969 + 3 ^ 40 * 1511351 * 2
def baseEnd_1511351 : Nat := 258683166884473855320643

theorem tailTrace_1511351 : CollatzResearch.WordTrace tailWord_1511351 prefixEnd_1511351 258683166884473855320643 := by
  unfold tailWord_1511351
  simp only [CollatzResearch.WordTrace]
  refine ⟨55123499547640920046069907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36748999698427280030713271 55123499547640920046069907)
  ·
    refine ⟨82685249321461380069104861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55123499547640920046069907 82685249321461380069104861)
    ·
      refine ⟨31006968495548017525914323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82685249321461380069104861 31006968495548017525914323)
      ·
        refine ⟨46510452743322026288871485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31006968495548017525914323 46510452743322026288871485)
        ·
          refine ⟨17441419778745759858326807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46510452743322026288871485 17441419778745759858326807)
          ·
            refine ⟨26162129668118639787490211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17441419778745759858326807 26162129668118639787490211)
            ·
              refine ⟨39243194502177959681235317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26162129668118639787490211 39243194502177959681235317)
              ·
                refine ⟨3679049484579183720115811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39243194502177959681235317 3679049484579183720115811)
                ·
                  refine ⟨5518574226868775580173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679049484579183720115811 5518574226868775580173717)
                  ·
                    refine ⟨258683166884473855320643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5518574226868775580173717 258683166884473855320643)
                    ·
                      rfl

theorem cell23_1511351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_1511351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511351 prefixEnd_1511351 := by exact prefixLift 1511351
  have htrace : WordTrace (prefixWord ++ tailWord_1511351) baseStart_1511351 baseEnd_1511351 := by
    simpa [prefixWord, tailWord_1511351, baseEnd_1511351] using wordTrace_append hprefix tailTrace_1511351
  have hstable : (prefixWord ++ tailWord_1511351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511351).length < 2 ^ (prefixWord ++ tailWord_1511351).sum := by decide
  have hdescent : baseEnd_1511351 < baseStart_1511351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511368 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1511368 : Nat := 118140960795 + 1511368 * 2 ^ 59
def prefixEnd_1511368 : Nat := 4983230072969 + 3 ^ 40 * 1511368 * 2
def baseEnd_1511368 : Nat := 258686076608182666483117

theorem tailTrace_1511368 : CollatzResearch.WordTrace tailWord_1511368 prefixEnd_1511368 258686076608182666483117 := by
  unfold tailWord_1511368
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562059794289665974719379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36749413059052887966292505 27562059794289665974719379)
  ·
    refine ⟨41343089691434498962079069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27562059794289665974719379 41343089691434498962079069)
    ·
      refine ⟨15503658634287937110779651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41343089691434498962079069 15503658634287937110779651)
      ·
        refine ⟨23255487951431905666169477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15503658634287937110779651 23255487951431905666169477)
        ·
          refine ⟨4360403990893482312406777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23255487951431905666169477 4360403990893482312406777)
          ·
            refine ⟨3270302993170111734305083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360403990893482312406777 3270302993170111734305083)
            ·
              refine ⟨4905454489755167601457625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270302993170111734305083 4905454489755167601457625)
              ·
                refine ⟨3679090867316375701093219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905454489755167601457625 3679090867316375701093219)
                ·
                  refine ⟨5518636300974563551639829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679090867316375701093219 5518636300974563551639829)
                  ·
                    refine ⟨258686076608182666483117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5518636300974563551639829 258686076608182666483117)
                    ·
                      rfl

theorem cell23_1511368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1511368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511368 prefixEnd_1511368 := by exact prefixLift 1511368
  have htrace : WordTrace (prefixWord ++ tailWord_1511368) baseStart_1511368 baseEnd_1511368 := by
    simpa [prefixWord, tailWord_1511368, baseEnd_1511368] using wordTrace_append hprefix tailTrace_1511368
  have hstable : (prefixWord ++ tailWord_1511368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511368).length < 2 ^ (prefixWord ++ tailWord_1511368).sum := by decide
  have hdescent : baseEnd_1511368 < baseStart_1511368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511375 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 1, 1, 4]
def baseStart_1511375 : Nat := 118140960795 + 1511375 * 2 ^ 59
def prefixEnd_1511375 : Nat := 4983230072969 + 3 ^ 40 * 1511375 * 2
def baseEnd_1511375 : Nat := 776061824189129472061819

theorem tailTrace_1511375 : CollatzResearch.WordTrace tailWord_1511375 prefixEnd_1511375 776061824189129472061819 := by
  unfold tailWord_1511375
  simp only [CollatzResearch.WordTrace]
  refine ⟨55124374899553972144943579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36749583266369314763295719 55124374899553972144943579)
  ·
    refine ⟨82686562349330958217415369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55124374899553972144943579 82686562349330958217415369)
    ·
      refine ⟨62014921761998218663061527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82686562349330958217415369 62014921761998218663061527)
      ·
        refine ⟨93022382642997327994592291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62014921761998218663061527 93022382642997327994592291)
        ·
          refine ⟨139533573964495991991888437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93022382642997327994592291 139533573964495991991888437)
          ·
            refine ⟨13081272559171499249239541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139533573964495991991888437 13081272559171499249239541)
            ·
              refine ⟨1226369302422328054616207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13081272559171499249239541 1226369302422328054616207)
              ·
                refine ⟨1839553953633492081924311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226369302422328054616207 1839553953633492081924311)
                ·
                  refine ⟨2759330930450238122886467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839553953633492081924311 2759330930450238122886467)
                  ·
                    refine ⟨4138996395675357184329701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759330930450238122886467 4138996395675357184329701)
                    ·
                      refine ⟨776061824189129472061819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4138996395675357184329701 776061824189129472061819)
                      ·
                        rfl

theorem cell23_1511375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 1, 4].length) (baseStart_1511375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511375 prefixEnd_1511375 := by exact prefixLift 1511375
  have htrace : WordTrace (prefixWord ++ tailWord_1511375) baseStart_1511375 baseEnd_1511375 := by
    simpa [prefixWord, tailWord_1511375, baseEnd_1511375] using wordTrace_append hprefix tailTrace_1511375
  have hstable : (prefixWord ++ tailWord_1511375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511375).length < 2 ^ (prefixWord ++ tailWord_1511375).sum := by decide
  have hdescent : baseEnd_1511375 < baseStart_1511375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511381 : List Nat := [1, 3, 2, 3, 2, 12]
def baseStart_1511381 : Nat := 118140960795 + 1511381 * 2 ^ 59
def prefixEnd_1511381 : Nat := 4983230072969 + 3 ^ 40 * 1511381 * 2
def baseEnd_1511381 : Nat := 3193682736926158224637

theorem tailTrace_1511381 : CollatzResearch.WordTrace tailWord_1511381 prefixEnd_1511381 3193682736926158224637 := by
  unfold tailWord_1511381
  simp only [CollatzResearch.WordTrace]
  refine ⟨55124593737532235169661997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36749729158354823446441331 55124593737532235169661997)
  ·
    refine ⟨20671722651574588188623249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55124593737532235169661997 20671722651574588188623249)
    ·
      refine ⟨15503791988680941141467437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20671722651574588188623249 15503791988680941141467437)
      ·
        refine ⟨5813921995755352928050289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15503791988680941141467437 5813921995755352928050289)
        ·
          refine ⟨4360441496816514696037717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5813921995755352928050289 4360441496816514696037717)
          ·
            refine ⟨3193682736926158224637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4360441496816514696037717 3193682736926158224637)
            ·
              rfl

theorem cell23_1511381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 12].length) (baseStart_1511381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511381 prefixEnd_1511381 := by exact prefixLift 1511381
  have htrace : WordTrace (prefixWord ++ tailWord_1511381) baseStart_1511381 baseEnd_1511381 := by
    simpa [prefixWord, tailWord_1511381, baseEnd_1511381] using wordTrace_append hprefix tailTrace_1511381
  have hstable : (prefixWord ++ tailWord_1511381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511381).length < 2 ^ (prefixWord ++ tailWord_1511381).sum := by decide
  have hdescent : baseEnd_1511381 < baseStart_1511381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511386 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3]
def baseStart_1511386 : Nat := 118140960795 + 1511386 * 2 ^ 59
def prefixEnd_1511386 : Nat := 4983230072969 + 3 ^ 40 * 1511386 * 2
def baseEnd_1511386 : Nat := 776067472476328929024269

theorem tailTrace_1511386 : CollatzResearch.WordTrace tailWord_1511386 prefixEnd_1511386 776067472476328929024269 := by
  unfold tailWord_1511386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781194025628530255898503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36749850735009414015729341 13781194025628530255898503)
  ·
    refine ⟨20671791038442795383847755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13781194025628530255898503 20671791038442795383847755)
    ·
      refine ⟨31007686557664193075771633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20671791038442795383847755 31007686557664193075771633)
      ·
        refine ⟨23255764918248144806828725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31007686557664193075771633 23255764918248144806828725)
        ·
          refine ⟨2180227961085763575640193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23255764918248144806828725 2180227961085763575640193)
          ·
            refine ⟨1635170970814322681730145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180227961085763575640193 1635170970814322681730145)
            ·
              refine ⟨1226378228110742011297609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635170970814322681730145 1226378228110742011297609)
              ·
                refine ⟨919783671083056508473207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226378228110742011297609 919783671083056508473207)
                ·
                  refine ⟨1379675506624584762709811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919783671083056508473207 1379675506624584762709811)
                  ·
                    refine ⟨2069513259936877144064717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379675506624584762709811 2069513259936877144064717)
                    ·
                      refine ⟨776067472476328929024269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069513259936877144064717 776067472476328929024269)
                      ·
                        rfl

theorem cell23_1511386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_1511386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511386 prefixEnd_1511386 := by exact prefixLift 1511386
  have htrace : WordTrace (prefixWord ++ tailWord_1511386) baseStart_1511386 baseEnd_1511386 := by
    simpa [prefixWord, tailWord_1511386, baseEnd_1511386] using wordTrace_append hprefix tailTrace_1511386
  have hstable : (prefixWord ++ tailWord_1511386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511386).length < 2 ^ (prefixWord ++ tailWord_1511386).sum := by decide
  have hdescent : baseEnd_1511386 < baseStart_1511386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511408 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_1511408 : Nat := 118140960795 + 1511408 * 2 ^ 59
def prefixEnd_1511408 : Nat := 4983230072969 + 3 ^ 40 * 1511408 * 2
def baseEnd_1511408 : Nat := 776078769050727842949167

theorem tailTrace_1511408 : CollatzResearch.WordTrace tailWord_1511408 prefixEnd_1511408 776078769050727842949167 := by
  unfold tailWord_1511408
  simp only [CollatzResearch.WordTrace]
  refine ⟨27562789254217209390447439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36750385672289612520596585 27562789254217209390447439)
  ·
    refine ⟨41344183881325814085671159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27562789254217209390447439 41344183881325814085671159)
    ·
      refine ⟨62016275821988721128506739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41344183881325814085671159 62016275821988721128506739)
      ·
        refine ⟨93024413732983081692760109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62016275821988721128506739 93024413732983081692760109)
        ·
          refine ⟨34884155149868655634785041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93024413732983081692760109 34884155149868655634785041)
          ·
            refine ⟨26163116362401491726088781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34884155149868655634785041 26163116362401491726088781)
            ·
              refine ⟨9811168635900559397283293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26163116362401491726088781 9811168635900559397283293)
              ·
                refine ⟨3679188238462709773981235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9811168635900559397283293 3679188238462709773981235)
                ·
                  refine ⟨5518782357694064660971853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679188238462709773981235 5518782357694064660971853)
                  ·
                    refine ⟨2069543384135274247864445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5518782357694064660971853 2069543384135274247864445)
                    ·
                      refine ⟨776078769050727842949167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069543384135274247864445 776078769050727842949167)
                      ·
                        rfl

theorem cell23_1511408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_1511408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511408 prefixEnd_1511408 := by exact prefixLift 1511408
  have htrace : WordTrace (prefixWord ++ tailWord_1511408) baseStart_1511408 baseEnd_1511408 := by
    simpa [prefixWord, tailWord_1511408, baseEnd_1511408] using wordTrace_append hprefix tailTrace_1511408
  have hstable : (prefixWord ++ tailWord_1511408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511408).length < 2 ^ (prefixWord ++ tailWord_1511408).sum := by decide
  have hdescent : baseEnd_1511408 < baseStart_1511408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511425 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1511425 : Nat := 118140960795 + 1511425 * 2 ^ 59
def prefixEnd_1511425 : Nat := 4983230072969 + 3 ^ 40 * 1511425 * 2
def baseEnd_1511425 : Nat := 776087498221854276436589

theorem tailTrace_1511425 : CollatzResearch.WordTrace tailWord_1511425 prefixEnd_1511425 776087498221854276436589 := by
  unfold tailWord_1511425
  simp only [CollatzResearch.WordTrace]
  refine ⟨55126198549372830684263729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36750799032915220456175819 55126198549372830684263729)
  ·
    refine ⟨41344648912029623013197797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55126198549372830684263729 41344648912029623013197797)
    ·
      refine ⟨7752121671005554314974587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41344648912029623013197797 7752121671005554314974587)
      ·
        refine ⟨11628182506508331472461881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752121671005554314974587 11628182506508331472461881)
        ·
          refine ⟨8721136879881248604346411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11628182506508331472461881 8721136879881248604346411)
          ·
            refine ⟨13081705319821872906519617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8721136879881248604346411 13081705319821872906519617)
            ·
              refine ⟨9811278989866404679889713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13081705319821872906519617 9811278989866404679889713)
              ·
                refine ⟨7358459242399803509917285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9811278989866404679889713 7358459242399803509917285)
                ·
                  refine ⟨1379711107949963158109491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7358459242399803509917285 1379711107949963158109491)
                  ·
                    refine ⟨2069566661924944737164237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379711107949963158109491 2069566661924944737164237)
                    ·
                      refine ⟨776087498221854276436589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069566661924944737164237 776087498221854276436589)
                      ·
                        rfl

theorem cell23_1511425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1511425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511425 prefixEnd_1511425 := by exact prefixLift 1511425
  have htrace : WordTrace (prefixWord ++ tailWord_1511425) baseStart_1511425 baseEnd_1511425 := by
    simpa [prefixWord, tailWord_1511425, baseEnd_1511425] using wordTrace_append hprefix tailTrace_1511425
  have hstable : (prefixWord ++ tailWord_1511425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511425).length < 2 ^ (prefixWord ++ tailWord_1511425).sum := by decide
  have hdescent : baseEnd_1511425 < baseStart_1511425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511451 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_1511451 : Nat := 118140960795 + 1511451 * 2 ^ 59
def prefixEnd_1511451 : Nat := 4983230072969 + 3 ^ 40 * 1511451 * 2
def baseEnd_1511451 : Nat := 776100848718871174711469

theorem tailTrace_1511451 : CollatzResearch.WordTrace tailWord_1511451 prefixEnd_1511451 776100848718871174711469 := by
  unfold tailWord_1511451
  simp only [CollatzResearch.WordTrace]
  refine ⟨55127146847278637124710207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36751431231519091416473471 55127146847278637124710207)
  ·
    refine ⟨82690720270917955687065311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55127146847278637124710207 82690720270917955687065311)
    ·
      refine ⟨124036080406376933530597967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82690720270917955687065311 124036080406376933530597967)
      ·
        refine ⟨186054120609565400295896951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124036080406376933530597967 186054120609565400295896951)
        ·
          refine ⟨279081180914348100443845427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186054120609565400295896951 279081180914348100443845427)
          ·
            refine ⟨418621771371522150665768141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279081180914348100443845427 418621771371522150665768141)
            ·
              refine ⟨156983164264320806499663053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418621771371522150665768141 156983164264320806499663053)
              ·
                refine ⟨58868686599120302437373645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156983164264320806499663053 58868686599120302437373645)
                ·
                  refine ⟨22075757474670113414015117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58868686599120302437373645 22075757474670113414015117)
                  ·
                    refine ⟨8278409053001292530255669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22075757474670113414015117 8278409053001292530255669)
                    ·
                      refine ⟨776100848718871174711469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8278409053001292530255669 776100848718871174711469)
                      ·
                        rfl

theorem cell23_1511451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_1511451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511451 prefixEnd_1511451 := by exact prefixLift 1511451
  have htrace : WordTrace (prefixWord ++ tailWord_1511451) baseStart_1511451 baseEnd_1511451 := by
    simpa [prefixWord, tailWord_1511451, baseEnd_1511451] using wordTrace_append hprefix tailTrace_1511451
  have hstable : (prefixWord ++ tailWord_1511451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511451).length < 2 ^ (prefixWord ++ tailWord_1511451).sum := by decide
  have hdescent : baseEnd_1511451 < baseStart_1511451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511458 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1511458 : Nat := 118140960795 + 1511458 * 2 ^ 59
def prefixEnd_1511458 : Nat := 4983230072969 + 3 ^ 40 * 1511458 * 2
def baseEnd_1511458 : Nat := 258701481027817549107979

theorem tailTrace_1511458 : CollatzResearch.WordTrace tailWord_1511458 prefixEnd_1511458 258701481027817549107979 := by
  unfold tailWord_1511458
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781850539563319330053757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36751601438835518213476685 13781850539563319330053757)
  ·
    refine ⟨5168193952336244748770159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13781850539563319330053757 5168193952336244748770159)
    ·
      refine ⟨7752290928504367123155239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5168193952336244748770159 7752290928504367123155239)
      ·
        refine ⟨11628436392756550684732859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7752290928504367123155239 11628436392756550684732859)
        ·
          refine ⟨17442654589134826027099289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11628436392756550684732859 17442654589134826027099289)
          ·
            refine ⟨13081990941851119520324467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17442654589134826027099289 13081990941851119520324467)
            ·
              refine ⟨19622986412776679280486701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13081990941851119520324467 19622986412776679280486701)
              ·
                refine ⟨7358619904791254730182513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19622986412776679280486701 7358619904791254730182513)
                ·
                  refine ⟨5518964928593441047636885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7358619904791254730182513 5518964928593441047636885)
                  ·
                    refine ⟨258701481027817549107979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5518964928593441047636885 258701481027817549107979)
                    ·
                      rfl

theorem cell23_1511458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1511458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511458 prefixEnd_1511458 := by exact prefixLift 1511458
  have htrace : WordTrace (prefixWord ++ tailWord_1511458) baseStart_1511458 baseEnd_1511458 := by
    simpa [prefixWord, tailWord_1511458, baseEnd_1511458] using wordTrace_append hprefix tailTrace_1511458
  have hstable : (prefixWord ++ tailWord_1511458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511458).length < 2 ^ (prefixWord ++ tailWord_1511458).sum := by decide
  have hdescent : baseEnd_1511458 < baseStart_1511458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511471 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 9]
def baseStart_1511471 : Nat := 118140960795 + 1511471 * 2 ^ 59
def prefixEnd_1511471 : Nat := 4983230072969 + 3 ^ 40 * 1511471 * 2
def baseEnd_1511471 : Nat := 86234568703551232940153

theorem tailTrace_1511471 : CollatzResearch.WordTrace tailWord_1511471 prefixEnd_1511471 86234568703551232940153 := by
  unfold tailWord_1511471
  simp only [CollatzResearch.WordTrace]
  refine ⟨55127876307206180540438267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36751917538137453693625511 55127876307206180540438267)
  ·
    refine ⟨82691814460809270810657401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55127876307206180540438267 82691814460809270810657401)
    ·
      refine ⟨62018860845606953107993051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82691814460809270810657401 62018860845606953107993051)
      ·
        refine ⟨93028291268410429661989577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62018860845606953107993051 93028291268410429661989577)
        ·
          refine ⟨69771218451307822246492183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93028291268410429661989577 69771218451307822246492183)
          ·
            refine ⟨104656827676961733369738275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69771218451307822246492183 104656827676961733369738275)
            ·
              refine ⟨156985241515442600054607413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104656827676961733369738275 156985241515442600054607413)
              ·
                refine ⟨14717366392072743755119445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156985241515442600054607413 14717366392072743755119445)
                ·
                  refine ⟨86234568703551232940153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14717366392072743755119445 86234568703551232940153)
                  ·
                    rfl

theorem cell23_1511471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 9].length) (baseStart_1511471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511471 prefixEnd_1511471 := by exact prefixLift 1511471
  have htrace : WordTrace (prefixWord ++ tailWord_1511471) baseStart_1511471 baseEnd_1511471 := by
    simpa [prefixWord, tailWord_1511471, baseEnd_1511471] using wordTrace_append hprefix tailTrace_1511471
  have hstable : (prefixWord ++ tailWord_1511471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511471).length < 2 ^ (prefixWord ++ tailWord_1511471).sum := by decide
  have hdescent : baseEnd_1511471 < baseStart_1511471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511516 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_1511516 : Nat := 118140960795 + 1511516 * 2 ^ 59
def prefixEnd_1511516 : Nat := 4983230072969 + 3 ^ 40 * 1511516 * 2
def baseEnd_1511516 : Nat := 776134224961413420398671

theorem tailTrace_1511516 : CollatzResearch.WordTrace tailWord_1511516 prefixEnd_1511516 776134224961413420398671 := by
  unfold tailWord_1511516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27564758796021576612913201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36753011728028768817217601 27564758796021576612913201)
  ·
    refine ⟨20673569097016182459684901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27564758796021576612913201 20673569097016182459684901)
    ·
      refine ⟨3876294205690534211190919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20673569097016182459684901 3876294205690534211190919)
      ·
        refine ⟨5814441308535801316786379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876294205690534211190919 5814441308535801316786379)
        ·
          refine ⟨8721661962803701975179569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814441308535801316786379 8721661962803701975179569)
          ·
            refine ⟨6541246472102776481384677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8721661962803701975179569 6541246472102776481384677)
            ·
              refine ⟨1226483713519270590259627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6541246472102776481384677 1226483713519270590259627)
              ·
                refine ⟨1839725570278905885389441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226483713519270590259627 1839725570278905885389441)
                ·
                  refine ⟨1379794177709179414042081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1839725570278905885389441 1379794177709179414042081)
                  ·
                    refine ⟨1034845633281884560531561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1379794177709179414042081 1034845633281884560531561)
                    ·
                      refine ⟨776134224961413420398671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1034845633281884560531561 776134224961413420398671)
                      ·
                        rfl

theorem cell23_1511516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_1511516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511516 prefixEnd_1511516 := by exact prefixLift 1511516
  have htrace : WordTrace (prefixWord ++ tailWord_1511516) baseStart_1511516 baseEnd_1511516 := by
    simpa [prefixWord, tailWord_1511516, baseEnd_1511516] using wordTrace_append hprefix tailTrace_1511516
  have hstable : (prefixWord ++ tailWord_1511516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511516).length < 2 ^ (prefixWord ++ tailWord_1511516).sum := by decide
  have hdescent : baseEnd_1511516 < baseStart_1511516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511535 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 2, 5]
def baseStart_1511535 : Nat := 118140960795 + 1511535 * 2 ^ 59
def prefixEnd_1511535 : Nat := 4983230072969 + 3 ^ 40 * 1511535 * 2
def baseEnd_1511535 : Nat := 258714660364616282020361

theorem tailTrace_1511535 : CollatzResearch.WordTrace tailWord_1511535 prefixEnd_1511535 258714660364616282020361 := by
  unfold tailWord_1511535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55130210578974319470768059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36753473719316212980512039 55130210578974319470768059)
  ·
    refine ⟨82695315868461479206152089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55130210578974319470768059 82695315868461479206152089)
    ·
      refine ⟨62021486901346109404614067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82695315868461479206152089 62021486901346109404614067)
      ·
        refine ⟨93032230352019164106921101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62021486901346109404614067 93032230352019164106921101)
        ·
          refine ⟨34887086382007186540095413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93032230352019164106921101 34887086382007186540095413)
          ·
            refine ⟨3270664348313173738133945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34887086382007186540095413 3270664348313173738133945)
            ·
              refine ⟨2452998261234880303600459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3270664348313173738133945 2452998261234880303600459)
              ·
                refine ⟨3679497391852320455400689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452998261234880303600459 3679497391852320455400689)
                ·
                  refine ⟨2759623043889240341550517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679497391852320455400689 2759623043889240341550517)
                  ·
                    refine ⟨258714660364616282020361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2759623043889240341550517 258714660364616282020361)
                    ·
                      rfl

theorem cell23_1511535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_1511535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511535 prefixEnd_1511535 := by exact prefixLift 1511535
  have htrace : WordTrace (prefixWord ++ tailWord_1511535) baseStart_1511535 baseEnd_1511535 := by
    simpa [prefixWord, tailWord_1511535, baseEnd_1511535] using wordTrace_append hprefix tailTrace_1511535
  have hstable : (prefixWord ++ tailWord_1511535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511535).length < 2 ^ (prefixWord ++ tailWord_1511535).sum := by decide
  have hdescent : baseEnd_1511535 < baseStart_1511535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511555 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1511555 : Nat := 118140960795 + 1511555 * 2 ^ 59
def prefixEnd_1511555 : Nat := 4983230072969 + 3 ^ 40 * 1511555 * 2
def baseEnd_1511555 : Nat := 776154250706938767810991

theorem tailTrace_1511555 : CollatzResearch.WordTrace tailWord_1511555 prefixEnd_1511555 776154250706938767810991 := by
  unfold tailWord_1511555
  simp only [CollatzResearch.WordTrace]
  refine ⟨55130940038901862886496119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36753960025934575257664079 55130940038901862886496119)
  ·
    refine ⟨82696410058352794329744179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55130940038901862886496119 82696410058352794329744179)
    ·
      refine ⟨124044615087529191494616269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82696410058352794329744179 124044615087529191494616269)
      ·
        refine ⟨46516730657823446810481101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124044615087529191494616269 46516730657823446810481101)
        ·
          refine ⟨17443773996683792553930413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46516730657823446810481101 17443773996683792553930413)
          ·
            refine ⟨6541415248756422207723905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17443773996683792553930413 6541415248756422207723905)
            ·
              refine ⟨4906061436567316655792929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6541415248756422207723905 4906061436567316655792929)
              ·
                refine ⟨3679546077425487491844697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906061436567316655792929 3679546077425487491844697)
                ·
                  refine ⟨2759659558069115618883523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3679546077425487491844697 2759659558069115618883523)
                  ·
                    refine ⟨4139489337103673428325285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2759659558069115618883523 4139489337103673428325285)
                    ·
                      refine ⟨776154250706938767810991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4139489337103673428325285 776154250706938767810991)
                      ·
                        rfl

theorem cell23_1511555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1511555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511555 prefixEnd_1511555 := by exact prefixLift 1511555
  have htrace : WordTrace (prefixWord ++ tailWord_1511555) baseStart_1511555 baseEnd_1511555 := by
    simpa [prefixWord, tailWord_1511555, baseEnd_1511555] using wordTrace_append hprefix tailTrace_1511555
  have hstable : (prefixWord ++ tailWord_1511555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511555).length < 2 ^ (prefixWord ++ tailWord_1511555).sum := by decide
  have hdescent : baseEnd_1511555 < baseStart_1511555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511656 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1511656 : Nat := 118140960795 + 1511656 * 2 ^ 59
def prefixEnd_1511656 : Nat := 4983230072969 + 3 ^ 40 * 1511656 * 2
def baseEnd_1511656 : Nat := 776206112253042872648027

theorem tailTrace_1511656 : CollatzResearch.WordTrace tailWord_1511656 prefixEnd_1511656 776206112253042872648027 := by
  unfold tailWord_1511656
  simp only [CollatzResearch.WordTrace]
  refine ⟨27567311905767978567961411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36756415874357304757281881 27567311905767978567961411)
  ·
    refine ⟨41350967858651967851942117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27567311905767978567961411 41350967858651967851942117)
    ·
      refine ⟨7753306473497243972239147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41350967858651967851942117 7753306473497243972239147)
      ·
        refine ⟨11629959710245865958358721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753306473497243972239147 11629959710245865958358721)
        ·
          refine ⟨8722469782684399468769041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11629959710245865958358721 8722469782684399468769041)
          ·
            refine ⟨6541852337013299601576781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8722469782684399468769041 6541852337013299601576781)
            ·
              refine ⟨2453194626379987350591293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6541852337013299601576781 2453194626379987350591293)
              ·
                refine ⟨919947984892495256471735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453194626379987350591293 919947984892495256471735)
                ·
                  refine ⟨1379921977338742884707603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919947984892495256471735 1379921977338742884707603)
                  ·
                    refine ⟨2069882966008114327061405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1379921977338742884707603 2069882966008114327061405)
                    ·
                      refine ⟨776206112253042872648027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069882966008114327061405 776206112253042872648027)
                      ·
                        rfl

theorem cell23_1511656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1511656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511656 prefixEnd_1511656 := by exact prefixLift 1511656
  have htrace : WordTrace (prefixWord ++ tailWord_1511656) baseStart_1511656 baseEnd_1511656 := by
    simpa [prefixWord, tailWord_1511656, baseEnd_1511656] using wordTrace_append hprefix tailTrace_1511656
  have hstable : (prefixWord ++ tailWord_1511656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511656).length < 2 ^ (prefixWord ++ tailWord_1511656).sum := by decide
  have hdescent : baseEnd_1511656 < baseStart_1511656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511665 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1511665 : Nat := 118140960795 + 1511665 * 2 ^ 59
def prefixEnd_1511665 : Nat := 4983230072969 + 3 ^ 40 * 1511665 * 2
def baseEnd_1511665 : Nat := 776210733578933337435485

theorem tailTrace_1511665 : CollatzResearch.WordTrace tailWord_1511665 prefixEnd_1511665 776210733578933337435485 := by
  unfold tailWord_1511665
  simp only [CollatzResearch.WordTrace]
  refine ⟨55134952068503351673000449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36756634712335567782000299 55134952068503351673000449)
  ·
    refine ⟨41351214051377513754750337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55134952068503351673000449 41351214051377513754750337)
    ·
      refine ⟨31013410538533135316062753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41351214051377513754750337 31013410538533135316062753)
      ·
        refine ⟨23260057903899851487047065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31013410538533135316062753 23260057903899851487047065)
        ·
          refine ⟨17445043427924888615285299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23260057903899851487047065 17445043427924888615285299)
          ·
            refine ⟨26167565141887332922927949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17445043427924888615285299 26167565141887332922927949)
            ·
              refine ⟨9812836928207749846097981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26167565141887332922927949 9812836928207749846097981)
              ·
                refine ⟨3679813848077906192286743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9812836928207749846097981 3679813848077906192286743)
                ·
                  refine ⟨5519720772116859288430115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679813848077906192286743 5519720772116859288430115)
                  ·
                    refine ⟨8279581158175288932645173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5519720772116859288430115 8279581158175288932645173)
                    ·
                      refine ⟨776210733578933337435485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8279581158175288932645173 776210733578933337435485)
                      ·
                        rfl

theorem cell23_1511665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1511665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511665 prefixEnd_1511665 := by exact prefixLift 1511665
  have htrace : WordTrace (prefixWord ++ tailWord_1511665) baseStart_1511665 baseEnd_1511665 := by
    simpa [prefixWord, tailWord_1511665, baseEnd_1511665] using wordTrace_append hprefix tailTrace_1511665
  have hstable : (prefixWord ++ tailWord_1511665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511665).length < 2 ^ (prefixWord ++ tailWord_1511665).sum := by decide
  have hdescent : baseEnd_1511665 < baseStart_1511665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511689 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 2, 4]
def baseStart_1511689 : Nat := 118140960795 + 1511689 * 2 ^ 59
def prefixEnd_1511689 : Nat := 4983230072969 + 3 ^ 40 * 1511689 * 2
def baseEnd_1511689 : Nat := 258741019038213747845125

theorem tailTrace_1511689 : CollatzResearch.WordTrace tailWord_1511689 prefixEnd_1511689 258741019038213747845125 := by
  unfold tailWord_1511689
  simp only [CollatzResearch.WordTrace]
  refine ⟨55135827420416403771874121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36757218280277602514582747 55135827420416403771874121)
  ·
    refine ⟨41351870565312302828905591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55135827420416403771874121 41351870565312302828905591)
    ·
      refine ⟨62027805847968454243358387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41351870565312302828905591 62027805847968454243358387)
      ·
        refine ⟨93041708771952681365037581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62027805847968454243358387 93041708771952681365037581)
        ·
          refine ⟨34890640789482255511889093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93041708771952681365037581 34890640789482255511889093)
          ·
            refine ⟨6541995148027922908479205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34890640789482255511889093 6541995148027922908479205)
            ·
              refine ⟨1226624090255235545339851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6541995148027922908479205 1226624090255235545339851)
              ·
                refine ⟨1839936135382853318009777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226624090255235545339851 1839936135382853318009777)
                ·
                  refine ⟨1379952101537139988507333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1839936135382853318009777 1379952101537139988507333)
                  ·
                    refine ⟨258741019038213747845125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379952101537139988507333 258741019038213747845125)
                    ·
                      rfl

theorem cell23_1511689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_1511689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511689 prefixEnd_1511689 := by exact prefixLift 1511689
  have htrace : WordTrace (prefixWord ++ tailWord_1511689) baseStart_1511689 baseEnd_1511689 := by
    simpa [prefixWord, tailWord_1511689, baseEnd_1511689] using wordTrace_append hprefix tailTrace_1511689
  have hstable : (prefixWord ++ tailWord_1511689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511689).length < 2 ^ (prefixWord ++ tailWord_1511689).sum := by decide
  have hdescent : baseEnd_1511689 < baseStart_1511689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511695 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_1511695 : Nat := 118140960795 + 1511695 * 2 ^ 59
def prefixEnd_1511695 : Nat := 4983230072969 + 3 ^ 40 * 1511695 * 2
def baseEnd_1511695 : Nat := 776226137998568220060347

theorem tailTrace_1511695 : CollatzResearch.WordTrace tailWord_1511695 prefixEnd_1511695 776226137998568220060347 := by
  unfold tailWord_1511695
  simp only [CollatzResearch.WordTrace]
  refine ⟨55136046258394666796592539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36757364172263111197728359 55136046258394666796592539)
  ·
    refine ⟨82704069387592000194888809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55136046258394666796592539 82704069387592000194888809)
    ·
      refine ⟨62028052040694000146166607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82704069387592000194888809 62028052040694000146166607)
      ·
        refine ⟨93042078061041000219249911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62028052040694000146166607 93042078061041000219249911)
        ·
          refine ⟨139563117091561500328874867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93042078061041000219249911 139563117091561500328874867)
          ·
            refine ⟨209344675637342250493312301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139563117091561500328874867 209344675637342250493312301)
            ·
              refine ⟨78504253364003343934992113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209344675637342250493312301 78504253364003343934992113)
              ·
                refine ⟨58878190023002507951244085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78504253364003343934992113 58878190023002507951244085)
                ·
                  refine ⟨5519830314656485120429133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58878190023002507951244085 5519830314656485120429133)
                  ·
                    refine ⟨2069936367996181920160925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5519830314656485120429133 2069936367996181920160925)
                    ·
                      refine ⟨776226137998568220060347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069936367996181920160925 776226137998568220060347)
                      ·
                        rfl

theorem cell23_1511695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_1511695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511695 prefixEnd_1511695 := by exact prefixLift 1511695
  have htrace : WordTrace (prefixWord ++ tailWord_1511695) baseStart_1511695 baseEnd_1511695 := by
    simpa [prefixWord, tailWord_1511695, baseEnd_1511695] using wordTrace_append hprefix tailTrace_1511695
  have hstable : (prefixWord ++ tailWord_1511695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511695).length < 2 ^ (prefixWord ++ tailWord_1511695).sum := by decide
  have hdescent : baseEnd_1511695 < baseStart_1511695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511709 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1511709 : Nat := 118140960795 + 1511709 * 2 ^ 59
def prefixEnd_1511709 : Nat := 4983230072969 + 3 ^ 40 * 1511709 * 2
def baseEnd_1511709 : Nat := 776233326727731165285283

theorem tailTrace_1511709 : CollatzResearch.WordTrace tailWord_1511709 prefixEnd_1511709 776233326727731165285283 := by
  unfold tailWord_1511709
  simp only [CollatzResearch.WordTrace]
  refine ⟨55136556880343947187602181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36757704586895964791734787 55136556880343947187602181)
  ·
    refine ⟨10338104415064490097675409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55136556880343947187602181 10338104415064490097675409)
    ·
      refine ⟨7753578311298367573256557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10338104415064490097675409 7753578311298367573256557)
      ·
        refine ⟨2907591866736887839971209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7753578311298367573256557 2907591866736887839971209)
        ·
          refine ⟨2180693900052665879978407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907591866736887839971209 2180693900052665879978407)
          ·
            refine ⟨3271040850078998819967611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180693900052665879978407 3271040850078998819967611)
            ·
              refine ⟨4906561275118498229951417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271040850078998819967611 4906561275118498229951417)
              ·
                refine ⟨3679920956338873672463563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906561275118498229951417 3679920956338873672463563)
                ·
                  refine ⟨5519881434508310508695345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3679920956338873672463563 5519881434508310508695345)
                  ·
                    refine ⟨4139911075881232881521509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5519881434508310508695345 4139911075881232881521509)
                    ·
                      refine ⟨776233326727731165285283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4139911075881232881521509 776233326727731165285283)
                      ·
                        rfl

theorem cell23_1511709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1511709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511709 prefixEnd_1511709 := by exact prefixLift 1511709
  have htrace : WordTrace (prefixWord ++ tailWord_1511709) baseStart_1511709 baseEnd_1511709 := by
    simpa [prefixWord, tailWord_1511709, baseEnd_1511709] using wordTrace_append hprefix tailTrace_1511709
  have hstable : (prefixWord ++ tailWord_1511709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511709).length < 2 ^ (prefixWord ++ tailWord_1511709).sum := by decide
  have hdescent : baseEnd_1511709 < baseStart_1511709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511712 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1511712 : Nat := 118140960795 + 1511712 * 2 ^ 59
def prefixEnd_1511712 : Nat := 4983230072969 + 3 ^ 40 * 1511712 * 2
def baseEnd_1511712 : Nat := 776234867169694653547769

theorem tailTrace_1511712 : CollatzResearch.WordTrace tailWord_1511712 prefixEnd_1511712 776234867169694653547769 := by
  unfold tailWord_1511712
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568333149666539349980695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36757777532888719133307593 27568333149666539349980695)
  ·
    refine ⟨41352499724499809024971043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27568333149666539349980695 41352499724499809024971043)
    ·
      refine ⟨62028749586749713537456565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41352499724499809024971043 62028749586749713537456565)
      ·
        refine ⟨5815195273757785644136553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62028749586749713537456565 5815195273757785644136553)
        ·
          refine ⟨4361396455318339233102415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5815195273757785644136553 4361396455318339233102415)
          ·
            refine ⟨6542094682977508849653623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361396455318339233102415 6542094682977508849653623)
            ·
              refine ⟨9813142024466263274480435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542094682977508849653623 9813142024466263274480435)
              ·
                refine ⟨14719713036699394911720653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813142024466263274480435 14719713036699394911720653)
                ·
                  refine ⟨5519892388762273091895245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14719713036699394911720653 5519892388762273091895245)
                  ·
                    refine ⟨2069959645785852409460717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5519892388762273091895245 2069959645785852409460717)
                    ·
                      refine ⟨776234867169694653547769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069959645785852409460717 776234867169694653547769)
                      ·
                        rfl

theorem cell23_1511712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1511712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511712 prefixEnd_1511712 := by exact prefixLift 1511712
  have htrace : WordTrace (prefixWord ++ tailWord_1511712) baseStart_1511712 baseEnd_1511712 := by
    simpa [prefixWord, tailWord_1511712, baseEnd_1511712] using wordTrace_append hprefix tailTrace_1511712
  have hstable : (prefixWord ++ tailWord_1511712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511712).length < 2 ^ (prefixWord ++ tailWord_1511712).sum := by decide
  have hdescent : baseEnd_1511712 < baseStart_1511712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511716 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_1511716 : Nat := 118140960795 + 1511716 * 2 ^ 59
def prefixEnd_1511716 : Nat := 4983230072969 + 3 ^ 40 * 1511716 * 2
def baseEnd_1511716 : Nat := 776236921092312637897751

theorem tailTrace_1511716 : CollatzResearch.WordTrace tailWord_1511716 prefixEnd_1511716 776236921092312637897751 := by
  unfold tailWord_1511716
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568406095659293691553501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36757874794212391588738001 27568406095659293691553501)
  ·
    refine ⟨10338152285872235134332563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27568406095659293691553501 10338152285872235134332563)
    ·
      refine ⟨15507228428808352701498845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338152285872235134332563 15507228428808352701498845)
      ·
        refine ⟨5815210660803132263062067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15507228428808352701498845 5815210660803132263062067)
        ·
          refine ⟨8722815991204698394593101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815210660803132263062067 8722815991204698394593101)
          ·
            refine ⟨3271055996701761897972413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8722815991204698394593101 3271055996701761897972413)
            ·
              refine ⟨1226645998763160711739655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3271055996701761897972413 1226645998763160711739655)
              ·
                refine ⟨1839968998144741067609483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226645998763160711739655 1839968998144741067609483)
                ·
                  refine ⟨2759953497217111601414225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839968998144741067609483 2759953497217111601414225)
                  ·
                    refine ⟨2069965122912833701060669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2759953497217111601414225 2069965122912833701060669)
                    ·
                      refine ⟨776236921092312637897751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2069965122912833701060669 776236921092312637897751)
                      ·
                        rfl

theorem cell23_1511716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_1511716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511716 prefixEnd_1511716 := by exact prefixLift 1511716
  have htrace : WordTrace (prefixWord ++ tailWord_1511716) baseStart_1511716 baseEnd_1511716 := by
    simpa [prefixWord, tailWord_1511716, baseEnd_1511716] using wordTrace_append hprefix tailTrace_1511716
  have hstable : (prefixWord ++ tailWord_1511716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511716).length < 2 ^ (prefixWord ++ tailWord_1511716).sum := by decide
  have hdescent : baseEnd_1511716 < baseStart_1511716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511719 : List Nat := [1, 1, 8, 1, 1, 11]
def baseStart_1511719 : Nat := 118140960795 + 1511719 * 2 ^ 59
def prefixEnd_1511719 : Nat := 4983230072969 + 3 ^ 40 * 1511719 * 2
def baseEnd_1511719 : Nat := 3194396961046403811359

theorem tailTrace_1511719 : CollatzResearch.WordTrace tailWord_1511719 prefixEnd_1511719 3194396961046403811359 := by
  unfold tailWord_1511719
  simp only [CollatzResearch.WordTrace]
  refine ⟨55136921610307718895466211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36757947740205145930310807 55136921610307718895466211)
  ·
    refine ⟨82705382415461578343199317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55136921610307718895466211 82705382415461578343199317)
    ·
      refine ⟨969203700181190371209367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 82705382415461578343199317 969203700181190371209367)
      ·
        refine ⟨1453805550271785556814051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969203700181190371209367 1453805550271785556814051)
        ·
          refine ⟨2180708325407678335221077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453805550271785556814051 2180708325407678335221077)
          ·
            refine ⟨3194396961046403811359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2180708325407678335221077 3194396961046403811359)
            ·
              rfl

theorem cell23_1511719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 11].length) (baseStart_1511719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511719 prefixEnd_1511719 := by exact prefixLift 1511719
  have htrace : WordTrace (prefixWord ++ tailWord_1511719) baseStart_1511719 baseEnd_1511719 := by
    simpa [prefixWord, tailWord_1511719, baseEnd_1511719] using wordTrace_append hprefix tailTrace_1511719
  have hstable : (prefixWord ++ tailWord_1511719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511719).length < 2 ^ (prefixWord ++ tailWord_1511719).sum := by decide
  have hdescent : baseEnd_1511719 < baseStart_1511719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511732 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1511732 : Nat := 118140960795 + 1511732 * 2 ^ 59
def prefixEnd_1511732 : Nat := 4983230072969 + 3 ^ 40 * 1511732 * 2
def baseEnd_1511732 : Nat := 258748378927594858432559

theorem tailTrace_1511732 : CollatzResearch.WordTrace tailWord_1511732 prefixEnd_1511732 258748378927594858432559 := by
  unfold tailWord_1511732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568697879630311057844725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36758263839507081410459633 27568697879630311057844725)
  ·
    refine ⟨2584565426215341661672943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27568697879630311057844725 2584565426215341661672943)
    ·
      refine ⟨3876848139323012492509415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584565426215341661672943 3876848139323012492509415)
      ·
        refine ⟨5815272208984518738764123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876848139323012492509415 5815272208984518738764123)
        ·
          refine ⟨8722908313476778108146185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5815272208984518738764123 8722908313476778108146185)
          ·
            refine ⟨6542181235107583581109639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8722908313476778108146185 6542181235107583581109639)
            ·
              refine ⟨9813271852661375371664459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542181235107583581109639 9813271852661375371664459)
              ·
                refine ⟨14719907778992063057496689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9813271852661375371664459 14719907778992063057496689)
                ·
                  refine ⟨11039930834244047293122517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14719907778992063057496689 11039930834244047293122517)
                  ·
                    refine ⟨258748378927594858432559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11039930834244047293122517 258748378927594858432559)
                    ·
                      rfl

theorem cell23_1511732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1511732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511732 prefixEnd_1511732 := by exact prefixLift 1511732
  have htrace : WordTrace (prefixWord ++ tailWord_1511732) baseStart_1511732 baseEnd_1511732 := by
    simpa [prefixWord, tailWord_1511732, baseEnd_1511732] using wordTrace_append hprefix tailTrace_1511732
  have hstable : (prefixWord ++ tailWord_1511732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511732).length < 2 ^ (prefixWord ++ tailWord_1511732).sum := by decide
  have hdescent : baseEnd_1511732 < baseStart_1511732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511755 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_1511755 : Nat := 118140960795 + 1511755 * 2 ^ 59
def prefixEnd_1511755 : Nat := 4983230072969 + 3 ^ 40 * 1511755 * 2
def baseEnd_1511755 : Nat := 776256946837837985310071

theorem tailTrace_1511755 : CollatzResearch.WordTrace tailWord_1511755 prefixEnd_1511755 776256946837837985310071 := by
  unfold tailWord_1511755
  simp only [CollatzResearch.WordTrace]
  refine ⟨55138234638177297043776719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36758823092118198029184479 55138234638177297043776719)
  ·
    refine ⟨82707351957265945565665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55138234638177297043776719 82707351957265945565665079)
    ·
      refine ⟨124061027935898918348497619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82707351957265945565665079 124061027935898918348497619)
      ·
        refine ⟨186091541903848377522746429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124061027935898918348497619 186091541903848377522746429)
        ·
          refine ⟨69784328213943141571029911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186091541903848377522746429 69784328213943141571029911)
          ·
            refine ⟨104676492320914712356544867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69784328213943141571029911 104676492320914712356544867)
            ·
              refine ⟨157014738481372068534817301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104676492320914712356544867 157014738481372068534817301)
              ·
                refine ⟨7360065866314315712569561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157014738481372068534817301 7360065866314315712569561)
                ·
                  refine ⟨5520049399735736784427171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7360065866314315712569561 5520049399735736784427171)
                  ·
                    refine ⟨8280074099603605176640757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520049399735736784427171 8280074099603605176640757)
                    ·
                      refine ⟨776256946837837985310071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8280074099603605176640757 776256946837837985310071)
                      ·
                        rfl

theorem cell23_1511755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_1511755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511755 prefixEnd_1511755 := by exact prefixLift 1511755
  have htrace : WordTrace (prefixWord ++ tailWord_1511755) baseStart_1511755 baseEnd_1511755 := by
    simpa [prefixWord, tailWord_1511755, baseEnd_1511755] using wordTrace_append hprefix tailTrace_1511755
  have hstable : (prefixWord ++ tailWord_1511755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511755).length < 2 ^ (prefixWord ++ tailWord_1511755).sum := by decide
  have hdescent : baseEnd_1511755 < baseStart_1511755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511769 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 4, 2, 2]
def baseStart_1511769 : Nat := 118140960795 + 1511769 * 2 ^ 59
def prefixEnd_1511769 : Nat := 4983230072969 + 3 ^ 40 * 1511769 * 2
def baseEnd_1511769 : Nat := 776264135567000930535007

theorem tailTrace_1511769 : CollatzResearch.WordTrace tailWord_1511769 prefixEnd_1511769 776264135567000930535007 := by
  unfold tailWord_1511769
  simp only [CollatzResearch.WordTrace]
  refine ⟨55138745260126577434786361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36759163506751051623190907 55138745260126577434786361)
  ·
    refine ⟨41354058945094933076089771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55138745260126577434786361 41354058945094933076089771)
    ·
      refine ⟨62031088417642399614134657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41354058945094933076089771 62031088417642399614134657)
      ·
        refine ⟨46523316313231799710600993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62031088417642399614134657 46523316313231799710600993)
        ·
          refine ⟨34892487234923849782950745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46523316313231799710600993 34892487234923849782950745)
          ·
            refine ⟨26169365426192887337213059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34892487234923849782950745 26169365426192887337213059)
            ·
              refine ⟨39254048139289331005819589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26169365426192887337213059 39254048139289331005819589)
              ·
                refine ⟨7360134026116749563591173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39254048139289331005819589 7360134026116749563591173)
                ·
                  refine ⟨1380025129896890543173345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7360134026116749563591173 1380025129896890543173345)
                  ·
                    refine ⟨1035018847422667907380009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380025129896890543173345 1035018847422667907380009)
                    ·
                      refine ⟨776264135567000930535007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035018847422667907380009 776264135567000930535007)
                      ·
                        rfl

theorem cell23_1511769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_1511769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511769 prefixEnd_1511769 := by exact prefixLift 1511769
  have htrace : WordTrace (prefixWord ++ tailWord_1511769) baseStart_1511769 baseEnd_1511769 := by
    simpa [prefixWord, tailWord_1511769, baseEnd_1511769] using wordTrace_append hprefix tailTrace_1511769
  have hstable : (prefixWord ++ tailWord_1511769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511769).length < 2 ^ (prefixWord ++ tailWord_1511769).sum := by decide
  have hdescent : baseEnd_1511769 < baseStart_1511769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511774 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1511774 : Nat := 118140960795 + 1511774 * 2 ^ 59
def prefixEnd_1511774 : Nat := 4983230072969 + 3 ^ 40 * 1511774 * 2
def baseEnd_1511774 : Nat := 258755567656757803657495

theorem tailTrace_1511774 : CollatzResearch.WordTrace tailWord_1511774 prefixEnd_1511774 258755567656757803657495 := by
  unfold tailWord_1511774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892365953138557911089797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36759285083405642192478917 6892365953138557911089797)
  ·
    refine ⟨1292318616213479608329337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6892365953138557911089797 1292318616213479608329337)
    ·
      refine ⟨969238962160109706247003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292318616213479608329337 969238962160109706247003)
      ·
        refine ⟨1453858443240164559370505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969238962160109706247003 1453858443240164559370505)
        ·
          refine ⟨1090393832430123419527879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1453858443240164559370505 1090393832430123419527879)
          ·
            refine ⟨1635590748645185129291819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090393832430123419527879 1635590748645185129291819)
            ·
              refine ⟨2453386122967777693937729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635590748645185129291819 2453386122967777693937729)
              ·
                refine ⟨1840039592225833270453297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453386122967777693937729 1840039592225833270453297)
                ·
                  refine ⟨1380029694169374952839973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840039592225833270453297 1380029694169374952839973)
                  ·
                    refine ⟨258755567656757803657495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380029694169374952839973 258755567656757803657495)
                    ·
                      rfl

theorem cell23_1511774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1511774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511774 prefixEnd_1511774 := by exact prefixLift 1511774
  have htrace : WordTrace (prefixWord ++ tailWord_1511774) baseStart_1511774 baseEnd_1511774 := by
    simpa [prefixWord, tailWord_1511774, baseEnd_1511774] using wordTrace_append hprefix tailTrace_1511774
  have hstable : (prefixWord ++ tailWord_1511774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511774).length < 2 ^ (prefixWord ++ tailWord_1511774).sum := by decide
  have hdescent : baseEnd_1511774 < baseStart_1511774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511792 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 7]
def baseStart_1511792 : Nat := 118140960795 + 1511792 * 2 ^ 59
def prefixEnd_1511792 : Nat := 4983230072969 + 3 ^ 40 * 1511792 * 2
def baseEnd_1511792 : Nat := 86252882846894926727489

theorem tailTrace_1511792 : CollatzResearch.WordTrace tailWord_1511792 prefixEnd_1511792 86252882846894926727489 := by
  unfold tailWord_1511792
  simp only [CollatzResearch.WordTrace]
  refine ⟨27569792069521626181436815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36759722759362168241915753 27569792069521626181436815)
  ·
    refine ⟨41354688104282439272155223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27569792069521626181436815 41354688104282439272155223)
    ·
      refine ⟨62032032156423658908232835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41354688104282439272155223 62032032156423658908232835)
      ·
        refine ⟨93048048234635488362349253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62032032156423658908232835 93048048234635488362349253)
        ·
          refine ⟨17446509043994154067940485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93048048234635488362349253 17446509043994154067940485)
          ·
            refine ⟨3271220445748903887738841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17446509043994154067940485 3271220445748903887738841)
            ·
              refine ⟨2453415334311677915804131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271220445748903887738841 2453415334311677915804131)
              ·
                refine ⟨3680123001467516873706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453415334311677915804131 3680123001467516873706197)
                ·
                  refine ⟨86252882846894926727489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3680123001467516873706197 86252882846894926727489)
                  ·
                    rfl

theorem cell23_1511792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_1511792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511792 prefixEnd_1511792 := by exact prefixLift 1511792
  have htrace : WordTrace (prefixWord ++ tailWord_1511792) baseStart_1511792 baseEnd_1511792 := by
    simpa [prefixWord, tailWord_1511792, baseEnd_1511792] using wordTrace_append hprefix tailTrace_1511792
  have hstable : (prefixWord ++ tailWord_1511792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511792).length < 2 ^ (prefixWord ++ tailWord_1511792).sum := by decide
  have hdescent : baseEnd_1511792 < baseStart_1511792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511803 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 2, 2, 2]
def baseStart_1511803 : Nat := 118140960795 + 1511803 * 2 ^ 59
def prefixEnd_1511803 : Nat := 4983230072969 + 3 ^ 40 * 1511803 * 2
def baseEnd_1511803 : Nat := 776281593909253797509851

theorem tailTrace_1511803 : CollatzResearch.WordTrace tailWord_1511803 prefixEnd_1511803 776281593909253797509851 := by
  unfold tailWord_1511803
  simp only [CollatzResearch.WordTrace]
  refine ⟨55139985342003401241524063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36759990228002267494349375 55139985342003401241524063)
  ·
    refine ⟨82709978013005101862286095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55139985342003401241524063 82709978013005101862286095)
    ·
      refine ⟨124064967019507652793429143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82709978013005101862286095 124064967019507652793429143)
      ·
        refine ⟨186097450529261479190143715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124064967019507652793429143 186097450529261479190143715)
        ·
          refine ⟨279146175793892218785215573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186097450529261479190143715 279146175793892218785215573)
          ·
            refine ⟨3271244247584674438889245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 279146175793892218785215573 3271244247584674438889245)
            ·
              refine ⟨1226716592844252914583467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3271244247584674438889245 1226716592844252914583467)
              ·
                refine ⟨1840074889266379371875201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226716592844252914583467 1840074889266379371875201)
                ·
                  refine ⟨1380056166949784528906401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840074889266379371875201 1380056166949784528906401)
                  ·
                    refine ⟨1035042125212338396679801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380056166949784528906401 1035042125212338396679801)
                    ·
                      refine ⟨776281593909253797509851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035042125212338396679801 776281593909253797509851)
                      ·
                        rfl

theorem cell23_1511803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 2, 2, 2].length) (baseStart_1511803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511803 prefixEnd_1511803 := by exact prefixLift 1511803
  have htrace : WordTrace (prefixWord ++ tailWord_1511803) baseStart_1511803 baseEnd_1511803 := by
    simpa [prefixWord, tailWord_1511803, baseEnd_1511803] using wordTrace_append hprefix tailTrace_1511803
  have hstable : (prefixWord ++ tailWord_1511803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511803).length < 2 ^ (prefixWord ++ tailWord_1511803).sum := by decide
  have hdescent : baseEnd_1511803 < baseStart_1511803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511879 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1511879 : Nat := 118140960795 + 1511879 * 2 ^ 59
def prefixEnd_1511879 : Nat := 4983230072969 + 3 ^ 40 * 1511879 * 2
def baseEnd_1511879 : Nat := 776320618438995500159501

theorem tailTrace_1511879 : CollatzResearch.WordTrace tailWord_1511879 prefixEnd_1511879 776320618438995500159501 := by
  unfold tailWord_1511879
  simp only [CollatzResearch.WordTrace]
  refine ⟨55142757289728066221290691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36761838193152044147527127 55142757289728066221290691)
  ·
    refine ⟨82714135934592099331936037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55142757289728066221290691 82714135934592099331936037)
    ·
      refine ⟨15508900487736018624738007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82714135934592099331936037 15508900487736018624738007)
      ·
        refine ⟨23263350731604027937107011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508900487736018624738007 23263350731604027937107011)
        ·
          refine ⟨34895026097406041905660517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23263350731604027937107011 34895026097406041905660517)
          ·
            refine ⟨6542817393263632857311347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34895026097406041905660517 6542817393263632857311347)
            ·
              refine ⟨9814226089895449285967021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6542817393263632857311347 9814226089895449285967021)
              ·
                refine ⟨3680334783710793482237633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9814226089895449285967021 3680334783710793482237633)
                ·
                  refine ⟨2760251087783095111678225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680334783710793482237633 2760251087783095111678225)
                  ·
                    refine ⟨2070188315837321333758669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2760251087783095111678225 2070188315837321333758669)
                    ·
                      refine ⟨776320618438995500159501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2070188315837321333758669 776320618438995500159501)
                      ·
                        rfl

theorem cell23_1511879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1511879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511879 prefixEnd_1511879 := by exact prefixLift 1511879
  have htrace : WordTrace (prefixWord ++ tailWord_1511879) baseStart_1511879 baseEnd_1511879 := by
    simpa [prefixWord, tailWord_1511879, baseEnd_1511879] using wordTrace_append hprefix tailTrace_1511879
  have hstable : (prefixWord ++ tailWord_1511879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511879).length < 2 ^ (prefixWord ++ tailWord_1511879).sum := by decide
  have hdescent : baseEnd_1511879 < baseStart_1511879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511886 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_1511886 : Nat := 118140960795 + 1511886 * 2 ^ 59
def prefixEnd_1511886 : Nat := 4983230072969 + 3 ^ 40 * 1511886 * 2
def baseEnd_1511886 : Nat := 258774737601192324257323

theorem tailTrace_1511886 : CollatzResearch.WordTrace tailWord_1511886 prefixEnd_1511886 258774737601192324257323 := by
  unfold tailWord_1511886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892876575087838302099439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36762008400468470944530341 6892876575087838302099439)
  ·
    refine ⟨10339314862631757453149159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892876575087838302099439 10339314862631757453149159)
    ·
      refine ⟨15508972293947636179723739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339314862631757453149159 15508972293947636179723739)
      ·
        refine ⟨23263458440921454269585609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508972293947636179723739 23263458440921454269585609)
        ·
          refine ⟨17447593830691090702189207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23263458440921454269585609 17447593830691090702189207)
          ·
            refine ⟨26171390746036636053283811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17447593830691090702189207 26171390746036636053283811)
            ·
              refine ⟨39257086119054954079925717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26171390746036636053283811 39257086119054954079925717)
              ·
                refine ⟨920087955915350486248259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39257086119054954079925717 920087955915350486248259)
                ·
                  refine ⟨1380131933873025729372389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920087955915350486248259 1380131933873025729372389)
                  ·
                    refine ⟨258774737601192324257323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380131933873025729372389 258774737601192324257323)
                    ·
                      rfl

theorem cell23_1511886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_1511886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511886 prefixEnd_1511886 := by exact prefixLift 1511886
  have htrace : WordTrace (prefixWord ++ tailWord_1511886) baseStart_1511886 baseEnd_1511886 := by
    simpa [prefixWord, tailWord_1511886, baseEnd_1511886] using wordTrace_append hprefix tailTrace_1511886
  have hstable : (prefixWord ++ tailWord_1511886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511886).length < 2 ^ (prefixWord ++ tailWord_1511886).sum := by decide
  have hdescent : baseEnd_1511886 < baseStart_1511886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511903 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 1, 4]
def baseStart_1511903 : Nat := 118140960795 + 1511903 * 2 ^ 59
def prefixEnd_1511903 : Nat := 4983230072969 + 3 ^ 40 * 1511903 * 2
def baseEnd_1511903 : Nat := 258777647324901135419797

theorem tailTrace_1511903 : CollatzResearch.WordTrace tailWord_1511903 prefixEnd_1511903 258777647324901135419797 := by
  unfold tailWord_1511903
  simp only [CollatzResearch.WordTrace]
  refine ⟨55143632641641118320164363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36762421761094078880109575 55143632641641118320164363)
  ·
    refine ⟨82715448962461677480246545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55143632641641118320164363 82715448962461677480246545)
    ·
      refine ⟨62036586721846258110184909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82715448962461677480246545 62036586721846258110184909)
      ·
        refine ⟨23263720020692346791319341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62036586721846258110184909 23263720020692346791319341)
        ·
          refine ⟨8723895007759630046744753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23263720020692346791319341 8723895007759630046744753)
          ·
            refine ⟨6542921255819722535058565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8723895007759630046744753 6542921255819722535058565)
            ·
              refine ⟨1226797735466197975323481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6542921255819722535058565 1226797735466197975323481)
              ·
                refine ⟨920098301599648481492611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226797735466197975323481 920098301599648481492611)
                ·
                  refine ⟨1380147452399472722238917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920098301599648481492611 1380147452399472722238917)
                  ·
                    refine ⟨258777647324901135419797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380147452399472722238917 258777647324901135419797)
                    ·
                      rfl

theorem cell23_1511903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 4].length) (baseStart_1511903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511903 prefixEnd_1511903 := by exact prefixLift 1511903
  have htrace : WordTrace (prefixWord ++ tailWord_1511903) baseStart_1511903 baseEnd_1511903 := by
    simpa [prefixWord, tailWord_1511903, baseEnd_1511903] using wordTrace_append hprefix tailTrace_1511903
  have hstable : (prefixWord ++ tailWord_1511903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511903).length < 2 ^ (prefixWord ++ tailWord_1511903).sum := by decide
  have hdescent : baseEnd_1511903 < baseStart_1511903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511919 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 5, 2]
def baseStart_1511919 : Nat := 118140960795 + 1511919 * 2 ^ 59
def prefixEnd_1511919 : Nat := 4983230072969 + 3 ^ 40 * 1511919 * 2
def baseEnd_1511919 : Nat := 776341157665175343659317

theorem tailTrace_1511919 : CollatzResearch.WordTrace tailWord_1511919 prefixEnd_1511919 776341157665175343659317 := by
  unfold tailWord_1511919
  simp only [CollatzResearch.WordTrace]
  refine ⟨55144216209583153052746811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36762810806388768701831207 55144216209583153052746811)
  ·
    refine ⟨82716324314374729579120217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55144216209583153052746811 82716324314374729579120217)
    ·
      refine ⟨62037243235781047184340163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82716324314374729579120217 62037243235781047184340163)
      ·
        refine ⟨93055864853671570776510245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62037243235781047184340163 93055864853671570776510245)
        ·
          refine ⟨17447974660063419520595671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93055864853671570776510245 17447974660063419520595671)
          ·
            refine ⟨26171961990095129280893507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17447974660063419520595671 26171961990095129280893507)
            ·
              refine ⟨39257942985142693921340261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26171961990095129280893507 39257942985142693921340261)
              ·
                refine ⟨7360864309714255110251299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39257942985142693921340261 7360864309714255110251299)
                ·
                  refine ⟨11041296464571382665376949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360864309714255110251299 11041296464571382665376949)
                  ·
                    refine ⟨1035121543553567124879089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11041296464571382665376949 1035121543553567124879089)
                    ·
                      refine ⟨776341157665175343659317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035121543553567124879089 776341157665175343659317)
                      ·
                        rfl

theorem cell23_1511919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 5, 2].length) (baseStart_1511919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511919 prefixEnd_1511919 := by exact prefixLift 1511919
  have htrace : WordTrace (prefixWord ++ tailWord_1511919) baseStart_1511919 baseEnd_1511919 := by
    simpa [prefixWord, tailWord_1511919, baseEnd_1511919] using wordTrace_append hprefix tailTrace_1511919
  have hstable : (prefixWord ++ tailWord_1511919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511919).length < 2 ^ (prefixWord ++ tailWord_1511919).sum := by decide
  have hdescent : baseEnd_1511919 < baseStart_1511919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511969 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1511969 : Nat := 118140960795 + 1511969 * 2 ^ 59
def prefixEnd_1511969 : Nat := 4983230072969 + 3 ^ 40 * 1511969 * 2
def baseEnd_1511969 : Nat := 776366831697900148034087

theorem tailTrace_1511969 : CollatzResearch.WordTrace tailWord_1511969 prefixEnd_1511969 776366831697900148034087 := by
  unfold tailWord_1511969
  simp only [CollatzResearch.WordTrace]
  refine ⟨55146039859402011592066961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36764026572934674394711307 55146039859402011592066961)
  ·
    refine ⟨41359529894551508694050221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55146039859402011592066961 41359529894551508694050221)
    ·
      refine ⟨15509823710456815760268833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41359529894551508694050221 15509823710456815760268833)
      ·
        refine ⟨11632367782842611820201625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15509823710456815760268833 11632367782842611820201625)
        ·
          refine ⟨8724275837131958865151219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11632367782842611820201625 8724275837131958865151219)
          ·
            refine ⟨13086413755697938297726829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8724275837131958865151219 13086413755697938297726829)
            ·
              refine ⟨4907405158386726861647561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13086413755697938297726829 4907405158386726861647561)
              ·
                refine ⟨3680553868790045146235671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4907405158386726861647561 3680553868790045146235671)
                ·
                  refine ⟨5520830803185067719353507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680553868790045146235671 5520830803185067719353507)
                  ·
                    refine ⟨8281246204777601579030261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5520830803185067719353507 8281246204777601579030261)
                    ·
                      refine ⟨776366831697900148034087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8281246204777601579030261 776366831697900148034087)
                      ·
                        rfl

theorem cell23_1511969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1511969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511969 prefixEnd_1511969 := by exact prefixLift 1511969
  have htrace : WordTrace (prefixWord ++ tailWord_1511969) baseStart_1511969 baseEnd_1511969 := by
    simpa [prefixWord, tailWord_1511969, baseEnd_1511969] using wordTrace_append hprefix tailTrace_1511969
  have hstable : (prefixWord ++ tailWord_1511969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511969).length < 2 ^ (prefixWord ++ tailWord_1511969).sum := by decide
  have hdescent : baseEnd_1511969 < baseStart_1511969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511976 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1511976 : Nat := 118140960795 + 1511976 * 2 ^ 59
def prefixEnd_1511976 : Nat := 4983230072969 + 3 ^ 40 * 1511976 * 2
def baseEnd_1511976 : Nat := 258790142020827206882185

theorem tailTrace_1511976 : CollatzResearch.WordTrace tailWord_1511976 prefixEnd_1511976 258790142020827206882185 := by
  unfold tailWord_1511976
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573147585188325893785891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36764196780251101191714521 27573147585188325893785891)
  ·
    refine ⟨41359721377782488840678837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27573147585188325893785891 41359721377782488840678837)
    ·
      refine ⟨3877473879167108328813641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41359721377782488840678837 3877473879167108328813641)
      ·
        refine ⟨2908105409375331246610231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3877473879167108328813641 2908105409375331246610231)
        ·
          refine ⟨4362158114062996869915347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908105409375331246610231 4362158114062996869915347)
          ·
            refine ⟨6543237171094495304873021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362158114062996869915347 6543237171094495304873021)
            ·
              refine ⟨2453713939160435739327383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6543237171094495304873021 2453713939160435739327383)
              ·
                refine ⟨3680570908740653608991075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453713939160435739327383 3680570908740653608991075)
                ·
                  refine ⟨5520856363110980413486613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680570908740653608991075 5520856363110980413486613)
                  ·
                    refine ⟨258790142020827206882185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5520856363110980413486613 258790142020827206882185)
                    ·
                      rfl

theorem cell23_1511976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1511976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511976 prefixEnd_1511976 := by exact prefixLift 1511976
  have htrace : WordTrace (prefixWord ++ tailWord_1511976) baseStart_1511976 baseEnd_1511976 := by
    simpa [prefixWord, tailWord_1511976, baseEnd_1511976] using wordTrace_append hprefix tailTrace_1511976
  have hstable : (prefixWord ++ tailWord_1511976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511976).length < 2 ^ (prefixWord ++ tailWord_1511976).sum := by decide
  have hdescent : baseEnd_1511976 < baseStart_1511976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511986 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1511986 : Nat := 118140960795 + 1511986 * 2 ^ 59
def prefixEnd_1511986 : Nat := 4983230072969 + 3 ^ 40 * 1511986 * 2
def baseEnd_1511986 : Nat := 776375560869026581521509

theorem tailTrace_1511986 : CollatzResearch.WordTrace tailWord_1511986 prefixEnd_1511986 776375560869026581521509 := by
  unfold tailWord_1511986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786664975085105873858953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36764439933560282330290541 13786664975085105873858953)
  ·
    refine ⟨10339998731313829405394215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13786664975085105873858953 10339998731313829405394215)
    ·
      refine ⟨15509998096970744108091323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339998731313829405394215 15509998096970744108091323)
      ·
        refine ⟨23264997145456116162136985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15509998096970744108091323 23264997145456116162136985)
        ·
          refine ⟨17448747859092087121602739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23264997145456116162136985 17448747859092087121602739)
          ·
            refine ⟨26173121788638130682404109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17448747859092087121602739 26173121788638130682404109)
            ·
              refine ⟨9814920670739299005901541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26173121788638130682404109 9814920670739299005901541)
              ·
                refine ⟨1840297625763618563606539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9814920670739299005901541 1840297625763618563606539)
                ·
                  refine ⟨2760446438645427845409809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840297625763618563606539 2760446438645427845409809)
                  ·
                    refine ⟨2070334828984070884057357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2760446438645427845409809 2070334828984070884057357)
                    ·
                      refine ⟨776375560869026581521509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2070334828984070884057357 776375560869026581521509)
                      ·
                        rfl

theorem cell23_1511986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1511986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511986 prefixEnd_1511986 := by exact prefixLift 1511986
  have htrace : WordTrace (prefixWord ++ tailWord_1511986) baseStart_1511986 baseEnd_1511986 := by
    simpa [prefixWord, tailWord_1511986, baseEnd_1511986] using wordTrace_append hprefix tailTrace_1511986
  have hstable : (prefixWord ++ tailWord_1511986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511986).length < 2 ^ (prefixWord ++ tailWord_1511986).sum := by decide
  have hdescent : baseEnd_1511986 < baseStart_1511986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511999 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_1511999 : Nat := 118140960795 + 1511999 * 2 ^ 59
def prefixEnd_1511999 : Nat := 4983230072969 + 3 ^ 40 * 1511999 * 2
def baseEnd_1511999 : Nat := 776382236117535030658949

theorem tailTrace_1511999 : CollatzResearch.WordTrace tailWord_1511999 prefixEnd_1511999 776382236117535030658949 := by
  unfold tailWord_1511999
  simp only [CollatzResearch.WordTrace]
  refine ⟨55147134049293326715659051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36764756032862217810439367 55147134049293326715659051)
  ·
    refine ⟨82720701073939990073488577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55147134049293326715659051 82720701073939990073488577)
    ·
      refine ⟨62040525805454992555116433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82720701073939990073488577 62040525805454992555116433)
      ·
        refine ⟨46530394354091244416337325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62040525805454992555116433 46530394354091244416337325)
        ·
          refine ⟨17448897882784216656126497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46530394354091244416337325 17448897882784216656126497)
          ·
            refine ⟨13086673412088162492094873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17448897882784216656126497 13086673412088162492094873)
            ·
              refine ⟨9815005059066121869071155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13086673412088162492094873 9815005059066121869071155)
              ·
                refine ⟨14722507588599182803606733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9815005059066121869071155 14722507588599182803606733)
                ·
                  refine ⟨5520940345724693551352525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14722507588599182803606733 5520940345724693551352525)
                  ·
                    refine ⟨2070352629646760081757197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5520940345724693551352525 2070352629646760081757197)
                    ·
                      refine ⟨776382236117535030658949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2070352629646760081757197 776382236117535030658949)
                      ·
                        rfl

theorem cell23_1511999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_1511999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1511999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1511999 prefixEnd_1511999 := by exact prefixLift 1511999
  have htrace : WordTrace (prefixWord ++ tailWord_1511999) baseStart_1511999 baseEnd_1511999 := by
    simpa [prefixWord, tailWord_1511999, baseEnd_1511999] using wordTrace_append hprefix tailTrace_1511999
  have hstable : (prefixWord ++ tailWord_1511999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511999).length < 2 ^ (prefixWord ++ tailWord_1511999).sum := by decide
  have hdescent : baseEnd_1511999 < baseStart_1511999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512000 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 1, 2, 2]
def baseStart_1512000 : Nat := 118140960795 + 1512000 * 2 ^ 59
def prefixEnd_1512000 : Nat := 4983230072969 + 3 ^ 40 * 1512000 * 2
def baseEnd_1512000 : Nat := 776382749598189526746445

theorem tailTrace_1512000 : CollatzResearch.WordTrace tailWord_1512000 prefixEnd_1512000 776382749598189526746445 := by
  unfold tailWord_1512000
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573585261144851943222727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36764780348193135924296969 27573585261144851943222727)
  ·
    refine ⟨41360377891717277914834091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27573585261144851943222727 41360377891717277914834091)
    ·
      refine ⟨62040566837575916872251137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41360377891717277914834091 62040566837575916872251137)
      ·
        refine ⟨46530425128181937654188353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62040566837575916872251137 46530425128181937654188353)
        ·
          refine ⟨34897818846136453240641265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46530425128181937654188353 34897818846136453240641265)
          ·
            refine ⟨26173364134602339930480949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34897818846136453240641265 26173364134602339930480949)
            ·
              refine ⟨2453752887618969368482589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26173364134602339930480949 2453752887618969368482589)
              ·
                refine ⟨920157332857113513180971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453752887618969368482589 920157332857113513180971)
                ·
                  refine ⟨1380235999285670269771457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920157332857113513180971 1380235999285670269771457)
                  ·
                    refine ⟨1035176999464252702328593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380235999285670269771457 1035176999464252702328593)
                    ·
                      refine ⟨776382749598189526746445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035176999464252702328593 776382749598189526746445)
                      ·
                        rfl

theorem cell23_1512000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_1512000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512000 prefixEnd_1512000 := by exact prefixLift 1512000
  have htrace : WordTrace (prefixWord ++ tailWord_1512000) baseStart_1512000 baseEnd_1512000 := by
    simpa [prefixWord, tailWord_1512000, baseEnd_1512000] using wordTrace_append hprefix tailTrace_1512000
  have hstable : (prefixWord ++ tailWord_1512000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512000).length < 2 ^ (prefixWord ++ tailWord_1512000).sum := by decide
  have hdescent : baseEnd_1512000 < baseStart_1512000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512006 : List Nat := [6, 1, 1, 1, 2, 1, 11]
def baseStart_1512006 : Nat := 118140960795 + 1512006 * 2 ^ 59
def prefixEnd_1512006 : Nat := 4983230072969 + 3 ^ 40 * 1512006 * 2
def baseEnd_1512006 : Nat := 9585010252865635842857

theorem tailTrace_1512006 : CollatzResearch.WordTrace tailWord_1512006 prefixEnd_1512006 9585010252865635842857 := by
  unfold tailWord_1512006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723355917508373965973871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36764926240178644607442581 1723355917508373965973871)
  ·
    refine ⟨2585033876262560948960807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1723355917508373965973871 2585033876262560948960807)
    ·
      refine ⟨3877550814393841423441211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585033876262560948960807 3877550814393841423441211)
      ·
        refine ⟨5816326221590762135161817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877550814393841423441211 5816326221590762135161817)
        ·
          refine ⟨4362244666193071601371363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5816326221590762135161817 4362244666193071601371363)
          ·
            refine ⟨6543366999289607402057045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362244666193071601371363 6543366999289607402057045)
            ·
              refine ⟨9585010252865635842857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6543366999289607402057045 9585010252865635842857)
              ·
                rfl

theorem cell23_1512006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 11].length) (baseStart_1512006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512006 prefixEnd_1512006 := by exact prefixLift 1512006
  have htrace : WordTrace (prefixWord ++ tailWord_1512006) baseStart_1512006 baseEnd_1512006 := by
    simpa [prefixWord, tailWord_1512006, baseEnd_1512006] using wordTrace_append hprefix tailTrace_1512006
  have hstable : (prefixWord ++ tailWord_1512006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512006).length < 2 ^ (prefixWord ++ tailWord_1512006).sum := by decide
  have hdescent : baseEnd_1512006 < baseStart_1512006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512017 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 1, 2, 2]
def baseStart_1512017 : Nat := 118140960795 + 1512017 * 2 ^ 59
def prefixEnd_1512017 : Nat := 4983230072969 + 3 ^ 40 * 1512017 * 2
def baseEnd_1512017 : Nat := 776391478769315960233867

theorem tailTrace_1512017 : CollatzResearch.WordTrace tailWord_1512017 prefixEnd_1512017 776391478769315960233867 := by
  unfold tailWord_1512017
  simp only [CollatzResearch.WordTrace]
  refine ⟨55147790563228115789814305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36765193708818743859876203 55147790563228115789814305)
  ·
    refine ⟨41360842922421086842360729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55147790563228115789814305 41360842922421086842360729)
    ·
      refine ⟨31020632191815815131770547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41360842922421086842360729 31020632191815815131770547)
      ·
        refine ⟨46530948287723722697655821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31020632191815815131770547 46530948287723722697655821)
        ·
          refine ⟨17449105607896396011620933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46530948287723722697655821 17449105607896396011620933)
          ·
            refine ⟨3271707301480574252178925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17449105607896396011620933 3271707301480574252178925)
            ·
              refine ⟨1226890238055215344567097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3271707301480574252178925 1226890238055215344567097)
              ·
                refine ⟨920167678541411508425323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226890238055215344567097 920167678541411508425323)
                ·
                  refine ⟨1380251517812117262637985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920167678541411508425323 1380251517812117262637985)
                  ·
                    refine ⟨1035188638359087946978489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380251517812117262637985 1035188638359087946978489)
                    ·
                      refine ⟨776391478769315960233867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035188638359087946978489 776391478769315960233867)
                      ·
                        rfl

theorem cell23_1512017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_1512017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512017 prefixEnd_1512017 := by exact prefixLift 1512017
  have htrace : WordTrace (prefixWord ++ tailWord_1512017) baseStart_1512017 baseEnd_1512017 := by
    simpa [prefixWord, tailWord_1512017, baseEnd_1512017] using wordTrace_append hprefix tailTrace_1512017
  have hstable : (prefixWord ++ tailWord_1512017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512017).length < 2 ^ (prefixWord ++ tailWord_1512017).sum := by decide
  have hdescent : baseEnd_1512017 < baseStart_1512017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512033 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_1512033 : Nat := 118140960795 + 1512033 * 2 ^ 59
def prefixEnd_1512033 : Nat := 4983230072969 + 3 ^ 40 * 1512033 * 2
def baseEnd_1512033 : Nat := 776399694459787897633793

theorem tailTrace_1512033 : CollatzResearch.WordTrace tailWord_1512033 prefixEnd_1512033 776399694459787897633793 := by
  unfold tailWord_1512033
  simp only [CollatzResearch.WordTrace]
  refine ⟨55148374131170150522396753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36765582754113433681597835 55148374131170150522396753)
  ·
    refine ⟨41361280598377612891797565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55148374131170150522396753 41361280598377612891797565)
    ·
      refine ⟨15510480224391604834424087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41361280598377612891797565 15510480224391604834424087)
      ·
        refine ⟨23265720336587407251636131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15510480224391604834424087 23265720336587407251636131)
        ·
          refine ⟨34898580504881110877454197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23265720336587407251636131 34898580504881110877454197)
          ·
            refine ⟨3271741922332604144761331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34898580504881110877454197 3271741922332604144761331)
            ·
              refine ⟨4907612883498906217141997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271741922332604144761331 4907612883498906217141997)
              ·
                refine ⟨1840354831312089831428249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4907612883498906217141997 1840354831312089831428249)
                ·
                  refine ⟨1380266123484067373571187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840354831312089831428249 1380266123484067373571187)
                  ·
                    refine ⟨2070399185226101060356781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380266123484067373571187 2070399185226101060356781)
                    ·
                      refine ⟨776399694459787897633793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2070399185226101060356781 776399694459787897633793)
                      ·
                        rfl

theorem cell23_1512033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_1512033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512033 prefixEnd_1512033 := by exact prefixLift 1512033
  have htrace : WordTrace (prefixWord ++ tailWord_1512033) baseStart_1512033 baseEnd_1512033 := by
    simpa [prefixWord, tailWord_1512033, baseEnd_1512033] using wordTrace_append hprefix tailTrace_1512033
  have hstable : (prefixWord ++ tailWord_1512033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512033).length < 2 ^ (prefixWord ++ tailWord_1512033).sum := by decide
  have hdescent : baseEnd_1512033 < baseStart_1512033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512056 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_1512056 : Nat := 118140960795 + 1512056 * 2 ^ 59
def prefixEnd_1512056 : Nat := 4983230072969 + 3 ^ 40 * 1512056 * 2
def baseEnd_1512056 : Nat := 776411504514841307646187

theorem tailTrace_1512056 : CollatzResearch.WordTrace tailWord_1512056 prefixEnd_1512056 776411504514841307646187 := by
  unfold tailWord_1512056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27574606505043412725242011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36766142006724550300322681 27574606505043412725242011)
  ·
    refine ⟨41361909757565119087863017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27574606505043412725242011 41361909757565119087863017)
    ·
      refine ⟨31021432318173839315897263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41361909757565119087863017 31021432318173839315897263)
      ·
        refine ⟨46532148477260758973845895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31021432318173839315897263 46532148477260758973845895)
        ·
          refine ⟨69798222715891138460768843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46532148477260758973845895 69798222715891138460768843)
          ·
            refine ⟨104697334073836707691153265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69798222715891138460768843 104697334073836707691153265)
            ·
              refine ⟨78523000555377530768364949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104697334073836707691153265 78523000555377530768364949)
              ·
                refine ⟨3680765651033321754767107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78523000555377530768364949 3680765651033321754767107)
                ·
                  refine ⟨5521148476549982632150661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680765651033321754767107 5521148476549982632150661)
                  ·
                    refine ⟨1035215339353121743528249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5521148476549982632150661 1035215339353121743528249)
                    ·
                      refine ⟨776411504514841307646187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035215339353121743528249 776411504514841307646187)
                      ·
                        rfl

theorem cell23_1512056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_1512056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512056 prefixEnd_1512056 := by exact prefixLift 1512056
  have htrace : WordTrace (prefixWord ++ tailWord_1512056) baseStart_1512056 baseEnd_1512056 := by
    simpa [prefixWord, tailWord_1512056, baseEnd_1512056] using wordTrace_append hprefix tailTrace_1512056
  have hstable : (prefixWord ++ tailWord_1512056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512056).length < 2 ^ (prefixWord ++ tailWord_1512056).sum := by decide
  have hdescent : baseEnd_1512056 < baseStart_1512056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512096 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 7]
def baseStart_1512096 : Nat := 118140960795 + 1512096 * 2 ^ 59
def prefixEnd_1512096 : Nat := 4983230072969 + 3 ^ 40 * 1512096 * 2
def baseEnd_1512096 : Nat := 86270227082335683460667

theorem tailTrace_1512096 : CollatzResearch.WordTrace tailWord_1512096 prefixEnd_1512096 86270227082335683460667 := by
  unfold tailWord_1512096
  simp only [CollatzResearch.WordTrace]
  refine ⟨27575335964970956140970071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36767114619961274854626761 27575335964970956140970071)
  ·
    refine ⟨41363003947456434211455107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27575335964970956140970071 41363003947456434211455107)
    ·
      refine ⟨62044505921184651317182661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41363003947456434211455107 62044505921184651317182661)
      ·
        refine ⟨11633344860222122121971749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62044505921184651317182661 11633344860222122121971749)
        ·
          refine ⟨2181252161291647897869703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11633344860222122121971749 2181252161291647897869703)
          ·
            refine ⟨3271878241937471846804555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181252161291647897869703 3271878241937471846804555)
            ·
              refine ⟨4907817362906207770206833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271878241937471846804555 4907817362906207770206833)
              ·
                refine ⟨3680863022179655827655125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4907817362906207770206833 3680863022179655827655125)
                ·
                  refine ⟨86270227082335683460667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3680863022179655827655125 86270227082335683460667)
                  ·
                    rfl

theorem cell23_1512096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_1512096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512096 prefixEnd_1512096 := by exact prefixLift 1512096
  have htrace : WordTrace (prefixWord ++ tailWord_1512096) baseStart_1512096 baseEnd_1512096 := by
    simpa [prefixWord, tailWord_1512096, baseEnd_1512096] using wordTrace_append hprefix tailTrace_1512096
  have hstable : (prefixWord ++ tailWord_1512096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512096).length < 2 ^ (prefixWord ++ tailWord_1512096).sum := by decide
  have hdescent : baseEnd_1512096 < baseStart_1512096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512126 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1512126 : Nat := 118140960795 + 1512126 * 2 ^ 59
def prefixEnd_1512126 : Nat := 4983230072969 + 3 ^ 40 * 1512126 * 2
def baseEnd_1512126 : Nat := 258815816053552011256955

theorem tailTrace_1512126 : CollatzResearch.WordTrace tailWord_1512126 prefixEnd_1512126 258815816053552011256955 := by
  unfold tailWord_1512126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893970764979153425691529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36767844079888818270354821 6893970764979153425691529)
  ·
    refine ⟨5170478073734365069268647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6893970764979153425691529 5170478073734365069268647)
    ·
      refine ⟨7755717110601547603902971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170478073734365069268647 7755717110601547603902971)
      ·
        refine ⟨11633575665902321405854457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755717110601547603902971 11633575665902321405854457)
        ·
          refine ⟨8725181749426741054390843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11633575665902321405854457 8725181749426741054390843)
          ·
            refine ⟨13087772624140111581586265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8725181749426741054390843 13087772624140111581586265)
            ·
              refine ⟨9815829468105083686189699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13087772624140111581586265 9815829468105083686189699)
              ·
                refine ⟨14723744202157625529284549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9815829468105083686189699 14723744202157625529284549)
                ·
                  refine ⟨2760702037904554786740853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14723744202157625529284549 2760702037904554786740853)
                  ·
                    refine ⟨258815816053552011256955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2760702037904554786740853 258815816053552011256955)
                    ·
                      rfl

theorem cell23_1512126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1512126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512126 prefixEnd_1512126 := by exact prefixLift 1512126
  have htrace : WordTrace (prefixWord ++ tailWord_1512126) baseStart_1512126 baseEnd_1512126 := by
    simpa [prefixWord, tailWord_1512126, baseEnd_1512126] using wordTrace_append hprefix tailTrace_1512126
  have hstable : (prefixWord ++ tailWord_1512126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512126).length < 2 ^ (prefixWord ++ tailWord_1512126).sum := by decide
  have hdescent : baseEnd_1512126 < baseStart_1512126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512141 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1512141 : Nat := 118140960795 + 1512141 * 2 ^ 59
def prefixEnd_1512141 : Nat := 4983230072969 + 3 ^ 40 * 1512141 * 2
def baseEnd_1512141 : Nat := 776455150370473475083297

theorem tailTrace_1512141 : CollatzResearch.WordTrace tailWord_1512141 prefixEnd_1512141 776455150370473475083297 := by
  unfold tailWord_1512141
  simp only [CollatzResearch.WordTrace]
  refine ⟨55152313214778884967328277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36768208809852589978218851 55152313214778884967328277)
  ·
    refine ⟨2585264681942760232843513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55152313214778884967328277 2585264681942760232843513)
    ·
      refine ⟨1938948511457070174632635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2585264681942760232843513 1938948511457070174632635)
      ·
        refine ⟨2908422767185605261948953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938948511457070174632635 2908422767185605261948953)
        ·
          refine ⟨2181317075389203946461715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2908422767185605261948953 2181317075389203946461715)
          ·
            refine ⟨3271975613083805919692573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181317075389203946461715 3271975613083805919692573)
            ·
              refine ⟨1226990854906427219884715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3271975613083805919692573 1226990854906427219884715)
              ·
                refine ⟨1840486282359640829827073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226990854906427219884715 1840486282359640829827073)
                ·
                  refine ⟨1380364711769730622370305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840486282359640829827073 1380364711769730622370305)
                  ·
                    refine ⟨1035273533827297966777729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380364711769730622370305 1035273533827297966777729)
                    ·
                      refine ⟨776455150370473475083297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035273533827297966777729 776455150370473475083297)
                      ·
                        rfl

theorem cell23_1512141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1512141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512141 prefixEnd_1512141 := by exact prefixLift 1512141
  have htrace : WordTrace (prefixWord ++ tailWord_1512141) baseStart_1512141 baseEnd_1512141 := by
    simpa [prefixWord, tailWord_1512141, baseEnd_1512141] using wordTrace_append hprefix tailTrace_1512141
  have hstable : (prefixWord ++ tailWord_1512141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512141).length < 2 ^ (prefixWord ++ tailWord_1512141).sum := by decide
  have hdescent : baseEnd_1512141 < baseStart_1512141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512169 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 8]
def baseStart_1512169 : Nat := 118140960795 + 1512169 * 2 ^ 59
def prefixEnd_1512169 : Nat := 4983230072969 + 3 ^ 40 * 1512169 * 2
def baseEnd_1512169 : Nat := 86274391980977707281463

theorem tailTrace_1512169 : CollatzResearch.WordTrace tailWord_1512169 prefixEnd_1512169 86274391980977707281463 := by
  unfold tailWord_1512169
  simp only [CollatzResearch.WordTrace]
  refine ⟨55153334458677445749347561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36768889639118297166231707 55153334458677445749347561)
  ·
    refine ⟨41365000844008084312010671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55153334458677445749347561 41365000844008084312010671)
    ·
      refine ⟨62047501266012126468016007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41365000844008084312010671 62047501266012126468016007)
      ·
        refine ⟨93071251899018189702024011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62047501266012126468016007 93071251899018189702024011)
        ·
          refine ⟨139606877848527284553036017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93071251899018189702024011 139606877848527284553036017)
          ·
            refine ⟨104705158386395463414777013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139606877848527284553036017 104705158386395463414777013)
            ·
              refine ⟨9816108598724574695135345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104705158386395463414777013 9816108598724574695135345)
              ·
                refine ⟨7362081449043431021351509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9816108598724574695135345 7362081449043431021351509)
                ·
                  refine ⟨86274391980977707281463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7362081449043431021351509 86274391980977707281463)
                  ·
                    rfl

theorem cell23_1512169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_1512169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512169 prefixEnd_1512169 := by exact prefixLift 1512169
  have htrace : WordTrace (prefixWord ++ tailWord_1512169) baseStart_1512169 baseEnd_1512169 := by
    simpa [prefixWord, tailWord_1512169, baseEnd_1512169] using wordTrace_append hprefix tailTrace_1512169
  have hstable : (prefixWord ++ tailWord_1512169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512169).length < 2 ^ (prefixWord ++ tailWord_1512169).sum := by decide
  have hdescent : baseEnd_1512169 < baseStart_1512169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512190 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1512190 : Nat := 118140960795 + 1512190 * 2 ^ 59
def prefixEnd_1512190 : Nat := 4983230072969 + 3 ^ 40 * 1512190 * 2
def baseEnd_1512190 : Nat := 258826770307514594456857

theorem tailTrace_1512190 : CollatzResearch.WordTrace tailWord_1512190 prefixEnd_1512190 258826770307514594456857 := by
  unfold tailWord_1512190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6894262548950170791982753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36769400261067577557241349 6894262548950170791982753)
  ·
    refine ⟨5170696911712628093987065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6894262548950170791982753 5170696911712628093987065)
    ·
      refine ⟨3878022683784471070490299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170696911712628093987065 3878022683784471070490299)
      ·
        refine ⟨5817034025676706605735449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878022683784471070490299 5817034025676706605735449)
        ·
          refine ⟨4362775519257529954301587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817034025676706605735449 4362775519257529954301587)
          ·
            refine ⟨6544163278886294931452381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4362775519257529954301587 6544163278886294931452381)
            ·
              refine ⟨2454061229582360599294643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6544163278886294931452381 2454061229582360599294643)
              ·
                refine ⟨3681091844373540898941965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454061229582360599294643 3681091844373540898941965)
                ·
                  refine ⟨1380409441640077837103237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3681091844373540898941965 1380409441640077837103237)
                  ·
                    refine ⟨258826770307514594456857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380409441640077837103237 258826770307514594456857)
                    ·
                      rfl

theorem cell23_1512190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1512190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512190 prefixEnd_1512190 := by exact prefixLift 1512190
  have htrace : WordTrace (prefixWord ++ tailWord_1512190) baseStart_1512190 baseEnd_1512190 := by
    simpa [prefixWord, tailWord_1512190, baseEnd_1512190] using wordTrace_append hprefix tailTrace_1512190
  have hstable : (prefixWord ++ tailWord_1512190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512190).length < 2 ^ (prefixWord ++ tailWord_1512190).sum := by decide
  have hdescent : baseEnd_1512190 < baseStart_1512190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512213 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_1512213 : Nat := 118140960795 + 1512213 * 2 ^ 59
def prefixEnd_1512213 : Nat := 4983230072969 + 3 ^ 40 * 1512213 * 2
def baseEnd_1512213 : Nat := 776492120977597193382965

theorem tailTrace_1512213 : CollatzResearch.WordTrace tailWord_1512213 prefixEnd_1512213 776492120977597193382965 := by
  unfold tailWord_1512213
  simp only [CollatzResearch.WordTrace]
  refine ⟨55154939270518041263949293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36769959513678694175966195 55154939270518041263949293)
  ·
    refine ⟨20683102226444265473980985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55154939270518041263949293 20683102226444265473980985)
    ·
      refine ⟨15512326669833199105485739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20683102226444265473980985 15512326669833199105485739)
      ·
        refine ⟨23268490004749798658228609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15512326669833199105485739 23268490004749798658228609)
        ·
          refine ⟨17451367503562348993671457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23268490004749798658228609 17451367503562348993671457)
          ·
            refine ⟨13088525627671761745253593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17451367503562348993671457 13088525627671761745253593)
            ·
              refine ⟨9816394220753821308940195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13088525627671761745253593 9816394220753821308940195)
              ·
                refine ⟨14724591331130731963410293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9816394220753821308940195 14724591331130731963410293)
                ·
                  refine ⟨1380430437293506121569715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14724591331130731963410293 1380430437293506121569715)
                  ·
                    refine ⟨2070645655940259182354573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380430437293506121569715 2070645655940259182354573)
                    ·
                      refine ⟨776492120977597193382965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2070645655940259182354573 776492120977597193382965)
                      ·
                        rfl

theorem cell23_1512213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_1512213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512213 prefixEnd_1512213 := by exact prefixLift 1512213
  have htrace : WordTrace (prefixWord ++ tailWord_1512213) baseStart_1512213 baseEnd_1512213 := by
    simpa [prefixWord, tailWord_1512213, baseEnd_1512213] using wordTrace_append hprefix tailTrace_1512213
  have hstable : (prefixWord ++ tailWord_1512213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512213).length < 2 ^ (prefixWord ++ tailWord_1512213).sum := by decide
  have hdescent : baseEnd_1512213 < baseStart_1512213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512237 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1512237 : Nat := 118140960795 + 1512237 * 2 ^ 59
def prefixEnd_1512237 : Nat := 4983230072969 + 3 ^ 40 * 1512237 * 2
def baseEnd_1512237 : Nat := 86278271612589455498095

theorem tailTrace_1512237 : CollatzResearch.WordTrace tailWord_1512237 prefixEnd_1512237 86278271612589455498095 := by
  unfold tailWord_1512237
  simp only [CollatzResearch.WordTrace]
  refine ⟨55155814622431093362822965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36770543081620728908548643 55155814622431093362822965)
  ·
    refine ⟨5170857620852915002764653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55155814622431093362822965 5170857620852915002764653)
    ·
      refine ⟨1939071607819843126036745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5170857620852915002764653 1939071607819843126036745)
      ·
        refine ⟨1454303705864882344527559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1939071607819843126036745 1454303705864882344527559)
        ·
          refine ⟨2181455558797323516791339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454303705864882344527559 2181455558797323516791339)
          ·
            refine ⟨3272183338195985275187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181455558797323516791339 3272183338195985275187009)
            ·
              refine ⟨2454137503646988956390257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272183338195985275187009 2454137503646988956390257)
              ·
                refine ⟨1840603127735241717292693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2454137503646988956390257 1840603127735241717292693)
                ·
                  refine ⟨86278271612589455498095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1840603127735241717292693 86278271612589455498095)
                  ·
                    rfl

theorem cell23_1512237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1512237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512237 prefixEnd_1512237 := by exact prefixLift 1512237
  have htrace : WordTrace (prefixWord ++ tailWord_1512237) baseStart_1512237 baseEnd_1512237 := by
    simpa [prefixWord, tailWord_1512237, baseEnd_1512237] using wordTrace_append hprefix tailTrace_1512237
  have hstable : (prefixWord ++ tailWord_1512237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512237).length < 2 ^ (prefixWord ++ tailWord_1512237).sum := by decide
  have hdescent : baseEnd_1512237 < baseStart_1512237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512256 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_1512256 : Nat := 118140960795 + 1512256 * 2 ^ 59
def prefixEnd_1512256 : Nat := 4983230072969 + 3 ^ 40 * 1512256 * 2
def baseEnd_1512256 : Nat := 776514200645740525145267

theorem tailTrace_1512256 : CollatzResearch.WordTrace tailWord_1512256 prefixEnd_1512256 776514200645740525145267 := by
  unfold tailWord_1512256
  simp only [CollatzResearch.WordTrace]
  refine ⟨27578253804681129803882311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36771005072908173071843081 27578253804681129803882311)
  ·
    refine ⟨41367380707021694705823467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27578253804681129803882311 41367380707021694705823467)
    ·
      refine ⟨62051071060532542058735201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41367380707021694705823467 62051071060532542058735201)
      ·
        refine ⟨46538303295399406544051401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62051071060532542058735201 46538303295399406544051401)
        ·
          refine ⟨34903727471549554908038551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46538303295399406544051401 34903727471549554908038551)
          ·
            refine ⟨52355591207324332362057827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34903727471549554908038551 52355591207324332362057827)
            ·
              refine ⟨78533386810986498543086741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52355591207324332362057827 78533386810986498543086741)
              ·
                refine ⟨3681252506764992119207191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78533386810986498543086741 3681252506764992119207191)
                ·
                  refine ⟨5521878760147488178810787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3681252506764992119207191 5521878760147488178810787)
                  ·
                    refine ⟨8282818140221232268216181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5521878760147488178810787 8282818140221232268216181)
                    ·
                      refine ⟨776514200645740525145267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8282818140221232268216181 776514200645740525145267)
                      ·
                        rfl

theorem cell23_1512256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_1512256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512256 prefixEnd_1512256 := by exact prefixLift 1512256
  have htrace : WordTrace (prefixWord ++ tailWord_1512256) baseStart_1512256 baseEnd_1512256 := by
    simpa [prefixWord, tailWord_1512256, baseEnd_1512256] using wordTrace_append hprefix tailTrace_1512256
  have hstable : (prefixWord ++ tailWord_1512256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512256).length < 2 ^ (prefixWord ++ tailWord_1512256).sum := by decide
  have hdescent : baseEnd_1512256 < baseStart_1512256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512306 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1512306 : Nat := 118140960795 + 1512306 * 2 ^ 59
def prefixEnd_1512306 : Nat := 4983230072969 + 3 ^ 40 * 1512306 * 2
def baseEnd_1512306 : Nat := 258846624892821776506679

theorem tailTrace_1512306 : CollatzResearch.WordTrace tailWord_1512306 prefixEnd_1512306 258846624892821776506679 := by
  unfold tailWord_1512306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789582814795279536771193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36772220839454078764723181 13789582814795279536771193)
  ·
    refine ⟨10342187111096459652578395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13789582814795279536771193 10342187111096459652578395)
    ·
      refine ⟨15513280666644689478867593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10342187111096459652578395 15513280666644689478867593)
      ·
        refine ⟨11634960499983517109150695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15513280666644689478867593 11634960499983517109150695)
        ·
          refine ⟨17452440749975275663726043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11634960499983517109150695 17452440749975275663726043)
          ·
            refine ⟨26178661124962913495589065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17452440749975275663726043 26178661124962913495589065)
            ·
              refine ⟨19633995843722185121691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26178661124962913495589065 19633995843722185121691799)
              ·
                refine ⟨29450993765583277682537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19633995843722185121691799 29450993765583277682537699)
                ·
                  refine ⟨44176490648374916523806549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29450993765583277682537699 44176490648374916523806549)
                  ·
                    refine ⟨258846624892821776506679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44176490648374916523806549 258846624892821776506679)
                    ·
                      rfl

theorem cell23_1512306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1512306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512306 prefixEnd_1512306 := by exact prefixLift 1512306
  have htrace : WordTrace (prefixWord ++ tailWord_1512306) baseStart_1512306 baseEnd_1512306 := by
    simpa [prefixWord, tailWord_1512306, baseEnd_1512306] using wordTrace_append hprefix tailTrace_1512306
  have hstable : (prefixWord ++ tailWord_1512306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512306).length < 2 ^ (prefixWord ++ tailWord_1512306).sum := by decide
  have hdescent : baseEnd_1512306 < baseStart_1512306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512316 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1512316 : Nat := 118140960795 + 1512316 * 2 ^ 59
def prefixEnd_1512316 : Nat := 4983230072969 + 3 ^ 40 * 1512316 * 2
def baseEnd_1512316 : Nat := 776545009485010290394991

theorem tailTrace_1512316 : CollatzResearch.WordTrace tailWord_1512316 prefixEnd_1512316 776545009485010290394991 := by
  unfold tailWord_1512316
  simp only [CollatzResearch.WordTrace]
  refine ⟨27579347994572444927474401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36772463992763259903299201 27579347994572444927474401)
  ·
    refine ⟨20684510995929333695605801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27579347994572444927474401 20684510995929333695605801)
    ·
      refine ⟨15513383246947000271704351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20684510995929333695605801 15513383246947000271704351)
      ·
        refine ⟨23270074870420500407556527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15513383246947000271704351 23270074870420500407556527)
        ·
          refine ⟨34905112305630750611334791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23270074870420500407556527 34905112305630750611334791)
          ·
            refine ⟨52357668458446125917002187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34905112305630750611334791 52357668458446125917002187)
            ·
              refine ⟨78536502687669188875503281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52357668458446125917002187 78536502687669188875503281)
              ·
                refine ⟨58902377015751891656627461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78536502687669188875503281 58902377015751891656627461)
                ·
                  refine ⟨11044195690453479685617649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58902377015751891656627461 11044195690453479685617649)
                  ·
                    refine ⟨8283146767840109764213237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11044195690453479685617649 8283146767840109764213237)
                    ·
                      refine ⟨776545009485010290394991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8283146767840109764213237 776545009485010290394991)
                      ·
                        rfl

theorem cell23_1512316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1512316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512316 prefixEnd_1512316 := by exact prefixLift 1512316
  have htrace : WordTrace (prefixWord ++ tailWord_1512316) baseStart_1512316 baseEnd_1512316 := by
    simpa [prefixWord, tailWord_1512316, baseEnd_1512316] using wordTrace_append hprefix tailTrace_1512316
  have hstable : (prefixWord ++ tailWord_1512316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512316).length < 2 ^ (prefixWord ++ tailWord_1512316).sum := by decide
  have hdescent : baseEnd_1512316 < baseStart_1512316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512338 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1512338 : Nat := 118140960795 + 1512338 * 2 ^ 59
def prefixEnd_1512338 : Nat := 4983230072969 + 3 ^ 40 * 1512338 * 2
def baseEnd_1512338 : Nat := 776556306059409204319891

theorem tailTrace_1512338 : CollatzResearch.WordTrace tailWord_1512338 prefixEnd_1512338 776556306059409204319891 := by
  unfold tailWord_1512338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789874598766296903062417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36772998930043458408166445 13789874598766296903062417)
  ·
    refine ⟨10342405949074722677296813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13789874598766296903062417 10342405949074722677296813)
    ·
      refine ⟨3878402230903021003986305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10342405949074722677296813 3878402230903021003986305)
      ·
        refine ⟨2908801673177265752989729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3878402230903021003986305 2908801673177265752989729)
        ·
          refine ⟨2181601254882949314742297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2908801673177265752989729 2181601254882949314742297)
          ·
            refine ⟨1636200941162211986056723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181601254882949314742297 1636200941162211986056723)
            ·
              refine ⟨2454301411743317979085085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636200941162211986056723 2454301411743317979085085)
              ·
                refine ⟨920363029403744242156907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2454301411743317979085085 920363029403744242156907)
                ·
                  refine ⟨1380544544105616363235361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920363029403744242156907 1380544544105616363235361)
                  ·
                    refine ⟨1035408408079212272426521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380544544105616363235361 1035408408079212272426521)
                    ·
                      refine ⟨776556306059409204319891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035408408079212272426521 776556306059409204319891)
                      ·
                        rfl

theorem cell23_1512338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1512338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512338 prefixEnd_1512338 := by exact prefixLift 1512338
  have htrace : WordTrace (prefixWord ++ tailWord_1512338) baseStart_1512338 baseEnd_1512338 := by
    simpa [prefixWord, tailWord_1512338, baseEnd_1512338] using wordTrace_append hprefix tailTrace_1512338
  have hstable : (prefixWord ++ tailWord_1512338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512338).length < 2 ^ (prefixWord ++ tailWord_1512338).sum := by decide
  have hdescent : baseEnd_1512338 < baseStart_1512338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512373 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1512373 : Nat := 118140960795 + 1512373 * 2 ^ 59
def prefixEnd_1512373 : Nat := 4983230072969 + 3 ^ 40 * 1512373 * 2
def baseEnd_1512373 : Nat := 776574277882316567382229

theorem tailTrace_1512373 : CollatzResearch.WordTrace tailWord_1512373 prefixEnd_1512373 776574277882316567382229 := by
  unfold tailWord_1512373
  simp only [CollatzResearch.WordTrace]
  refine ⟨55160774949938388589773773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36773849966625592393182515 55160774949938388589773773)
  ·
    refine ⟨20685290606226895721165165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55160774949938388589773773 20685290606226895721165165)
    ·
      refine ⟨7756983977335085895436937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20685290606226895721165165 7756983977335085895436937)
      ·
        refine ⟨5817737983001314421577703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756983977335085895436937 5817737983001314421577703)
        ·
          refine ⟨8726606974501971632366555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817737983001314421577703 8726606974501971632366555)
          ·
            refine ⟨13089910461752957448549833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8726606974501971632366555 13089910461752957448549833)
            ·
              refine ⟨9817432846314718086412375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13089910461752957448549833 9817432846314718086412375)
              ·
                refine ⟨14726149269472077129618563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9817432846314718086412375 14726149269472077129618563)
                ·
                  refine ⟨22089223904208115694427845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14726149269472077129618563 22089223904208115694427845)
                  ·
                    refine ⟨4141729482039021692705221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22089223904208115694427845 4141729482039021692705221)
                    ·
                      refine ⟨776574277882316567382229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4141729482039021692705221 776574277882316567382229)
                      ·
                        rfl

theorem cell23_1512373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1512373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512373 prefixEnd_1512373 := by exact prefixLift 1512373
  have htrace : WordTrace (prefixWord ++ tailWord_1512373) baseStart_1512373 baseEnd_1512373 := by
    simpa [prefixWord, tailWord_1512373, baseEnd_1512373] using wordTrace_append hprefix tailTrace_1512373
  have hstable : (prefixWord ++ tailWord_1512373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512373).length < 2 ^ (prefixWord ++ tailWord_1512373).sum := by decide
  have hdescent : baseEnd_1512373 < baseStart_1512373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512381 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_1512381 : Nat := 118140960795 + 1512381 * 2 ^ 59
def prefixEnd_1512381 : Nat := 4983230072969 + 3 ^ 40 * 1512381 * 2
def baseEnd_1512381 : Nat := 776578385727552536082193

theorem tailTrace_1512381 : CollatzResearch.WordTrace tailWord_1512381 prefixEnd_1512381 776578385727552536082193 := by
  unfold tailWord_1512381
  simp only [CollatzResearch.WordTrace]
  refine ⟨55161066733909405956064997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36774044489272937304043331 55161066733909405956064997)
  ·
    refine ⟨10342700012608013616762187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55161066733909405956064997 10342700012608013616762187)
    ·
      refine ⟨15514050018912020425143281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10342700012608013616762187 15514050018912020425143281)
      ·
        refine ⟨11635537514184015318857461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15514050018912020425143281 11635537514184015318857461)
        ·
          refine ⟨1090831641954751436142887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11635537514184015318857461 1090831641954751436142887)
          ·
            refine ⟨1636247462932127154214331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090831641954751436142887 1636247462932127154214331)
            ·
              refine ⟨2454371194398190731321497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636247462932127154214331 2454371194398190731321497)
              ·
                refine ⟨1840778395798643048491123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2454371194398190731321497 1840778395798643048491123)
                ·
                  refine ⟨2761167593697964572736685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840778395798643048491123 2761167593697964572736685)
                  ·
                    refine ⟨1035437847636736714776257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2761167593697964572736685 1035437847636736714776257)
                    ·
                      refine ⟨776578385727552536082193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035437847636736714776257 776578385727552536082193)
                      ·
                        rfl

theorem cell23_1512381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_1512381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512381 prefixEnd_1512381 := by exact prefixLift 1512381
  have htrace : WordTrace (prefixWord ++ tailWord_1512381) baseStart_1512381 baseEnd_1512381 := by
    simpa [prefixWord, tailWord_1512381, baseEnd_1512381] using wordTrace_append hprefix tailTrace_1512381
  have hstable : (prefixWord ++ tailWord_1512381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512381).length < 2 ^ (prefixWord ++ tailWord_1512381).sum := by decide
  have hdescent : baseEnd_1512381 < baseStart_1512381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512487 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1512487 : Nat := 118140960795 + 1512487 * 2 ^ 59
def prefixEnd_1512487 : Nat := 4983230072969 + 3 ^ 40 * 1512487 * 2
def baseEnd_1512487 : Nat := 776632814676929121356705

theorem tailTrace_1512487 : CollatzResearch.WordTrace tailWord_1512487 prefixEnd_1512487 776632814676929121356705 := by
  unfold tailWord_1512487
  simp only [CollatzResearch.WordTrace]
  refine ⟨55164932871525386059423715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36776621914350257372949143 55164932871525386059423715)
  ·
    refine ⟨82747399307288079089135573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55164932871525386059423715 82747399307288079089135573)
    ·
      refine ⟨1939392171264564353651615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 82747399307288079089135573 1939392171264564353651615)
      ·
        refine ⟨2909088256896846530477423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939392171264564353651615 2909088256896846530477423)
        ·
          refine ⟨4363632385345269795716135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909088256896846530477423 4363632385345269795716135)
          ·
            refine ⟨6545448578017904693574203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363632385345269795716135 6545448578017904693574203)
            ·
              refine ⟨9818172867026857040361305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545448578017904693574203 9818172867026857040361305)
              ·
                refine ⟨7363629650270142780270979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9818172867026857040361305 7363629650270142780270979)
                ·
                  refine ⟨11045444475405214170406469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7363629650270142780270979 11045444475405214170406469)
                  ·
                    refine ⟨2071020839138477656951213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11045444475405214170406469 2071020839138477656951213)
                    ·
                      refine ⟨776632814676929121356705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071020839138477656951213 776632814676929121356705)
                      ·
                        rfl

theorem cell23_1512487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1512487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512487 prefixEnd_1512487 := by exact prefixLift 1512487
  have htrace : WordTrace (prefixWord ++ tailWord_1512487) baseStart_1512487 baseEnd_1512487 := by
    simpa [prefixWord, tailWord_1512487, baseEnd_1512487] using wordTrace_append hprefix tailTrace_1512487
  have hstable : (prefixWord ++ tailWord_1512487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512487).length < 2 ^ (prefixWord ++ tailWord_1512487).sum := by decide
  have hdescent : baseEnd_1512487 < baseStart_1512487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512520 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1512520 : Nat := 118140960795 + 1512520 * 2 ^ 59
def prefixEnd_1512520 : Nat := 4983230072969 + 3 ^ 40 * 1512520 * 2
def baseEnd_1512520 : Nat := 258883253179509164081351

theorem tailTrace_1512520 : CollatzResearch.WordTrace tailWord_1512520 prefixEnd_1512520 258883253179509164081351 := by
  unfold tailWord_1512520
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583068240202916347687507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36777424320270555130250009 27583068240202916347687507)
  ·
    refine ⟨41374602360304374521531261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27583068240202916347687507 41374602360304374521531261)
    ·
      refine ⟨15515475885114140445574223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41374602360304374521531261 15515475885114140445574223)
      ·
        refine ⟨23273213827671210668361335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15515475885114140445574223 23273213827671210668361335)
        ·
          refine ⟨34909820741506816002542003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23273213827671210668361335 34909820741506816002542003)
          ·
            refine ⟨52364731112260224003813005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34909820741506816002542003 52364731112260224003813005)
            ·
              refine ⟨19636774167097584001429877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52364731112260224003813005 19636774167097584001429877)
              ·
                refine ⟨1840947578165398500134051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19636774167097584001429877 1840947578165398500134051)
                ·
                  refine ⟨2761421367248097750201077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840947578165398500134051 2761421367248097750201077)
                  ·
                    refine ⟨258883253179509164081351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2761421367248097750201077 258883253179509164081351)
                    ·
                      rfl

theorem cell23_1512520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1512520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512520 prefixEnd_1512520 := by exact prefixLift 1512520
  have htrace : WordTrace (prefixWord ++ tailWord_1512520) baseStart_1512520 baseEnd_1512520 := by
    simpa [prefixWord, tailWord_1512520, baseEnd_1512520] using wordTrace_append hprefix tailTrace_1512520
  have hstable : (prefixWord ++ tailWord_1512520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512520).length < 2 ^ (prefixWord ++ tailWord_1512520).sum := by decide
  have hdescent : baseEnd_1512520 < baseStart_1512520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512541 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 6]
def baseStart_1512541 : Nat := 118140960795 + 1512541 * 2 ^ 59
def prefixEnd_1512541 : Nat := 4983230072969 + 3 ^ 40 * 1512541 * 2
def baseEnd_1512541 : Nat := 86295615848030212231273

theorem tailTrace_1512541 : CollatzResearch.WordTrace tailWord_1512541 prefixEnd_1512541 86295615848030212231273 := by
  unfold tailWord_1512541
  simp only [CollatzResearch.WordTrace]
  refine ⟨55166902413329753281889477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36777934942219835521259651 55166902413329753281889477)
  ·
    refine ⟨10343794202499328740354277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55166902413329753281889477 10343794202499328740354277)
    ·
      refine ⟨1939461412968624138816427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10343794202499328740354277 1939461412968624138816427)
      ·
        refine ⟨2909192119452936208224641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939461412968624138816427 2909192119452936208224641)
        ·
          refine ⟨2181894089589702156168481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2909192119452936208224641 2181894089589702156168481)
          ·
            refine ⟨1636420567192276617126361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181894089589702156168481 1636420567192276617126361)
            ·
              refine ⟨1227315425394207462844771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636420567192276617126361 1227315425394207462844771)
              ·
                refine ⟨1840973138091311194267157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227315425394207462844771 1840973138091311194267157)
                ·
                  refine ⟨86295615848030212231273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1840973138091311194267157 86295615848030212231273)
                  ·
                    rfl

theorem cell23_1512541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_1512541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512541 prefixEnd_1512541 := by exact prefixLift 1512541
  have htrace : WordTrace (prefixWord ++ tailWord_1512541) baseStart_1512541 baseEnd_1512541 := by
    simpa [prefixWord, tailWord_1512541, baseEnd_1512541] using wordTrace_append hprefix tailTrace_1512541
  have hstable : (prefixWord ++ tailWord_1512541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512541).length < 2 ^ (prefixWord ++ tailWord_1512541).sum := by decide
  have hdescent : baseEnd_1512541 < baseStart_1512541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512554 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1512554 : Nat := 118140960795 + 1512554 * 2 ^ 59
def prefixEnd_1512554 : Nat := 4983230072969 + 3 ^ 40 * 1512554 * 2
def baseEnd_1512554 : Nat := 258889072626926786406299

theorem tailTrace_1512554 : CollatzResearch.WordTrace tailWord_1512554 prefixEnd_1512554 258889072626926786406299 := by
  unfold tailWord_1512554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13791844140570664125528179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36778251041521771001408477 13791844140570664125528179)
  ·
    refine ⟨20687766210855996188292269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13791844140570664125528179 20687766210855996188292269)
    ·
      refine ⟨7757912329070998570609601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20687766210855996188292269 7757912329070998570609601)
      ·
        refine ⟨5818434246803248927957201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7757912329070998570609601 5818434246803248927957201)
        ·
          refine ⟨4363825685102436695967901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5818434246803248927957201 4363825685102436695967901)
          ·
            refine ⟨1636434631913413760987963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4363825685102436695967901 1636434631913413760987963)
            ·
              refine ⟨2454651947870120641481945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636434631913413760987963 2454651947870120641481945)
              ·
                refine ⟨1840988960902590481111459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2454651947870120641481945 1840988960902590481111459)
                ·
                  refine ⟨2761483441353885721667189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840988960902590481111459 2761483441353885721667189)
                  ·
                    refine ⟨258889072626926786406299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2761483441353885721667189 258889072626926786406299)
                    ·
                      rfl

theorem cell23_1512554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1512554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512554 prefixEnd_1512554 := by exact prefixLift 1512554
  have htrace : WordTrace (prefixWord ++ tailWord_1512554) baseStart_1512554 baseEnd_1512554 := by
    simpa [prefixWord, tailWord_1512554, baseEnd_1512554] using wordTrace_append hprefix tailTrace_1512554
  have hstable : (prefixWord ++ tailWord_1512554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512554).length < 2 ^ (prefixWord ++ tailWord_1512554).sum := by decide
  have hdescent : baseEnd_1512554 < baseStart_1512554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512557 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1512557 : Nat := 118140960795 + 1512557 * 2 ^ 59
def prefixEnd_1512557 : Nat := 4983230072969 + 3 ^ 40 * 1512557 * 2
def baseEnd_1512557 : Nat := 776668758322743847481383

theorem tailTrace_1512557 : CollatzResearch.WordTrace tailWord_1512557 prefixEnd_1512557 776668758322743847481383 := by
  unfold tailWord_1512557
  simp only [CollatzResearch.WordTrace]
  refine ⟨55167485981271788014471925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36778323987514525342981283 55167485981271788014471925)
  ·
    refine ⟨5171951810744230126356743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55167485981271788014471925 5171951810744230126356743)
    ·
      refine ⟨7757927716116345189535115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171951810744230126356743 7757927716116345189535115)
      ·
        refine ⟨11636891574174517784302673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7757927716116345189535115 11636891574174517784302673)
        ·
          refine ⟨8727668680630888338227005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11636891574174517784302673 8727668680630888338227005)
          ·
            refine ⟨3272875755236583126835127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8727668680630888338227005 3272875755236583126835127)
            ·
              refine ⟨4909313632854874690252691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272875755236583126835127 4909313632854874690252691)
              ·
                refine ⟨7363970449282312035379037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909313632854874690252691 7363970449282312035379037)
                ·
                  refine ⟨2761488918480867013267139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7363970449282312035379037 2761488918480867013267139)
                  ·
                    refine ⟨4142233377721300519900709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761488918480867013267139 4142233377721300519900709)
                    ·
                      refine ⟨776668758322743847481383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4142233377721300519900709 776668758322743847481383)
                      ·
                        rfl

theorem cell23_1512557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1512557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512557 prefixEnd_1512557 := by exact prefixLift 1512557
  have htrace : WordTrace (prefixWord ++ tailWord_1512557) baseStart_1512557 baseEnd_1512557 := by
    simpa [prefixWord, tailWord_1512557, baseEnd_1512557] using wordTrace_append hprefix tailTrace_1512557
  have hstable : (prefixWord ++ tailWord_1512557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512557).length < 2 ^ (prefixWord ++ tailWord_1512557).sum := by decide
  have hdescent : baseEnd_1512557 < baseStart_1512557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512577 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1512577 : Nat := 118140960795 + 1512577 * 2 ^ 59
def prefixEnd_1512577 : Nat := 4983230072969 + 3 ^ 40 * 1512577 * 2
def baseEnd_1512577 : Nat := 776679027935833769231291

theorem tailTrace_1512577 : CollatzResearch.WordTrace tailWord_1512577 prefixEnd_1512577 776679027935833769231291 := by
  unfold tailWord_1512577
  simp only [CollatzResearch.WordTrace]
  refine ⟨55168215441199331430199985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36778810294132887620133323 55168215441199331430199985)
  ·
    refine ⟨41376161580899498572649989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55168215441199331430199985 41376161580899498572649989)
    ·
      refine ⟨7758030296418655982371873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41376161580899498572649989 7758030296418655982371873)
      ·
        refine ⟨5818522722313991986778905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7758030296418655982371873 5818522722313991986778905)
        ·
          refine ⟨4363892041735493990084179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5818522722313991986778905 4363892041735493990084179)
          ·
            refine ⟨6545838062603240985126269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363892041735493990084179 6545838062603240985126269)
            ·
              refine ⟨2454689273476215369422351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6545838062603240985126269 2454689273476215369422351)
              ·
                refine ⟨3682033910214323054133527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454689273476215369422351 3682033910214323054133527)
                ·
                  refine ⟨5523050865321484581200291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682033910214323054133527 5523050865321484581200291)
                  ·
                    refine ⟨8284576297982226871800437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5523050865321484581200291 8284576297982226871800437)
                    ·
                      refine ⟨776679027935833769231291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8284576297982226871800437 776679027935833769231291)
                      ·
                        rfl

theorem cell23_1512577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1512577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512577 prefixEnd_1512577 := by exact prefixLift 1512577
  have htrace : WordTrace (prefixWord ++ tailWord_1512577) baseStart_1512577 baseEnd_1512577 := by
    simpa [prefixWord, tailWord_1512577, baseEnd_1512577] using wordTrace_append hprefix tailTrace_1512577
  have hstable : (prefixWord ++ tailWord_1512577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512577).length < 2 ^ (prefixWord ++ tailWord_1512577).sum := by decide
  have hdescent : baseEnd_1512577 < baseStart_1512577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512641 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1512641 : Nat := 118140960795 + 1512641 * 2 ^ 59
def prefixEnd_1512641 : Nat := 4983230072969 + 3 ^ 40 * 1512641 * 2
def baseEnd_1512641 : Nat := 776711890697721518830997

theorem tailTrace_1512641 : CollatzResearch.WordTrace tailWord_1512641 prefixEnd_1512641 776711890697721518830997 := by
  unfold tailWord_1512641
  simp only [CollatzResearch.WordTrace]
  refine ⟨55170549712967470360529777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36780366475311646907019851 55170549712967470360529777)
  ·
    refine ⟨41377912284725602770397333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55170549712967470360529777 41377912284725602770397333)
    ·
      refine ⟨1939589638346512629862375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41377912284725602770397333 1939589638346512629862375)
      ·
        refine ⟨2909384457519768944793563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939589638346512629862375 2909384457519768944793563)
        ·
          refine ⟨4364076686279653417190345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909384457519768944793563 4364076686279653417190345)
          ·
            refine ⟨3273057514709740062892759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4364076686279653417190345 3273057514709740062892759)
            ·
              refine ⟨4909586272064610094339139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273057514709740062892759 4909586272064610094339139)
              ·
                refine ⟨7364379408096915141508709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909586272064610094339139 7364379408096915141508709)
                ·
                  refine ⟨1380821139018171589032883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7364379408096915141508709 1380821139018171589032883)
                  ·
                    refine ⟨2071231708527257383549325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380821139018171589032883 2071231708527257383549325)
                    ·
                      refine ⟨776711890697721518830997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071231708527257383549325 776711890697721518830997)
                      ·
                        rfl

theorem cell23_1512641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1512641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512641 prefixEnd_1512641 := by exact prefixLift 1512641
  have htrace : WordTrace (prefixWord ++ tailWord_1512641) baseStart_1512641 baseEnd_1512641 := by
    simpa [prefixWord, tailWord_1512641, baseEnd_1512641] using wordTrace_append hprefix tailTrace_1512641
  have hstable : (prefixWord ++ tailWord_1512641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512641).length < 2 ^ (prefixWord ++ tailWord_1512641).sum := by decide
  have hdescent : baseEnd_1512641 < baseStart_1512641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512647 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_1512647 : Nat := 118140960795 + 1512647 * 2 ^ 59
def prefixEnd_1512647 : Nat := 4983230072969 + 3 ^ 40 * 1512647 * 2
def baseEnd_1512647 : Nat := 776714971581648495355969

theorem tailTrace_1512647 : CollatzResearch.WordTrace tailWord_1512647 prefixEnd_1512647 776714971581648495355969 := by
  unfold tailWord_1512647
  simp only [CollatzResearch.WordTrace]
  refine ⟨55170768550945733385248195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36780512367297155590165463 55170768550945733385248195)
  ·
    refine ⟨82756152826418600077872293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55170768550945733385248195 82756152826418600077872293)
    ·
      refine ⟨15516778654953487514601055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82756152826418600077872293 15516778654953487514601055)
      ·
        refine ⟨23275167982430231271901583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15516778654953487514601055 23275167982430231271901583)
        ·
          refine ⟨34912751973645346907852375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23275167982430231271901583 34912751973645346907852375)
          ·
            refine ⟨52369127960468020361778563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34912751973645346907852375 52369127960468020361778563)
            ·
              refine ⟨78553691940702030542667845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52369127960468020361778563 78553691940702030542667845)
              ·
                refine ⟨14728817238881630726750221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78553691940702030542667845 14728817238881630726750221)
                ·
                  refine ⟨5523306464580611522531333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14728817238881630726750221 5523306464580611522531333)
                  ·
                    refine ⟨1035619962108864660474625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5523306464580611522531333 1035619962108864660474625)
                    ·
                      refine ⟨776714971581648495355969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035619962108864660474625 776714971581648495355969)
                      ·
                        rfl

theorem cell23_1512647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_1512647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512647 prefixEnd_1512647 := by exact prefixLift 1512647
  have htrace : WordTrace (prefixWord ++ tailWord_1512647) baseStart_1512647 baseEnd_1512647 := by
    simpa [prefixWord, tailWord_1512647, baseEnd_1512647] using wordTrace_append hprefix tailTrace_1512647
  have hstable : (prefixWord ++ tailWord_1512647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512647).length < 2 ^ (prefixWord ++ tailWord_1512647).sum := by decide
  have hdescent : baseEnd_1512647 < baseStart_1512647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512754 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1512754 : Nat := 118140960795 + 1512754 * 2 ^ 59
def prefixEnd_1512754 : Nat := 4983230072969 + 3 ^ 40 * 1512754 * 2
def baseEnd_1512754 : Nat := 776769914011679576717977

theorem tailTrace_1512754 : CollatzResearch.WordTrace tailWord_1512754 prefixEnd_1512754 776769914011679576717977 := by
  unfold tailWord_1512754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13793667790389522664848329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36783114107705393772928877 13793667790389522664848329)
  ·
    refine ⟨10345250842792141998636247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13793667790389522664848329 10345250842792141998636247)
    ·
      refine ⟨15517876264188212997954371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345250842792141998636247 15517876264188212997954371)
      ·
        refine ⟨23276814396282319496931557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15517876264188212997954371 23276814396282319496931557)
        ·
          refine ⟨4364402699302934905674667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23276814396282319496931557 4364402699302934905674667)
          ·
            refine ⟨6546604048954402358512001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364402699302934905674667 6546604048954402358512001)
            ·
              refine ⟨4909953036715801768884001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546604048954402358512001 4909953036715801768884001)
              ·
                refine ⟨3682464777536851326663001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4909953036715801768884001 3682464777536851326663001)
                ·
                  refine ⟨2761848583152638494997251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682464777536851326663001 2761848583152638494997251)
                  ·
                    refine ⟨4142772874728957742495877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2761848583152638494997251 4142772874728957742495877)
                    ·
                      refine ⟨776769914011679576717977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4142772874728957742495877 776769914011679576717977)
                      ·
                        rfl

theorem cell23_1512754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1512754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512754 prefixEnd_1512754 := by exact prefixLift 1512754
  have htrace : WordTrace (prefixWord ++ tailWord_1512754) baseStart_1512754 baseEnd_1512754 := by
    simpa [prefixWord, tailWord_1512754, baseEnd_1512754] using wordTrace_append hprefix tailTrace_1512754
  have hstable : (prefixWord ++ tailWord_1512754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512754).length < 2 ^ (prefixWord ++ tailWord_1512754).sum := by decide
  have hdescent : baseEnd_1512754 < baseStart_1512754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512777 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 6]
def baseStart_1512777 : Nat := 118140960795 + 1512777 * 2 ^ 59
def prefixEnd_1512777 : Nat := 4983230072969 + 3 ^ 40 * 1512777 * 2
def baseEnd_1512777 : Nat := 86309080451859220747819

theorem tailTrace_1512777 : CollatzResearch.WordTrace tailWord_1512777 prefixEnd_1512777 86309080451859220747819 := by
  unfold tailWord_1512777
  simp only [CollatzResearch.WordTrace]
  refine ⟨55175510040474765587480585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36783673360316510391653723 55175510040474765587480585)
  ·
    refine ⟨41381632530356074190610439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55175510040474765587480585 41381632530356074190610439)
    ·
      refine ⟨62072448795534111285915659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41381632530356074190610439 62072448795534111285915659)
      ·
        refine ⟨93108673193301166928873489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62072448795534111285915659 93108673193301166928873489)
        ·
          refine ⟨69831504894975875196655117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93108673193301166928873489 69831504894975875196655117)
          ·
            refine ⟨26186814335615953198745669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69831504894975875196655117 26186814335615953198745669)
            ·
              refine ⟨4910027687927991224764813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26186814335615953198745669 4910027687927991224764813)
              ·
                refine ⟨1841260382972996709286805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4910027687927991224764813 1841260382972996709286805)
                ·
                  refine ⟨86309080451859220747819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1841260382972996709286805 86309080451859220747819)
                  ·
                    rfl

theorem cell23_1512777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_1512777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512777 prefixEnd_1512777 := by exact prefixLift 1512777
  have htrace : WordTrace (prefixWord ++ tailWord_1512777) baseStart_1512777 baseEnd_1512777 := by
    simpa [prefixWord, tailWord_1512777, baseEnd_1512777] using wordTrace_append hprefix tailTrace_1512777
  have hstable : (prefixWord ++ tailWord_1512777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512777).length < 2 ^ (prefixWord ++ tailWord_1512777).sum := by decide
  have hdescent : baseEnd_1512777 < baseStart_1512777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512791 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_1512791 : Nat := 118140960795 + 1512791 * 2 ^ 59
def prefixEnd_1512791 : Nat := 4983230072969 + 3 ^ 40 * 1512791 * 2
def baseEnd_1512791 : Nat := 776788912795895931955307

theorem tailTrace_1512791 : CollatzResearch.WordTrace tailWord_1512791 prefixEnd_1512791 776788912795895931955307 := by
  unfold tailWord_1512791
  simp only [CollatzResearch.WordTrace]
  refine ⟨55176020662424045978490227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36784013774949363985660151 55176020662424045978490227)
  ·
    refine ⟨82764030993636068967735341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55176020662424045978490227 82764030993636068967735341)
    ·
      refine ⟨31036511622613525862900753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82764030993636068967735341 31036511622613525862900753)
      ·
        refine ⟨23277383716960144397175565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31036511622613525862900753 23277383716960144397175565)
        ·
          refine ⟨8729018893860054148940837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23277383716960144397175565 8729018893860054148940837)
          ·
            refine ⟨1636691042598760152926407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8729018893860054148940837 1636691042598760152926407)
            ·
              refine ⟨2455036563898140229389611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636691042598760152926407 2455036563898140229389611)
              ·
                refine ⟨3682554845847210344084417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455036563898140229389611 3682554845847210344084417)
                ·
                  refine ⟨2761916134385407758063313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682554845847210344084417 2761916134385407758063313)
                  ·
                    refine ⟨2071437100789055818547485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2761916134385407758063313 2071437100789055818547485)
                    ·
                      refine ⟨776788912795895931955307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071437100789055818547485 776788912795895931955307)
                      ·
                        rfl

theorem cell23_1512791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_1512791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512791 prefixEnd_1512791 := by exact prefixLift 1512791
  have htrace : WordTrace (prefixWord ++ tailWord_1512791) baseStart_1512791 baseEnd_1512791 := by
    simpa [prefixWord, tailWord_1512791, baseEnd_1512791] using wordTrace_append hprefix tailTrace_1512791
  have hstable : (prefixWord ++ tailWord_1512791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512791).length < 2 ^ (prefixWord ++ tailWord_1512791).sum := by decide
  have hdescent : baseEnd_1512791 < baseStart_1512791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512841 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_1512841 : Nat := 118140960795 + 1512841 * 2 ^ 59
def prefixEnd_1512841 : Nat := 4983230072969 + 3 ^ 40 * 1512841 * 2
def baseEnd_1512841 : Nat := 258938195609540245443359

theorem tailTrace_1512841 : CollatzResearch.WordTrace tailWord_1512841 prefixEnd_1512841 258938195609540245443359 := by
  unfold tailWord_1512841
  simp only [CollatzResearch.WordTrace]
  refine ⟨55177844312242904517810377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36785229541495269678540251 55177844312242904517810377)
  ·
    refine ⟨41383383234182178388357783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55177844312242904517810377 41383383234182178388357783)
    ·
      refine ⟨62075074851273267582536675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41383383234182178388357783 62075074851273267582536675)
      ·
        refine ⟨93112612276909901373805013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62075074851273267582536675 93112612276909901373805013)
        ·
          refine ⟨2182326850240075813448555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 93112612276909901373805013 2182326850240075813448555)
          ·
            refine ⟨3273490275360113720172833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182326850240075813448555 3273490275360113720172833)
            ·
              refine ⟨2455117706520085290129625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3273490275360113720172833 2455117706520085290129625)
              ·
                refine ⟨1841338279890063967597219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455117706520085290129625 1841338279890063967597219)
                ·
                  refine ⟨2762007419835095951395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841338279890063967597219 2762007419835095951395829)
                  ·
                    refine ⟨258938195609540245443359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2762007419835095951395829 258938195609540245443359)
                    ·
                      rfl

theorem cell23_1512841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_1512841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512841 prefixEnd_1512841 := by exact prefixLift 1512841
  have htrace : WordTrace (prefixWord ++ tailWord_1512841) baseStart_1512841 baseEnd_1512841 := by
    simpa [prefixWord, tailWord_1512841, baseEnd_1512841] using wordTrace_append hprefix tailTrace_1512841
  have hstable : (prefixWord ++ tailWord_1512841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512841).length < 2 ^ (prefixWord ++ tailWord_1512841).sum := by decide
  have hdescent : baseEnd_1512841 < baseStart_1512841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512844 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_1512844 : Nat := 118140960795 + 1512844 * 2 ^ 59
def prefixEnd_1512844 : Nat := 4983230072969 + 3 ^ 40 * 1512844 * 2
def baseEnd_1512844 : Nat := 776816127270584224592563

theorem tailTrace_1512844 : CollatzResearch.WordTrace tailWord_1512844 prefixEnd_1512844 776816127270584224592563 := by
  unfold tailWord_1512844
  simp only [CollatzResearch.WordTrace]
  refine ⟨27588976865616018015084793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36785302487488024020113057 27588976865616018015084793)
  ·
    refine ⟨20691732649212013511313595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27588976865616018015084793 20691732649212013511313595)
    ·
      refine ⟨31037598973818020266970393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20691732649212013511313595 31037598973818020266970393)
      ·
        refine ⟨23278199230363515200227795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31037598973818020266970393 23278199230363515200227795)
        ·
          refine ⟨34917298845545272800341693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23278199230363515200227795 34917298845545272800341693)
          ·
            refine ⟨13093987067079477300128135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34917298845545272800341693 13093987067079477300128135)
            ·
              refine ⟨19640980600619215950192203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13093987067079477300128135 19640980600619215950192203)
              ·
                refine ⟨29461470900928823925288305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19640980600619215950192203 29461470900928823925288305)
                ·
                  refine ⟨22096103175696617943966229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29461470900928823925288305 22096103175696617943966229)
                  ·
                    refine ⟨1035754836360778966123417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22096103175696617943966229 1035754836360778966123417)
                    ·
                      refine ⟨776816127270584224592563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035754836360778966123417 776816127270584224592563)
                      ·
                        rfl

theorem cell23_1512844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_1512844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512844 prefixEnd_1512844 := by exact prefixLift 1512844
  have htrace : WordTrace (prefixWord ++ tailWord_1512844) baseStart_1512844 baseEnd_1512844 := by
    simpa [prefixWord, tailWord_1512844, baseEnd_1512844] using wordTrace_append hprefix tailTrace_1512844
  have hstable : (prefixWord ++ tailWord_1512844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512844).length < 2 ^ (prefixWord ++ tailWord_1512844).sum := by decide
  have hdescent : baseEnd_1512844 < baseStart_1512844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512861 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1512861 : Nat := 118140960795 + 1512861 * 2 ^ 59
def prefixEnd_1512861 : Nat := 4983230072969 + 3 ^ 40 * 1512861 * 2
def baseEnd_1512861 : Nat := 776824856441710658079985

theorem tailTrace_1512861 : CollatzResearch.WordTrace tailWord_1512861 prefixEnd_1512861 776824856441710658079985 := by
  unfold tailWord_1512861
  simp only [CollatzResearch.WordTrace]
  refine ⟨55178573772170447933538437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36785715848113631955692291 55178573772170447933538437)
  ·
    refine ⟨10345982582281958987538457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55178573772170447933538437 10345982582281958987538457)
    ·
      refine ⟨7759486936711469240653843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10345982582281958987538457 7759486936711469240653843)
      ·
        refine ⟨11639230405067203860980765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7759486936711469240653843 11639230405067203860980765)
        ·
          refine ⟨4364711401900201447867787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11639230405067203860980765 4364711401900201447867787)
          ·
            refine ⟨6547067102850302171801681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364711401900201447867787 6547067102850302171801681)
            ·
              refine ⟨4910300327137726628851261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6547067102850302171801681 4910300327137726628851261)
              ·
                refine ⟨1841362622676647485819223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4910300327137726628851261 1841362622676647485819223)
                ·
                  refine ⟨2762043934014971228728835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841362622676647485819223 2762043934014971228728835)
                  ·
                    refine ⟨4143065901022456843093253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2762043934014971228728835 4143065901022456843093253)
                    ·
                      refine ⟨776824856441710658079985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4143065901022456843093253 776824856441710658079985)
                      ·
                        rfl

theorem cell23_1512861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1512861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512861 prefixEnd_1512861 := by exact prefixLift 1512861
  have htrace : WordTrace (prefixWord ++ tailWord_1512861) baseStart_1512861 baseEnd_1512861 := by
    simpa [prefixWord, tailWord_1512861, baseEnd_1512861] using wordTrace_append hprefix tailTrace_1512861
  have hstable : (prefixWord ++ tailWord_1512861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512861).length < 2 ^ (prefixWord ++ tailWord_1512861).sum := by decide
  have hdescent : baseEnd_1512861 < baseStart_1512861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512864 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1512864 : Nat := 118140960795 + 1512864 * 2 ^ 59
def prefixEnd_1512864 : Nat := 4983230072969 + 3 ^ 40 * 1512864 * 2
def baseEnd_1512864 : Nat := 776826396883674146342471

theorem tailTrace_1512864 : CollatzResearch.WordTrace tailWord_1512864 prefixEnd_1512864 776826396883674146342471 := by
  unfold tailWord_1512864
  simp only [CollatzResearch.WordTrace]
  refine ⟨27589341595579789722948823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36785788794106386297265097 27589341595579789722948823)
  ·
    refine ⟨41384012393369684584423235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27589341595579789722948823 41384012393369684584423235)
    ·
      refine ⟨62076018590054526876634853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41384012393369684584423235 62076018590054526876634853)
      ·
        refine ⟨11639253485635223789369035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62076018590054526876634853 11639253485635223789369035)
        ·
          refine ⟨17458880228452835684053553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11639253485635223789369035 17458880228452835684053553)
          ·
            refine ⟨13094160171339626763040165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17458880228452835684053553 13094160171339626763040165)
            ·
              refine ⟨2455155032126180018070031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13094160171339626763040165 2455155032126180018070031)
              ·
                refine ⟨3682732548189270027105047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455155032126180018070031 3682732548189270027105047)
                ·
                  refine ⟨5524098822283905040657571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682732548189270027105047 5524098822283905040657571)
                  ·
                    refine ⟨8286148233425857560986357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5524098822283905040657571 8286148233425857560986357)
                    ·
                      refine ⟨776826396883674146342471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8286148233425857560986357 776826396883674146342471)
                      ·
                        rfl

theorem cell23_1512864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1512864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512864 prefixEnd_1512864 := by exact prefixLift 1512864
  have htrace : WordTrace (prefixWord ++ tailWord_1512864) baseStart_1512864 baseEnd_1512864 := by
    simpa [prefixWord, tailWord_1512864, baseEnd_1512864] using wordTrace_append hprefix tailTrace_1512864
  have hstable : (prefixWord ++ tailWord_1512864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512864).length < 2 ^ (prefixWord ++ tailWord_1512864).sum := by decide
  have hdescent : baseEnd_1512864 < baseStart_1512864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512871 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1512871 : Nat := 118140960795 + 1512871 * 2 ^ 59
def prefixEnd_1512871 : Nat := 4983230072969 + 3 ^ 40 * 1512871 * 2
def baseEnd_1512871 : Nat := 258943330416085206318313

theorem tailTrace_1512871 : CollatzResearch.WordTrace tailWord_1512871 prefixEnd_1512871 258943330416085206318313 := by
  unfold tailWord_1512871
  simp only [CollatzResearch.WordTrace]
  refine ⟨55178938502134219641402467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36785959001422813094268311 55178938502134219641402467)
  ·
    refine ⟨82768407753201329462103701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55178938502134219641402467 82768407753201329462103701)
    ·
      refine ⟨3879769113431312318536111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82768407753201329462103701 3879769113431312318536111)
      ·
        refine ⟨5819653670146968477804167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3879769113431312318536111 5819653670146968477804167)
        ·
          refine ⟨8729480505220452716706251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819653670146968477804167 8729480505220452716706251)
          ·
            refine ⟨13094220757830679075059377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8729480505220452716706251 13094220757830679075059377)
            ·
              refine ⟨9820665568373009306294533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13094220757830679075059377 9820665568373009306294533)
              ·
                refine ⟨1841374794069939244930225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9820665568373009306294533 1841374794069939244930225)
                ·
                  refine ⟨1381031095552454433697669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841374794069939244930225 1381031095552454433697669)
                  ·
                    refine ⟨258943330416085206318313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381031095552454433697669 258943330416085206318313)
                    ·
                      rfl

theorem cell23_1512871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1512871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512871 prefixEnd_1512871 := by exact prefixLift 1512871
  have htrace : WordTrace (prefixWord ++ tailWord_1512871) baseStart_1512871 baseEnd_1512871 := by
    simpa [prefixWord, tailWord_1512871, baseEnd_1512871] using wordTrace_append hprefix tailTrace_1512871
  have hstable : (prefixWord ++ tailWord_1512871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512871).length < 2 ^ (prefixWord ++ tailWord_1512871).sum := by decide
  have hdescent : baseEnd_1512871 < baseStart_1512871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512872 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1512872 : Nat := 118140960795 + 1512872 * 2 ^ 59
def prefixEnd_1512872 : Nat := 4983230072969 + 3 ^ 40 * 1512872 * 2
def baseEnd_1512872 : Nat := 776830504728910115042435

theorem tailTrace_1512872 : CollatzResearch.WordTrace tailWord_1512872 prefixEnd_1512872 776830504728910115042435 := by
  unfold tailWord_1512872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27589487487565298406094435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36785983316753731208125913 27589487487565298406094435)
  ·
    refine ⟨41384231231347947609141653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27589487487565298406094435 41384231231347947609141653)
    ·
      refine ⟨1939885838969435044178515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41384231231347947609141653 1939885838969435044178515)
      ·
        refine ⟨2909828758454152566267773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939885838969435044178515 2909828758454152566267773)
        ·
          refine ⟨1091185784420307212350415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2909828758454152566267773 1091185784420307212350415)
          ·
            refine ⟨1636778676630460818525623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091185784420307212350415 1636778676630460818525623)
            ·
              refine ⟨2455168014945691227788435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636778676630460818525623 2455168014945691227788435)
              ·
                refine ⟨3682752022418536841682653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455168014945691227788435 3682752022418536841682653)
                ·
                  refine ⟨1381032008406951315630995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3682752022418536841682653 1381032008406951315630995)
                  ·
                    refine ⟨2071548012610426973446493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1381032008406951315630995 2071548012610426973446493)
                    ·
                      refine ⟨776830504728910115042435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071548012610426973446493 776830504728910115042435)
                      ·
                        rfl

theorem cell23_1512872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1512872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512872 prefixEnd_1512872 := by exact prefixLift 1512872
  have htrace : WordTrace (prefixWord ++ tailWord_1512872) baseStart_1512872 baseEnd_1512872 := by
    simpa [prefixWord, tailWord_1512872, baseEnd_1512872] using wordTrace_append hprefix tailTrace_1512872
  have hstable : (prefixWord ++ tailWord_1512872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512872).length < 2 ^ (prefixWord ++ tailWord_1512872).sum := by decide
  have hdescent : baseEnd_1512872 < baseStart_1512872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512887 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1512887 : Nat := 118140960795 + 1512887 * 2 ^ 59
def prefixEnd_1512887 : Nat := 4983230072969 + 3 ^ 40 * 1512887 * 2
def baseEnd_1512887 : Nat := 776838206938727556354865

theorem tailTrace_1512887 : CollatzResearch.WordTrace tailWord_1512887 prefixEnd_1512887 776838206938727556354865 := by
  unfold tailWord_1512887
  simp only [CollatzResearch.WordTrace]
  refine ⟨55179522070076254373984915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36786348046717502915989943 55179522070076254373984915)
  ·
    refine ⟨82769283105114381560977373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55179522070076254373984915 82769283105114381560977373)
    ·
      refine ⟨31038481164417893085366515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82769283105114381560977373 31038481164417893085366515)
      ·
        refine ⟨46557721746626839628049773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31038481164417893085366515 46557721746626839628049773)
        ·
          refine ⟨17459145654985064860518665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46557721746626839628049773 17459145654985064860518665)
          ·
            refine ⟨13094359241238798645388999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17459145654985064860518665 13094359241238798645388999)
            ·
              refine ⟨19641538861858197968083499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13094359241238798645388999 19641538861858197968083499)
              ·
                refine ⟨29462308292787296952125249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19641538861858197968083499 29462308292787296952125249)
                ·
                  refine ⟨22096731219590472714093937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29462308292787296952125249 22096731219590472714093937)
                  ·
                    refine ⟨16572548414692854535570453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22096731219590472714093937 16572548414692854535570453)
                    ·
                      refine ⟨776838206938727556354865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16572548414692854535570453 776838206938727556354865)
                      ·
                        rfl

theorem cell23_1512887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1512887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512887 prefixEnd_1512887 := by exact prefixLift 1512887
  have htrace : WordTrace (prefixWord ++ tailWord_1512887) baseStart_1512887 baseEnd_1512887 := by
    simpa [prefixWord, tailWord_1512887, baseEnd_1512887] using wordTrace_append hprefix tailTrace_1512887
  have hstable : (prefixWord ++ tailWord_1512887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512887).length < 2 ^ (prefixWord ++ tailWord_1512887).sum := by decide
  have hdescent : baseEnd_1512887 < baseStart_1512887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512907 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_1512907 : Nat := 118140960795 + 1512907 * 2 ^ 59
def prefixEnd_1512907 : Nat := 4983230072969 + 3 ^ 40 * 1512907 * 2
def baseEnd_1512907 : Nat := 776848476551817478104773

theorem tailTrace_1512907 : CollatzResearch.WordTrace tailWord_1512907 prefixEnd_1512907 776848476551817478104773 := by
  unfold tailWord_1512907
  simp only [CollatzResearch.WordTrace]
  refine ⟨55180251530003797789712975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36786834353335865193141983 55180251530003797789712975)
  ·
    refine ⟨82770377295005696684569463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55180251530003797789712975 82770377295005696684569463)
    ·
      refine ⟨124155565942508545026854195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82770377295005696684569463 124155565942508545026854195)
      ·
        refine ⟨186233348913762817540281293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124155565942508545026854195 186233348913762817540281293)
        ·
          refine ⟨69837505842661056577605485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186233348913762817540281293 69837505842661056577605485)
          ·
            refine ⟨26189064690997896216602057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69837505842661056577605485 26189064690997896216602057)
            ·
              refine ⟨19641798518248422162451543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26189064690997896216602057 19641798518248422162451543)
              ·
                refine ⟨29462697777372633243677315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19641798518248422162451543 29462697777372633243677315)
                ·
                  refine ⟨44194046666058949865515973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29462697777372633243677315 44194046666058949865515973)
                  ·
                    refine ⟨8286383749886053099784245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44194046666058949865515973 8286383749886053099784245)
                    ·
                      refine ⟨776848476551817478104773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8286383749886053099784245 776848476551817478104773)
                      ·
                        rfl

theorem cell23_1512907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_1512907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512907 prefixEnd_1512907 := by exact prefixLift 1512907
  have htrace : WordTrace (prefixWord ++ tailWord_1512907) baseStart_1512907 baseEnd_1512907 := by
    simpa [prefixWord, tailWord_1512907, baseEnd_1512907] using wordTrace_append hprefix tailTrace_1512907
  have hstable : (prefixWord ++ tailWord_1512907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512907).length < 2 ^ (prefixWord ++ tailWord_1512907).sum := by decide
  have hdescent : baseEnd_1512907 < baseStart_1512907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512944 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_1512944 : Nat := 118140960795 + 1512944 * 2 ^ 59
def prefixEnd_1512944 : Nat := 4983230072969 + 3 ^ 40 * 1512944 * 2
def baseEnd_1512944 : Nat := 258955825112011277780701

theorem tailTrace_1512944 : CollatzResearch.WordTrace tailWord_1512944 prefixEnd_1512944 258955825112011277780701 := by
  unfold tailWord_1512944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590800515434876554404943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36787734020579835405873257 27590800515434876554404943)
  ·
    refine ⟨41386200773152314831607415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590800515434876554404943 41386200773152314831607415)
    ·
      refine ⟨62079301159728472247411123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41386200773152314831607415 62079301159728472247411123)
      ·
        refine ⟨93118951739592708371116685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62079301159728472247411123 93118951739592708371116685)
        ·
          refine ⟨34919606902347265639168757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93118951739592708371116685 34919606902347265639168757)
          ·
            refine ⟨3273713147095056153672071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34919606902347265639168757 3273713147095056153672071)
            ·
              refine ⟨4910569720642584230508107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273713147095056153672071 4910569720642584230508107)
              ·
                refine ⟨7365854580963876345762161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910569720642584230508107 7365854580963876345762161)
                ·
                  refine ⟨5524390935722907259321621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7365854580963876345762161 5524390935722907259321621)
                  ·
                    refine ⟨258955825112011277780701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5524390935722907259321621 258955825112011277780701)
                    ·
                      rfl

theorem cell23_1512944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_1512944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512944 prefixEnd_1512944 := by exact prefixLift 1512944
  have htrace : WordTrace (prefixWord ++ tailWord_1512944) baseStart_1512944 baseEnd_1512944 := by
    simpa [prefixWord, tailWord_1512944, baseEnd_1512944] using wordTrace_append hprefix tailTrace_1512944
  have hstable : (prefixWord ++ tailWord_1512944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512944).length < 2 ^ (prefixWord ++ tailWord_1512944).sum := by decide
  have hdescent : baseEnd_1512944 < baseStart_1512944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512954 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_1512954 : Nat := 118140960795 + 1512954 * 2 ^ 59
def prefixEnd_1512954 : Nat := 4983230072969 + 3 ^ 40 * 1512954 * 2
def baseEnd_1512954 : Nat := 776872610142578794217057

theorem tailTrace_1512954 : CollatzResearch.WordTrace tailWord_1512954 prefixEnd_1512954 776872610142578794217057 := by
  unfold tailWord_1512954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795491440208381204168479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36787977173889016544449277 13795491440208381204168479)
  ·
    refine ⟨20693237160312571806252719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795491440208381204168479 20693237160312571806252719)
    ·
      refine ⟨31039855740468857709379079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20693237160312571806252719 31039855740468857709379079)
      ·
        refine ⟨46559783610703286564068619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31039855740468857709379079 46559783610703286564068619)
        ·
          refine ⟨69839675416054929846102929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46559783610703286564068619 69839675416054929846102929)
          ·
            refine ⟨52379756562041197384577197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69839675416054929846102929 52379756562041197384577197)
            ·
              refine ⟨19642408710765449019216449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52379756562041197384577197 19642408710765449019216449)
              ·
                refine ⟨14731806533074086764412337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19642408710765449019216449 14731806533074086764412337)
                ·
                  refine ⟨11048854899805565073309253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14731806533074086764412337 11048854899805565073309253)
                  ·
                    refine ⟨2071660293713543451245485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11048854899805565073309253 2071660293713543451245485)
                    ·
                      refine ⟨776872610142578794217057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071660293713543451245485 776872610142578794217057)
                      ·
                        rfl

theorem cell23_1512954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_1512954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512954 prefixEnd_1512954 := by exact prefixLift 1512954
  have htrace : WordTrace (prefixWord ++ tailWord_1512954) baseStart_1512954 baseEnd_1512954 := by
    simpa [prefixWord, tailWord_1512954, baseEnd_1512954] using wordTrace_append hprefix tailTrace_1512954
  have hstable : (prefixWord ++ tailWord_1512954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512954).length < 2 ^ (prefixWord ++ tailWord_1512954).sum := by decide
  have hdescent : baseEnd_1512954 < baseStart_1512954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512966 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1512966 : Nat := 118140960795 + 1512966 * 2 ^ 59
def prefixEnd_1512966 : Nat := 4983230072969 + 3 ^ 40 * 1512966 * 2
def baseEnd_1512966 : Nat := 776878771910432747267003

theorem tailTrace_1512966 : CollatzResearch.WordTrace tailWord_1512966 prefixEnd_1512966 776878771910432747267003 := by
  unfold tailWord_1512966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724450107399689089565961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36788268957860033910740501 1724450107399689089565961)
  ·
    refine ⟨1293337580549766817174471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1724450107399689089565961 1293337580549766817174471)
    ·
      refine ⟨1940006370824650225761707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293337580549766817174471 1940006370824650225761707)
      ·
        refine ⟨2910009556236975338642561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940006370824650225761707 2910009556236975338642561)
        ·
          refine ⟨2182507167177731503981921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2910009556236975338642561 2182507167177731503981921)
          ·
            refine ⟨1636880375383298627986441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182507167177731503981921 1636880375383298627986441)
            ·
              refine ⟨1227660281537473970989831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636880375383298627986441 1227660281537473970989831)
              ·
                refine ⟨1841490422306210956484747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227660281537473970989831 1841490422306210956484747)
                ·
                  refine ⟨2762235633459316434727121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841490422306210956484747 2762235633459316434727121)
                  ·
                    refine ⟨2071676725094487326045341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2762235633459316434727121 2071676725094487326045341)
                    ·
                      refine ⟨776878771910432747267003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071676725094487326045341 776878771910432747267003)
                      ·
                        rfl

theorem cell23_1512966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1512966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512966 prefixEnd_1512966 := by exact prefixLift 1512966
  have htrace : WordTrace (prefixWord ++ tailWord_1512966) baseStart_1512966 baseEnd_1512966 := by
    simpa [prefixWord, tailWord_1512966, baseEnd_1512966] using wordTrace_append hprefix tailTrace_1512966
  have hstable : (prefixWord ++ tailWord_1512966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512966).length < 2 ^ (prefixWord ++ tailWord_1512966).sum := by decide
  have hdescent : baseEnd_1512966 < baseStart_1512966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512972 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_1512972 : Nat := 118140960795 + 1512972 * 2 ^ 59
def prefixEnd_1512972 : Nat := 4983230072969 + 3 ^ 40 * 1512972 * 2
def baseEnd_1512972 : Nat := 776881852794359723791975

theorem tailTrace_1512972 : CollatzResearch.WordTrace tailWord_1512972 prefixEnd_1512972 776881852794359723791975 := by
  unfold tailWord_1512972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27591311137384156945414585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36788414849845542593886113 27591311137384156945414585)
  ·
    refine ⟨20693483353038117709060939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27591311137384156945414585 20693483353038117709060939)
    ·
      refine ⟨31040225029557176563591409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20693483353038117709060939 31040225029557176563591409)
      ·
        refine ⟨23280168772167882422693557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31040225029557176563591409 23280168772167882422693557)
        ·
          refine ⟨2182515822390738977127521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23280168772167882422693557 2182515822390738977127521)
          ·
            refine ⟨1636886866793054232845641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182515822390738977127521 1636886866793054232845641)
            ·
              refine ⟨1227665150094790674634231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636886866793054232845641 1227665150094790674634231)
              ·
                refine ⟨1841497725142186011951347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227665150094790674634231 1841497725142186011951347)
                ·
                  refine ⟨2762246587713279017927021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841497725142186011951347 2762246587713279017927021)
                  ·
                    refine ⟨1035842470392479631722633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762246587713279017927021 1035842470392479631722633)
                    ·
                      refine ⟨776881852794359723791975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035842470392479631722633 776881852794359723791975)
                      ·
                        rfl

theorem cell23_1512972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_1512972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512972 prefixEnd_1512972 := by exact prefixLift 1512972
  have htrace : WordTrace (prefixWord ++ tailWord_1512972) baseStart_1512972 baseEnd_1512972 := by
    simpa [prefixWord, tailWord_1512972, baseEnd_1512972] using wordTrace_append hprefix tailTrace_1512972
  have hstable : (prefixWord ++ tailWord_1512972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512972).length < 2 ^ (prefixWord ++ tailWord_1512972).sum := by decide
  have hdescent : baseEnd_1512972 < baseStart_1512972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512991 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 5]
def baseStart_1512991 : Nat := 118140960795 + 1512991 * 2 ^ 59
def prefixEnd_1512991 : Nat := 4983230072969 + 3 ^ 40 * 1512991 * 2
def baseEnd_1512991 : Nat := 86321289880755016606043

theorem tailTrace_1512991 : CollatzResearch.WordTrace tailWord_1512991 prefixEnd_1512991 86321289880755016606043 := by
  unfold tailWord_1512991
  simp only [CollatzResearch.WordTrace]
  refine ⟨55183315261699480135770827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36788876841132986757180551 55183315261699480135770827)
  ·
    refine ⟨82774972892549220203656241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55183315261699480135770827 82774972892549220203656241)
    ·
      refine ⟨62081229669411915152742181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82774972892549220203656241 62081229669411915152742181)
      ·
        refine ⟨11640230563014734091139159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62081229669411915152742181 11640230563014734091139159)
        ·
          refine ⟨17460345844522101136708739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11640230563014734091139159 17460345844522101136708739)
          ·
            refine ⟨26190518766783151705063109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17460345844522101136708739 26190518766783151705063109)
            ·
              refine ⟨4910722268771840944699333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26190518766783151705063109 4910722268771840944699333)
              ·
                refine ⟨920760425394720177131125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4910722268771840944699333 920760425394720177131125)
                ·
                  refine ⟨86321289880755016606043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 920760425394720177131125 86321289880755016606043)
                  ·
                    rfl

theorem cell23_1512991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 5].length) (baseStart_1512991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1512991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1512991 prefixEnd_1512991 := by exact prefixLift 1512991
  have htrace : WordTrace (prefixWord ++ tailWord_1512991) baseStart_1512991 baseEnd_1512991 := by
    simpa [prefixWord, tailWord_1512991, baseEnd_1512991] using wordTrace_append hprefix tailTrace_1512991
  have hstable : (prefixWord ++ tailWord_1512991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512991).length < 2 ^ (prefixWord ++ tailWord_1512991).sum := by decide
  have hdescent : baseEnd_1512991 < baseStart_1512991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513002 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1513002 : Nat := 118140960795 + 1513002 * 2 ^ 59
def prefixEnd_1513002 : Nat := 4983230072969 + 3 ^ 40 * 1513002 * 2
def baseEnd_1513002 : Nat := 776897257213994606416837

theorem tailTrace_1513002 : CollatzResearch.WordTrace tailWord_1513002 prefixEnd_1513002 776897257213994606416837 := by
  unfold tailWord_1513002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795929116164907253605315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36789144309773086009614173 13795929116164907253605315)
  ·
    refine ⟨20693893674247360880407973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13795929116164907253605315 20693893674247360880407973)
    ·
      refine ⟨3880105063921380165076495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20693893674247360880407973 3880105063921380165076495)
      ·
        refine ⟨5820157595882070247614743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880105063921380165076495 5820157595882070247614743)
        ·
          refine ⟨8730236393823105371422115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820157595882070247614743 8730236393823105371422115)
          ·
            refine ⟨13095354590734658057133173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8730236393823105371422115 13095354590734658057133173)
            ·
              refine ⟨1227689492881374192856235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13095354590734658057133173 1227689492881374192856235)
              ·
                refine ⟨1841534239322061289284353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227689492881374192856235 1841534239322061289284353)
                ·
                  refine ⟨1381150679491545966963265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841534239322061289284353 1381150679491545966963265)
                  ·
                    refine ⟨1035863009618659475222449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381150679491545966963265 1035863009618659475222449)
                    ·
                      refine ⟨776897257213994606416837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035863009618659475222449 776897257213994606416837)
                      ·
                        rfl

theorem cell23_1513002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1513002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513002 prefixEnd_1513002 := by exact prefixLift 1513002
  have htrace : WordTrace (prefixWord ++ tailWord_1513002) baseStart_1513002 baseEnd_1513002 := by
    simpa [prefixWord, tailWord_1513002, baseEnd_1513002] using wordTrace_append hprefix tailTrace_1513002
  have hstable : (prefixWord ++ tailWord_1513002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513002).length < 2 ^ (prefixWord ++ tailWord_1513002).sum := by decide
  have hdescent : baseEnd_1513002 < baseStart_1513002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513041 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_1513041 : Nat := 118140960795 + 1513041 * 2 ^ 59
def prefixEnd_1513041 : Nat := 4983230072969 + 3 ^ 40 * 1513041 * 2
def baseEnd_1513041 : Nat := 776917282959519953829157

theorem tailTrace_1513041 : CollatzResearch.WordTrace tailWord_1513041 prefixEnd_1513041 776917282959519953829157 := by
  unfold tailWord_1513041
  simp only [CollatzResearch.WordTrace]
  refine ⟨55185138911518338675090977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36790092607678892450060651 55185138911518338675090977)
  ·
    refine ⟨41388854183638754006318233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55185138911518338675090977 41388854183638754006318233)
    ·
      refine ⟨31041640637729065504738675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41388854183638754006318233 31041640637729065504738675)
      ·
        refine ⟨46562460956593598257108013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31041640637729065504738675 46562460956593598257108013)
        ·
          refine ⟨17460922858722599346415505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46562460956593598257108013 17460922858722599346415505)
          ·
            refine ⟨13095692144041949509811629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17460922858722599346415505 13095692144041949509811629)
            ·
              refine ⟨4910884554015731066179361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13095692144041949509811629 4910884554015731066179361)
              ·
                refine ⟨3683163415511798299634521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910884554015731066179361 3683163415511798299634521)
                ·
                  refine ⟨2762372561633848724725891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3683163415511798299634521 2762372561633848724725891)
                  ·
                    refine ⟨4143558842450773087088837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2762372561633848724725891 4143558842450773087088837)
                    ·
                      refine ⟨776917282959519953829157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4143558842450773087088837 776917282959519953829157)
                      ·
                        rfl

theorem cell23_1513041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_1513041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513041 prefixEnd_1513041 := by exact prefixLift 1513041
  have htrace : WordTrace (prefixWord ++ tailWord_1513041) baseStart_1513041 baseEnd_1513041 := by
    simpa [prefixWord, tailWord_1513041, baseEnd_1513041] using wordTrace_append hprefix tailTrace_1513041
  have hstable : (prefixWord ++ tailWord_1513041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513041).length < 2 ^ (prefixWord ++ tailWord_1513041).sum := by decide
  have hdescent : baseEnd_1513041 < baseStart_1513041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513053 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1513053 : Nat := 118140960795 + 1513053 * 2 ^ 59
def prefixEnd_1513053 : Nat := 4983230072969 + 3 ^ 40 * 1513053 * 2
def baseEnd_1513053 : Nat := 776923444727373906879103

theorem tailTrace_1513053 : CollatzResearch.WordTrace tailWord_1513053 prefixEnd_1513053 776923444727373906879103 := by
  unfold tailWord_1513053
  simp only [CollatzResearch.WordTrace]
  refine ⟨55185576587474864724527813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36790384391649909816351875 55185576587474864724527813)
  ·
    refine ⟨10347295610151537135848965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55185576587474864724527813 10347295610151537135848965)
    ·
      refine ⟨1940117926903413212971681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10347295610151537135848965 1940117926903413212971681)
      ·
        refine ⟨1455088445177559909728761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940117926903413212971681 1455088445177559909728761)
        ·
          refine ⟨1091316333883169932296571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455088445177559909728761 1091316333883169932296571)
          ·
            refine ⟨1636974500824754898444857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091316333883169932296571 1636974500824754898444857)
            ·
              refine ⟨1227730875618566173833643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636974500824754898444857 1227730875618566173833643)
              ·
                refine ⟨1841596313427849260750465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227730875618566173833643 1841596313427849260750465)
                ·
                  refine ⟨1381197235070886945562849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841596313427849260750465 1381197235070886945562849)
                  ·
                    refine ⟨1035897926303165209172137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381197235070886945562849 1035897926303165209172137)
                    ·
                      refine ⟨776923444727373906879103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1035897926303165209172137 776923444727373906879103)
                      ·
                        rfl

theorem cell23_1513053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1513053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513053 prefixEnd_1513053 := by exact prefixLift 1513053
  have htrace : WordTrace (prefixWord ++ tailWord_1513053) baseStart_1513053 baseEnd_1513053 := by
    simpa [prefixWord, tailWord_1513053, baseEnd_1513053] using wordTrace_append hprefix tailTrace_1513053
  have hstable : (prefixWord ++ tailWord_1513053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513053).length < 2 ^ (prefixWord ++ tailWord_1513053).sum := by decide
  have hdescent : baseEnd_1513053 < baseStart_1513053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513084 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1513084 : Nat := 118140960795 + 1513084 * 2 ^ 59
def prefixEnd_1513084 : Nat := 4983230072969 + 3 ^ 40 * 1513084 * 2
def baseEnd_1513084 : Nat := 776939362627663285591459

theorem tailTrace_1513084 : CollatzResearch.WordTrace tailWord_1513084 prefixEnd_1513084 776939362627663285591459 := by
  unfold tailWord_1513084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593353625181278509453153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36791138166908371345937537 27593353625181278509453153)
  ·
    refine ⟨20695015218885958882089865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27593353625181278509453153 20695015218885958882089865)
    ·
      refine ⟨15521261414164469161567399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20695015218885958882089865 15521261414164469161567399)
      ·
        refine ⟨23281892121246703742351099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15521261414164469161567399 23281892121246703742351099)
        ·
          refine ⟨34922838181870055613526649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23281892121246703742351099 34922838181870055613526649)
          ·
            refine ⟨26192128636402541710144987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34922838181870055613526649 26192128636402541710144987)
            ·
              refine ⟨39288192954603812565217481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26192128636402541710144987 39288192954603812565217481)
              ·
                refine ⟨29466144715952859423913111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39288192954603812565217481 29466144715952859423913111)
                ·
                  refine ⟨44199217073929289135869667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29466144715952859423913111 44199217073929289135869667)
                  ·
                    refine ⟨66298825610893933703804501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44199217073929289135869667 66298825610893933703804501)
                    ·
                      refine ⟨776939362627663285591459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66298825610893933703804501 776939362627663285591459)
                      ·
                        rfl

theorem cell23_1513084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1513084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513084 prefixEnd_1513084 := by exact prefixLift 1513084
  have htrace : WordTrace (prefixWord ++ tailWord_1513084) baseStart_1513084 baseEnd_1513084 := by
    simpa [prefixWord, tailWord_1513084, baseEnd_1513084] using wordTrace_append hprefix tailTrace_1513084
  have hstable : (prefixWord ++ tailWord_1513084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513084).length < 2 ^ (prefixWord ++ tailWord_1513084).sum := by decide
  have hdescent : baseEnd_1513084 < baseStart_1513084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513098 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_1513098 : Nat := 118140960795 + 1513098 * 2 ^ 59
def prefixEnd_1513098 : Nat := 4983230072969 + 3 ^ 40 * 1513098 * 2
def baseEnd_1513098 : Nat := 86327394595202914535155

theorem tailTrace_1513098 : CollatzResearch.WordTrace tailWord_1513098 prefixEnd_1513098 86327394595202914535155 := by
  unfold tailWord_1513098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13796804468077959352478987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36791478581541224939943965 13796804468077959352478987)
  ·
    refine ⟨20695206702116939028718481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13796804468077959352478987 20695206702116939028718481)
    ·
      refine ⟨15521405026587704271538861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20695206702116939028718481 15521405026587704271538861)
      ·
        refine ⟨5820526884970389101827073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15521405026587704271538861 5820526884970389101827073)
        ·
          refine ⟨4365395163727791826370305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5820526884970389101827073 4365395163727791826370305)
          ·
            refine ⟨3274046372795843869777729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4365395163727791826370305 3274046372795843869777729)
            ·
              refine ⟨2455534779596882902333297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274046372795843869777729 2455534779596882902333297)
              ·
                refine ⟨1841651084697662176749973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455534779596882902333297 1841651084697662176749973)
                ·
                  refine ⟨86327394595202914535155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1841651084697662176749973 86327394595202914535155)
                  ·
                    rfl

theorem cell23_1513098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_1513098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513098 prefixEnd_1513098 := by exact prefixLift 1513098
  have htrace : WordTrace (prefixWord ++ tailWord_1513098) baseStart_1513098 baseEnd_1513098 := by
    simpa [prefixWord, tailWord_1513098, baseEnd_1513098] using wordTrace_append hprefix tailTrace_1513098
  have hstable : (prefixWord ++ tailWord_1513098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513098).length < 2 ^ (prefixWord ++ tailWord_1513098).sum := by decide
  have hdescent : baseEnd_1513098 < baseStart_1513098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513102 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_1513102 : Nat := 118140960795 + 1513102 * 2 ^ 59
def prefixEnd_1513102 : Nat := 4983230072969 + 3 ^ 40 * 1513102 * 2
def baseEnd_1513102 : Nat := 258982868426481405055459

theorem tailTrace_1513102 : CollatzResearch.WordTrace tailWord_1513102 prefixEnd_1513102 258982868426481405055459 := by
  unfold tailWord_1513102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898420470537168261632695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36791575842864897395374373 6898420470537168261632695)
  ·
    refine ⟨10347630705805752392449043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6898420470537168261632695 10347630705805752392449043)
    ·
      refine ⟨15521446058708628588673565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10347630705805752392449043 15521446058708628588673565)
      ·
        refine ⟨5820542272015735720752587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15521446058708628588673565 5820542272015735720752587)
        ·
          refine ⟨8730813408023603581128881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820542272015735720752587 8730813408023603581128881)
          ·
            refine ⟨6548110056017702685846661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8730813408023603581128881 6548110056017702685846661)
            ·
              refine ⟨1227770635503319253596249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6548110056017702685846661 1227770635503319253596249)
              ·
                refine ⟨920827976627489440197187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227770635503319253596249 920827976627489440197187)
                ·
                  refine ⟨1381241964941234160295781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920827976627489440197187 1381241964941234160295781)
                  ·
                    refine ⟨258982868426481405055459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381241964941234160295781 258982868426481405055459)
                    ·
                      rfl

theorem cell23_1513102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_1513102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513102 prefixEnd_1513102 := by exact prefixLift 1513102
  have htrace : WordTrace (prefixWord ++ tailWord_1513102) baseStart_1513102 baseEnd_1513102 := by
    simpa [prefixWord, tailWord_1513102, baseEnd_1513102] using wordTrace_append hprefix tailTrace_1513102
  have hstable : (prefixWord ++ tailWord_1513102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513102).length < 2 ^ (prefixWord ++ tailWord_1513102).sum := by decide
  have hdescent : baseEnd_1513102 < baseStart_1513102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513104 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_1513104 : Nat := 118140960795 + 1513104 * 2 ^ 59
def prefixEnd_1513104 : Nat := 4983230072969 + 3 ^ 40 * 1513104 * 2
def baseEnd_1513104 : Nat := 776949632240753207341367

theorem tailTrace_1513104 : CollatzResearch.WordTrace tailWord_1513104 prefixEnd_1513104 776949632240753207341367 := by
  unfold tailWord_1513104
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593718355145050217317183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36791624473526733623089577 27593718355145050217317183)
  ·
    refine ⟨41390577532717575325975775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27593718355145050217317183 41390577532717575325975775)
    ·
      refine ⟨62085866299076362988963663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41390577532717575325975775 62085866299076362988963663)
      ·
        refine ⟨93128799448614544483445495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62085866299076362988963663 93128799448614544483445495)
        ·
          refine ⟨139693199172921816725168243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93128799448614544483445495 139693199172921816725168243)
          ·
            refine ⟨209539798759382725087752365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139693199172921816725168243 209539798759382725087752365)
            ·
              refine ⟨78577424534768521907907137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209539798759382725087752365 78577424534768521907907137)
              ·
                refine ⟨58933068401076391430930353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78577424534768521907907137 58933068401076391430930353)
                ·
                  refine ⟨44199801300807293573197765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58933068401076391430930353 44199801300807293573197765)
                  ·
                    refine ⟨8287462743901367544974581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44199801300807293573197765 8287462743901367544974581)
                    ·
                      refine ⟨776949632240753207341367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8287462743901367544974581 776949632240753207341367)
                      ·
                        rfl

theorem cell23_1513104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_1513104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513104 prefixEnd_1513104 := by exact prefixLift 1513104
  have htrace : WordTrace (prefixWord ++ tailWord_1513104) baseStart_1513104 baseEnd_1513104 := by
    simpa [prefixWord, tailWord_1513104, baseEnd_1513104] using wordTrace_append hprefix tailTrace_1513104
  have hstable : (prefixWord ++ tailWord_1513104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513104).length < 2 ^ (prefixWord ++ tailWord_1513104).sum := by decide
  have hdescent : baseEnd_1513104 < baseStart_1513104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513111 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 3, 5]
def baseStart_1513111 : Nat := 118140960795 + 1513111 * 2 ^ 59
def prefixEnd_1513111 : Nat := 4983230072969 + 3 ^ 40 * 1513111 * 2
def baseEnd_1513111 : Nat := 258984408868444893317945

theorem tailTrace_1513111 : CollatzResearch.WordTrace tailWord_1513111 prefixEnd_1513111 258984408868444893317945 := by
  unfold tailWord_1513111
  simp only [CollatzResearch.WordTrace]
  refine ⟨55187692021264740630139187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36791794680843160420092791 55187692021264740630139187)
  ·
    refine ⟨82781538031897110945208781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55187692021264740630139187 82781538031897110945208781)
    ·
      refine ⟨31043076761961416604453293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82781538031897110945208781 31043076761961416604453293)
      ·
        refine ⟨11641153785735531226669985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31043076761961416604453293 11641153785735531226669985)
        ·
          refine ⟨8730865339301648420002489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11641153785735531226669985 8730865339301648420002489)
          ·
            refine ⟨6548149004476236315001867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8730865339301648420002489 6548149004476236315001867)
            ·
              refine ⟨9822223506714354472502801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548149004476236315001867 9822223506714354472502801)
              ·
                refine ⟨7366667630035765854377101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9822223506714354472502801 7366667630035765854377101)
                ·
                  refine ⟨2762500361263412195391413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7366667630035765854377101 2762500361263412195391413)
                  ·
                    refine ⟨258984408868444893317945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2762500361263412195391413 258984408868444893317945)
                    ·
                      rfl

theorem cell23_1513111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_1513111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513111 prefixEnd_1513111 := by exact prefixLift 1513111
  have htrace : WordTrace (prefixWord ++ tailWord_1513111) baseStart_1513111 baseEnd_1513111 := by
    simpa [prefixWord, tailWord_1513111, baseEnd_1513111] using wordTrace_append hprefix tailTrace_1513111
  have hstable : (prefixWord ++ tailWord_1513111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513111).length < 2 ^ (prefixWord ++ tailWord_1513111).sum := by decide
  have hdescent : baseEnd_1513111 < baseStart_1513111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513151 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1513151 : Nat := 118140960795 + 1513151 * 2 ^ 59
def prefixEnd_1513151 : Nat := 4983230072969 + 3 ^ 40 * 1513151 * 2
def baseEnd_1513151 : Nat := 776973765831514523453651

theorem tailTrace_1513151 : CollatzResearch.WordTrace tailWord_1513151 prefixEnd_1513151 776973765831514523453651 := by
  unfold tailWord_1513151
  simp only [CollatzResearch.WordTrace]
  refine ⟨55189150941119827461595307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36792767294079884974396871 55189150941119827461595307)
  ·
    refine ⟨82783726411679741192392961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55189150941119827461595307 82783726411679741192392961)
    ·
      refine ⟨62087794808759805894294721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82783726411679741192392961 62087794808759805894294721)
      ·
        refine ⟨46565846106569854420721041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62087794808759805894294721 46565846106569854420721041)
        ·
          refine ⟨34924384579927390815540781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46565846106569854420721041 34924384579927390815540781)
          ·
            refine ⟨13096644217472771555827793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34924384579927390815540781 13096644217472771555827793)
            ·
              refine ⟨9822483163104578666870845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13096644217472771555827793 9822483163104578666870845)
              ·
                refine ⟨3683431186164217000076567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9822483163104578666870845 3683431186164217000076567)
                ·
                  refine ⟨5525146779246325500114851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683431186164217000076567 5525146779246325500114851)
                  ·
                    refine ⟨8287720168869488250172277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5525146779246325500114851 8287720168869488250172277)
                    ·
                      refine ⟨776973765831514523453651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8287720168869488250172277 776973765831514523453651)
                      ·
                        rfl

theorem cell23_1513151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1513151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513151 prefixEnd_1513151 := by exact prefixLift 1513151
  have htrace : WordTrace (prefixWord ++ tailWord_1513151) baseStart_1513151 baseEnd_1513151 := by
    simpa [prefixWord, tailWord_1513151, baseEnd_1513151] using wordTrace_append hprefix tailTrace_1513151
  have hstable : (prefixWord ++ tailWord_1513151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513151).length < 2 ^ (prefixWord ++ tailWord_1513151).sum := by decide
  have hdescent : baseEnd_1513151 < baseStart_1513151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513175 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 2, 4]
def baseStart_1513175 : Nat := 118140960795 + 1513175 * 2 ^ 59
def prefixEnd_1513175 : Nat := 4983230072969 + 3 ^ 40 * 1513175 * 2
def baseEnd_1513175 : Nat := 258995363122407476517847

theorem tailTrace_1513175 : CollatzResearch.WordTrace tailWord_1513175 prefixEnd_1513175 258995363122407476517847 := by
  unfold tailWord_1513175
  simp only [CollatzResearch.WordTrace]
  refine ⟨55190026293032879560468979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36793350862021919706979319 55190026293032879560468979)
  ·
    refine ⟨82785039439549319340703469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55190026293032879560468979 82785039439549319340703469)
    ·
      refine ⟨31044389789830994752763801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82785039439549319340703469 31044389789830994752763801)
      ·
        refine ⟨23283292342373246064572851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31044389789830994752763801 23283292342373246064572851)
        ·
          refine ⟨34924938513559869096859277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23283292342373246064572851 34924938513559869096859277)
          ·
            refine ⟨13096851942584950911322229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34924938513559869096859277 13096851942584950911322229)
            ·
              refine ⟨1227829869617339147936459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13096851942584950911322229 1227829869617339147936459)
              ·
                refine ⟨1841744804426008721904689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227829869617339147936459 1841744804426008721904689)
                ·
                  refine ⟨1381308603319506541428517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841744804426008721904689 1381308603319506541428517)
                  ·
                    refine ⟨258995363122407476517847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381308603319506541428517 258995363122407476517847)
                    ·
                      rfl

theorem cell23_1513175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_1513175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513175 prefixEnd_1513175 := by exact prefixLift 1513175
  have htrace : WordTrace (prefixWord ++ tailWord_1513175) baseStart_1513175 baseEnd_1513175 := by
    simpa [prefixWord, tailWord_1513175, baseEnd_1513175] using wordTrace_append hprefix tailTrace_1513175
  have hstable : (prefixWord ++ tailWord_1513175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513175).length < 2 ^ (prefixWord ++ tailWord_1513175).sum := by decide
  have hdescent : baseEnd_1513175 < baseStart_1513175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513178 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1513178 : Nat := 118140960795 + 1513178 * 2 ^ 59
def prefixEnd_1513178 : Nat := 4983230072969 + 3 ^ 40 * 1513178 * 2
def baseEnd_1513178 : Nat := 776987629809185917816027

theorem tailTrace_1513178 : CollatzResearch.WordTrace tailWord_1513178 prefixEnd_1513178 776987629809185917816027 := by
  unfold tailWord_1513178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797533928005502768207047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36793423808014674048552125 13797533928005502768207047)
  ·
    refine ⟨20696300892008254152310571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13797533928005502768207047 20696300892008254152310571)
    ·
      refine ⟨31044451338012381228465857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20696300892008254152310571 31044451338012381228465857)
      ·
        refine ⟨23283338503509285921349393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31044451338012381228465857 23283338503509285921349393)
        ·
          refine ⟨17462503877631964441012045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23283338503509285921349393 17462503877631964441012045)
          ·
            refine ⟨6548438954111986665379517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17462503877631964441012045 6548438954111986665379517)
            ·
              refine ⟨2455664607791994999517319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6548438954111986665379517 2455664607791994999517319)
              ·
                refine ⟨3683496911687992499275979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455664607791994999517319 3683496911687992499275979)
                ·
                  refine ⟨5525245367531988748913969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3683496911687992499275979 5525245367531988748913969)
                  ·
                    refine ⟨4143934025648991561685477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5525245367531988748913969 4143934025648991561685477)
                    ·
                      refine ⟨776987629809185917816027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4143934025648991561685477 776987629809185917816027)
                      ·
                        rfl

theorem cell23_1513178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1513178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513178 prefixEnd_1513178 := by exact prefixLift 1513178
  have htrace : WordTrace (prefixWord ++ tailWord_1513178) baseStart_1513178 baseEnd_1513178 := by
    simpa [prefixWord, tailWord_1513178, baseEnd_1513178] using wordTrace_append hprefix tailTrace_1513178
  have hstable : (prefixWord ++ tailWord_1513178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513178).length < 2 ^ (prefixWord ++ tailWord_1513178).sum := by decide
  have hdescent : baseEnd_1513178 < baseStart_1513178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513198 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_1513198 : Nat := 118140960795 + 1513198 * 2 ^ 59
def prefixEnd_1513198 : Nat := 4983230072969 + 3 ^ 40 * 1513198 * 2
def baseEnd_1513198 : Nat := 776997899422275839565935

theorem tailTrace_1513198 : CollatzResearch.WordTrace tailWord_1513198 prefixEnd_1513198 776997899422275839565935 := by
  unfold tailWord_1513198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6898858146493694311069531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36793910114633036325704165 6898858146493694311069531)
  ·
    refine ⟨10348287219740541466604297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6898858146493694311069531 10348287219740541466604297)
    ·
      refine ⟨7761215414805406099953223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10348287219740541466604297 7761215414805406099953223)
      ·
        refine ⟨11641823122208109149929835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761215414805406099953223 11641823122208109149929835)
        ·
          refine ⟨17462734683312163724894753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11641823122208109149929835 17462734683312163724894753)
          ·
            refine ⟨13097051012484122793671065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17462734683312163724894753 13097051012484122793671065)
            ·
              refine ⟨9822788259363092095253299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13097051012484122793671065 9822788259363092095253299)
              ·
                refine ⟨14734182389044638142879949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9822788259363092095253299 14734182389044638142879949)
                ·
                  refine ⟨5525318395891739303579981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14734182389044638142879949 5525318395891739303579981)
                  ·
                    refine ⟨2071994398459402238842493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5525318395891739303579981 2071994398459402238842493)
                    ·
                      refine ⟨776997899422275839565935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2071994398459402238842493 776997899422275839565935)
                      ·
                        rfl

theorem cell23_1513198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_1513198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513198 prefixEnd_1513198 := by exact prefixLift 1513198
  have htrace : WordTrace (prefixWord ++ tailWord_1513198) baseStart_1513198 baseEnd_1513198 := by
    simpa [prefixWord, tailWord_1513198, baseEnd_1513198] using wordTrace_append hprefix tailTrace_1513198
  have hstable : (prefixWord ++ tailWord_1513198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513198).length < 2 ^ (prefixWord ++ tailWord_1513198).sum := by decide
  have hdescent : baseEnd_1513198 < baseStart_1513198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513218 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1513218 : Nat := 118140960795 + 1513218 * 2 ^ 59
def prefixEnd_1513218 : Nat := 4983230072969 + 3 ^ 40 * 1513218 * 2
def baseEnd_1513218 : Nat := 259002723011788587105281

theorem tailTrace_1513218 : CollatzResearch.WordTrace tailWord_1513218 prefixEnd_1513218 259002723011788587105281 := by
  unfold tailWord_1513218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13797898657969274476071077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36794396421251398602856205 13797898657969274476071077)
  ·
    refine ⟨2587105998369238964263327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13797898657969274476071077 2587105998369238964263327)
    ·
      refine ⟨3880658997553858446394991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587105998369238964263327 3880658997553858446394991)
      ·
        refine ⟨5820988496330787669592487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880658997553858446394991 5820988496330787669592487)
        ·
          refine ⟨8731482744496181504388731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820988496330787669592487 8731482744496181504388731)
          ·
            refine ⟨13097224116744272256583097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8731482744496181504388731 13097224116744272256583097)
            ·
              refine ⟨9822918087558204192437323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13097224116744272256583097 9822918087558204192437323)
              ·
                refine ⟨14734377131337306288655985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9822918087558204192437323 14734377131337306288655985)
                ·
                  refine ⟨11050782848502979716491989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14734377131337306288655985 11050782848502979716491989)
                  ·
                    refine ⟨259002723011788587105281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11050782848502979716491989 259002723011788587105281)
                    ·
                      rfl

theorem cell23_1513218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1513218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513218 prefixEnd_1513218 := by exact prefixLift 1513218
  have htrace : WordTrace (prefixWord ++ tailWord_1513218) baseStart_1513218 baseEnd_1513218 := by
    simpa [prefixWord, tailWord_1513218, baseEnd_1513218] using wordTrace_append hprefix tailTrace_1513218
  have hstable : (prefixWord ++ tailWord_1513218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513218).length < 2 ^ (prefixWord ++ tailWord_1513218).sum := by decide
  have hdescent : baseEnd_1513218 < baseStart_1513218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513242 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_1513242 : Nat := 118140960795 + 1513242 * 2 ^ 59
def prefixEnd_1513242 : Nat := 4983230072969 + 3 ^ 40 * 1513242 * 2
def baseEnd_1513242 : Nat := 777020492571073667415733

theorem tailTrace_1513242 : CollatzResearch.WordTrace tailWord_1513242 prefixEnd_1513242 777020492571073667415733 := by
  unfold tailWord_1513242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798117495947537500789495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36794979989193433335438653 13798117495947537500789495)
  ·
    refine ⟨20697176243921306251184243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13798117495947537500789495 20697176243921306251184243)
    ·
      refine ⟨31045764365881959376776365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20697176243921306251184243 31045764365881959376776365)
      ·
        refine ⟨11642161637205734766291137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31045764365881959376776365 11642161637205734766291137)
        ·
          refine ⟨8731621227904301074718353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11642161637205734766291137 8731621227904301074718353)
          ·
            refine ⟨6548715920928225806038765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8731621227904301074718353 6548715920928225806038765)
            ·
              refine ⟨2455768470348084677264537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6548715920928225806038765 2455768470348084677264537)
              ·
                refine ⟨1841826352761063507948403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455768470348084677264537 1841826352761063507948403)
                ·
                  refine ⟨2762739529141595261922605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841826352761063507948403 2762739529141595261922605)
                  ·
                    refine ⟨1036027323428098223220977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2762739529141595261922605 1036027323428098223220977)
                    ·
                      refine ⟨777020492571073667415733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036027323428098223220977 777020492571073667415733)
                      ·
                        rfl

theorem cell23_1513242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_1513242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513242 prefixEnd_1513242 := by exact prefixLift 1513242
  have htrace : WordTrace (prefixWord ++ tailWord_1513242) baseStart_1513242 baseEnd_1513242 := by
    simpa [prefixWord, tailWord_1513242, baseEnd_1513242] using wordTrace_append hprefix tailTrace_1513242
  have hstable : (prefixWord ++ tailWord_1513242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513242).length < 2 ^ (prefixWord ++ tailWord_1513242).sum := by decide
  have hdescent : baseEnd_1513242 < baseStart_1513242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513272 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_1513272 : Nat := 118140960795 + 1513272 * 2 ^ 59
def prefixEnd_1513272 : Nat := 4983230072969 + 3 ^ 40 * 1513272 * 2
def baseEnd_1513272 : Nat := 777035896990708550040595

theorem tailTrace_1513272 : CollatzResearch.WordTrace tailWord_1513272 prefixEnd_1513272 777035896990708550040595 := by
  unfold tailWord_1513272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27596782086840732563375035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36795709449120976751166713 27596782086840732563375035)
  ·
    refine ⟨41395173130261098845062553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27596782086840732563375035 41395173130261098845062553)
    ·
      refine ⟨31046379847695824133796915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41395173130261098845062553 31046379847695824133796915)
      ·
        refine ⟨46569569771543736200695373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31046379847695824133796915 46569569771543736200695373)
        ·
          refine ⟨17463588664328901075260765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46569569771543736200695373 17463588664328901075260765)
          ·
            refine ⟨6548845749123337903222787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17463588664328901075260765 6548845749123337903222787)
            ·
              refine ⟨9823268623685006854834181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548845749123337903222787 9823268623685006854834181)
              ·
                refine ⟨1841862866940938785281409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9823268623685006854834181 1841862866940938785281409)
                ·
                  refine ⟨1381397150205704088961057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841862866940938785281409 1381397150205704088961057)
                  ·
                    refine ⟨1036047862654278066720793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381397150205704088961057 1036047862654278066720793)
                    ·
                      refine ⟨777035896990708550040595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036047862654278066720793 777035896990708550040595)
                      ·
                        rfl

theorem cell23_1513272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_1513272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513272 prefixEnd_1513272 := by exact prefixLift 1513272
  have htrace : WordTrace (prefixWord ++ tailWord_1513272) baseStart_1513272 baseEnd_1513272 := by
    simpa [prefixWord, tailWord_1513272, baseEnd_1513272] using wordTrace_append hprefix tailTrace_1513272
  have hstable : (prefixWord ++ tailWord_1513272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513272).length < 2 ^ (prefixWord ++ tailWord_1513272).sum := by decide
  have hdescent : baseEnd_1513272 < baseStart_1513272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513288 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_1513288 : Nat := 118140960795 + 1513288 * 2 ^ 59
def prefixEnd_1513288 : Nat := 4983230072969 + 3 ^ 40 * 1513288 * 2
def baseEnd_1513288 : Nat := 777044112681180487440521

theorem tailTrace_1513288 : CollatzResearch.WordTrace tailWord_1513288 prefixEnd_1513288 777044112681180487440521 := by
  unfold tailWord_1513288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27597073870811749929666259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36796098494415666572888345 27597073870811749929666259)
  ·
    refine ⟨41395610806217624894499389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27597073870811749929666259 41395610806217624894499389)
    ·
      refine ⟨15523354052331609335437271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41395610806217624894499389 15523354052331609335437271)
      ·
        refine ⟨23285031078497414003155907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15523354052331609335437271 23285031078497414003155907)
        ·
          refine ⟨34927546617746121004733861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23285031078497414003155907 34927546617746121004733861)
          ·
            refine ⟨6548914990827397688387599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34927546617746121004733861 6548914990827397688387599)
            ·
              refine ⟨9823372486241096532581399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548914990827397688387599 9823372486241096532581399)
              ·
                refine ⟨14735058729361644798872099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9823372486241096532581399 14735058729361644798872099)
                ·
                  refine ⟨22102588094042467198308149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14735058729361644798872099 22102588094042467198308149)
                  ·
                    refine ⟨2072117633816481299841389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22102588094042467198308149 2072117633816481299841389)
                    ·
                      refine ⟨777044112681180487440521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2072117633816481299841389 777044112681180487440521)
                      ·
                        rfl

theorem cell23_1513288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_1513288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513288 prefixEnd_1513288 := by exact prefixLift 1513288
  have htrace : WordTrace (prefixWord ++ tailWord_1513288) baseStart_1513288 baseEnd_1513288 := by
    simpa [prefixWord, tailWord_1513288, baseEnd_1513288] using wordTrace_append hprefix tailTrace_1513288
  have hstable : (prefixWord ++ tailWord_1513288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513288).length < 2 ^ (prefixWord ++ tailWord_1513288).sum := by decide
  have hdescent : baseEnd_1513288 < baseStart_1513288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513321 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_1513321 : Nat := 118140960795 + 1513321 * 2 ^ 59
def prefixEnd_1513321 : Nat := 4983230072969 + 3 ^ 40 * 1513321 * 2
def baseEnd_1513321 : Nat := 259020352514259619442623

theorem tailTrace_1513321 : CollatzResearch.WordTrace tailWord_1513321 prefixEnd_1513321 259020352514259619442623 := by
  unfold tailWord_1513321
  simp only [CollatzResearch.WordTrace]
  refine ⟨55195351350503946495283817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36796900900335964330189211 55195351350503946495283817)
  ·
    refine ⟨41396513512877959871462863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55195351350503946495283817 41396513512877959871462863)
    ·
      refine ⟨62094770269316939807194295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41396513512877959871462863 62094770269316939807194295)
      ·
        refine ⟨93142155403975409710791443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62094770269316939807194295 93142155403975409710791443)
        ·
          refine ⟨139713233105963114566187165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93142155403975409710791443 139713233105963114566187165)
          ·
            refine ⟨52392462414736167962320187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139713233105963114566187165 52392462414736167962320187)
            ·
              refine ⟨78588693622104251943480281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52392462414736167962320187 78588693622104251943480281)
              ·
                refine ⟨58941520216578188957610211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78588693622104251943480281 58941520216578188957610211)
                ·
                  refine ⟨88412280324867283436415317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58941520216578188957610211 88412280324867283436415317)
                  ·
                    refine ⟨259020352514259619442623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 88412280324867283436415317 259020352514259619442623)
                    ·
                      rfl

theorem cell23_1513321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_1513321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513321 prefixEnd_1513321 := by exact prefixLift 1513321
  have htrace : WordTrace (prefixWord ++ tailWord_1513321) baseStart_1513321 baseEnd_1513321 := by
    simpa [prefixWord, tailWord_1513321, baseEnd_1513321] using wordTrace_append hprefix tailTrace_1513321
  have hstable : (prefixWord ++ tailWord_1513321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513321).length < 2 ^ (prefixWord ++ tailWord_1513321).sum := by decide
  have hdescent : baseEnd_1513321 < baseStart_1513321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513328 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_1513328 : Nat := 118140960795 + 1513328 * 2 ^ 59
def prefixEnd_1513328 : Nat := 4983230072969 + 3 ^ 40 * 1513328 * 2
def baseEnd_1513328 : Nat := 777064651907360330940337

theorem tailTrace_1513328 : CollatzResearch.WordTrace tailWord_1513328 prefixEnd_1513328 777064651907360330940337 := by
  unfold tailWord_1513328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27597803330739293345394319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36797071107652391127192425 27597803330739293345394319)
  ·
    refine ⟨41396704996108940018091479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27597803330739293345394319 41396704996108940018091479)
    ·
      refine ⟨62095057494163410027137219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41396704996108940018091479 62095057494163410027137219)
      ·
        refine ⟨93142586241245115040705829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62095057494163410027137219 93142586241245115040705829)
        ·
          refine ⟨17464234920233459070132343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93142586241245115040705829 17464234920233459070132343)
          ·
            refine ⟨26196352380350188605198515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17464234920233459070132343 26196352380350188605198515)
            ·
              refine ⟨39294528570525282907797773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26196352380350188605198515 39294528570525282907797773)
              ·
                refine ⟨14735448213946981090424165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39294528570525282907797773 14735448213946981090424165)
                ·
                  refine ⟨2762896540115058954454531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14735448213946981090424165 2762896540115058954454531)
                  ·
                    refine ⟨4144344810172588431681797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2762896540115058954454531 4144344810172588431681797)
                    ·
                      refine ⟨777064651907360330940337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4144344810172588431681797 777064651907360330940337)
                      ·
                        rfl

theorem cell23_1513328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_1513328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513328 prefixEnd_1513328 := by exact prefixLift 1513328
  have htrace : WordTrace (prefixWord ++ tailWord_1513328) baseStart_1513328 baseEnd_1513328 := by
    simpa [prefixWord, tailWord_1513328, baseEnd_1513328] using wordTrace_append hprefix tailTrace_1513328
  have hstable : (prefixWord ++ tailWord_1513328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513328).length < 2 ^ (prefixWord ++ tailWord_1513328).sum := by decide
  have hdescent : baseEnd_1513328 < baseStart_1513328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513365 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_1513365 : Nat := 118140960795 + 1513365 * 2 ^ 59
def prefixEnd_1513365 : Nat := 4983230072969 + 3 ^ 40 * 1513365 * 2
def baseEnd_1513365 : Nat := 777083650691576686177667

theorem tailTrace_1513365 : CollatzResearch.WordTrace tailWord_1513365 prefixEnd_1513365 777083650691576686177667 := by
  unfold tailWord_1513365
  simp only [CollatzResearch.WordTrace]
  refine ⟨55196956162344542009885549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36797970774896361339923699 55196956162344542009885549)
  ·
    refine ⟨20698858560879203253707081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55196956162344542009885549 20698858560879203253707081)
    ·
      refine ⟨15524143920659402440280311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20698858560879203253707081 15524143920659402440280311)
      ·
        refine ⟨23286215880989103660420467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15524143920659402440280311 23286215880989103660420467)
        ·
          refine ⟨34929323821483655490630701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23286215880989103660420467 34929323821483655490630701)
          ·
            refine ⟨13098496433056370808986513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34929323821483655490630701 13098496433056370808986513)
            ·
              refine ⟨9823872324792278106739885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13098496433056370808986513 9823872324792278106739885)
              ·
                refine ⟨3683952121797104290027457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9823872324792278106739885 3683952121797104290027457)
                ·
                  refine ⟨2762964091347828217520593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3683952121797104290027457 2762964091347828217520593)
                  ·
                    refine ⟨2072223068510871163140445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2762964091347828217520593 2072223068510871163140445)
                    ·
                      refine ⟨777083650691576686177667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2072223068510871163140445 777083650691576686177667)
                      ·
                        rfl

theorem cell23_1513365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_1513365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513365 prefixEnd_1513365 := by exact prefixLift 1513365
  have htrace : WordTrace (prefixWord ++ tailWord_1513365) baseStart_1513365 baseEnd_1513365 := by
    simpa [prefixWord, tailWord_1513365, baseEnd_1513365] using wordTrace_append hprefix tailTrace_1513365
  have hstable : (prefixWord ++ tailWord_1513365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513365).length < 2 ^ (prefixWord ++ tailWord_1513365).sum := by decide
  have hdescent : baseEnd_1513365 < baseStart_1513365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513432 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 1, 5]
def baseStart_1513432 : Nat := 118140960795 + 1513432 * 2 ^ 59
def prefixEnd_1513432 : Nat := 4983230072969 + 3 ^ 40 * 1513432 * 2
def baseEnd_1513432 : Nat := 259039351298475974679953

theorem tailTrace_1513432 : CollatzResearch.WordTrace tailWord_1513432 prefixEnd_1513432 259039351298475974679953 := by
  unfold tailWord_1513432
  simp only [CollatzResearch.WordTrace]
  refine ⟨27599699926550906226287275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36799599902067874968383033 27599699926550906226287275)
  ·
    refine ⟨41399549889826359339430913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27599699926550906226287275 41399549889826359339430913)
    ·
      refine ⟨31049662417369769504573185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41399549889826359339430913 31049662417369769504573185)
      ·
        refine ⟨23287246813027327128429889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31049662417369769504573185 23287246813027327128429889)
        ·
          refine ⟨17465435109770495346322417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23287246813027327128429889 17465435109770495346322417)
          ·
            refine ⟨13099076332327871509741813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17465435109770495346322417 13099076332327871509741813)
            ·
              refine ⟨1228038406155737954038295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13099076332327871509741813 1228038406155737954038295)
              ·
                refine ⟨1842057609233606931057443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228038406155737954038295 1842057609233606931057443)
                ·
                  refine ⟨2763086413850410396586165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842057609233606931057443 2763086413850410396586165)
                  ·
                    refine ⟨259039351298475974679953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2763086413850410396586165 259039351298475974679953)
                    ·
                      rfl

theorem cell23_1513432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_1513432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513432 prefixEnd_1513432 := by exact prefixLift 1513432
  have htrace : WordTrace (prefixWord ++ tailWord_1513432) baseStart_1513432 baseEnd_1513432 := by
    simpa [prefixWord, tailWord_1513432, baseEnd_1513432] using wordTrace_append hprefix tailTrace_1513432
  have hstable : (prefixWord ++ tailWord_1513432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513432).length < 2 ^ (prefixWord ++ tailWord_1513432).sum := by decide
  have hdescent : baseEnd_1513432 < baseStart_1513432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513436 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 6]
def baseStart_1513436 : Nat := 118140960795 + 1513436 * 2 ^ 59
def prefixEnd_1513436 : Nat := 4983230072969 + 3 ^ 40 * 1513436 * 2
def baseEnd_1513436 : Nat := 86346678646449545376649

theorem tailTrace_1513436 : CollatzResearch.WordTrace tailWord_1513436 prefixEnd_1513436 86346678646449545376649 := by
  unfold tailWord_1513436
  simp only [CollatzResearch.WordTrace]
  refine ⟨27599772872543660567860081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36799697163391547423813441 27599772872543660567860081)
  ·
    refine ⟨20699829654407745425895061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27599772872543660567860081 20699829654407745425895061)
    ·
      refine ⟨970304515050363066838831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20699829654407745425895061 970304515050363066838831)
      ·
        refine ⟨1455456772575544600258247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970304515050363066838831 1455456772575544600258247)
        ·
          refine ⟨2183185158863316900387371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455456772575544600258247 2183185158863316900387371)
          ·
            refine ⟨3274777738294975350581057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183185158863316900387371 3274777738294975350581057)
            ·
              refine ⟨2456083303721231512935793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274777738294975350581057 2456083303721231512935793)
              ·
                refine ⟨1842062477790923634701845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456083303721231512935793 1842062477790923634701845)
                ·
                  refine ⟨86346678646449545376649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1842062477790923634701845 86346678646449545376649)
                  ·
                    rfl

theorem cell23_1513436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_1513436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513436 prefixEnd_1513436 := by exact prefixLift 1513436
  have htrace : WordTrace (prefixWord ++ tailWord_1513436) baseStart_1513436 baseEnd_1513436 := by
    simpa [prefixWord, tailWord_1513436, baseEnd_1513436] using wordTrace_append hprefix tailTrace_1513436
  have hstable : (prefixWord ++ tailWord_1513436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513436).length < 2 ^ (prefixWord ++ tailWord_1513436).sum := by decide
  have hdescent : baseEnd_1513436 < baseStart_1513436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513452 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_1513452 : Nat := 118140960795 + 1513452 * 2 ^ 59
def prefixEnd_1513452 : Nat := 4983230072969 + 3 ^ 40 * 1513452 * 2
def baseEnd_1513452 : Nat := 777128323508517845789767

theorem tailTrace_1513452 : CollatzResearch.WordTrace tailWord_1513452 prefixEnd_1513452 777128323508517845789767 := by
  unfold tailWord_1513452
  simp only [CollatzResearch.WordTrace]
  refine ⟨27600064656514677934151305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36800086208686237245535073 27600064656514677934151305)
  ·
    refine ⟨20700048492386008450613479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27600064656514677934151305 20700048492386008450613479)
    ·
      refine ⟨31050072738579012675920219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20700048492386008450613479 31050072738579012675920219)
      ·
        refine ⟨46575109107868519013880329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31050072738579012675920219 46575109107868519013880329)
        ·
          refine ⟨34931331830901389260410247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46575109107868519013880329 34931331830901389260410247)
          ·
            refine ⟨52396997746352083890615371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34931331830901389260410247 52396997746352083890615371)
            ·
              refine ⟨78595496619528125835923057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52396997746352083890615371 78595496619528125835923057)
              ·
                refine ⟨58946622464646094376942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78595496619528125835923057 58946622464646094376942293)
                ·
                  refine ⟨1381561464015142836959585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58946622464646094376942293 1381561464015142836959585)
                  ·
                    refine ⟨1036171098011357127719689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381561464015142836959585 1036171098011357127719689)
                    ·
                      refine ⟨777128323508517845789767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036171098011357127719689 777128323508517845789767)
                      ·
                        rfl

theorem cell23_1513452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_1513452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513452 prefixEnd_1513452 := by exact prefixLift 1513452
  have htrace : WordTrace (prefixWord ++ tailWord_1513452) baseStart_1513452 baseEnd_1513452 := by
    simpa [prefixWord, tailWord_1513452, baseEnd_1513452] using wordTrace_append hprefix tailTrace_1513452
  have hstable : (prefixWord ++ tailWord_1513452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513452).length < 2 ^ (prefixWord ++ tailWord_1513452).sum := by decide
  have hdescent : baseEnd_1513452 < baseStart_1513452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513455 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_1513455 : Nat := 118140960795 + 1513455 * 2 ^ 59
def prefixEnd_1513455 : Nat := 4983230072969 + 3 ^ 40 * 1513455 * 2
def baseEnd_1513455 : Nat := 777129863950481334052253

theorem tailTrace_1513455 : CollatzResearch.WordTrace tailWord_1513455 prefixEnd_1513455 777129863950481334052253 := by
  unfold tailWord_1513455
  simp only [CollatzResearch.WordTrace]
  refine ⟨55200238732018487380661819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36800159154678991587107879 55200238732018487380661819)
  ·
    refine ⟨82800358098027731070992729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55200238732018487380661819 82800358098027731070992729)
    ·
      refine ⟨62100268573520798303244547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82800358098027731070992729 62100268573520798303244547)
      ·
        refine ⟨93150402860281197454866821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62100268573520798303244547 93150402860281197454866821)
        ·
          refine ⟨17465700536302724522787529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93150402860281197454866821 17465700536302724522787529)
          ·
            refine ⟨13099275402227043392090647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17465700536302724522787529 13099275402227043392090647)
            ·
              refine ⟨19648913103340565088135971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13099275402227043392090647 19648913103340565088135971)
              ·
                refine ⟨29473369655010847632203957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19648913103340565088135971 29473369655010847632203957)
                ·
                  refine ⟨2763128405157266965519121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29473369655010847632203957 2763128405157266965519121)
                  ·
                    refine ⟨2072346303867950224139341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2763128405157266965519121 2072346303867950224139341)
                    ·
                      refine ⟨777129863950481334052253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2072346303867950224139341 777129863950481334052253)
                      ·
                        rfl

theorem cell23_1513455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_1513455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513455 prefixEnd_1513455 := by exact prefixLift 1513455
  have htrace : WordTrace (prefixWord ++ tailWord_1513455) baseStart_1513455 baseEnd_1513455 := by
    simpa [prefixWord, tailWord_1513455, baseEnd_1513455] using wordTrace_append hprefix tailTrace_1513455
  have hstable : (prefixWord ++ tailWord_1513455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513455).length < 2 ^ (prefixWord ++ tailWord_1513455).sum := by decide
  have hdescent : baseEnd_1513455 < baseStart_1513455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513465 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1513465 : Nat := 118140960795 + 1513465 * 2 ^ 59
def prefixEnd_1513465 : Nat := 4983230072969 + 3 ^ 40 * 1513465 * 2
def baseEnd_1513465 : Nat := 777134998757026294927207

theorem tailTrace_1513465 : CollatzResearch.WordTrace tailWord_1513465 prefixEnd_1513465 777134998757026294927207 := by
  unfold tailWord_1513465
  simp only [CollatzResearch.WordTrace]
  refine ⟨55200603461982259088525849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36800402307988172725683899 55200603461982259088525849)
  ·
    refine ⟨41400452596486694316394387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55200603461982259088525849 41400452596486694316394387)
    ·
      refine ⟨62100678894730041474591581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41400452596486694316394387 62100678894730041474591581)
      ·
        refine ⟨23287754585523765552971843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62100678894730041474591581 23287754585523765552971843)
        ·
          refine ⟨34931631878285648329457765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23287754585523765552971843 34931631878285648329457765)
          ·
            refine ⟨6549680977178559061773331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34931631878285648329457765 6549680977178559061773331)
            ·
              refine ⟨9824521465767838592659997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6549680977178559061773331 9824521465767838592659997)
              ·
                refine ⟨3684195549662939472247499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9824521465767838592659997 3684195549662939472247499)
                ·
                  refine ⟨5526293324494409208371249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684195549662939472247499 5526293324494409208371249)
                  ·
                    refine ⟨4144719993370806906278437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5526293324494409208371249 4144719993370806906278437)
                    ·
                      refine ⟨777134998757026294927207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4144719993370806906278437 777134998757026294927207)
                      ·
                        rfl

theorem cell23_1513465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1513465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513465 prefixEnd_1513465 := by exact prefixLift 1513465
  have htrace : WordTrace (prefixWord ++ tailWord_1513465) baseStart_1513465 baseEnd_1513465 := by
    simpa [prefixWord, tailWord_1513465, baseEnd_1513465] using wordTrace_append hprefix tailTrace_1513465
  have hstable : (prefixWord ++ tailWord_1513465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513465).length < 2 ^ (prefixWord ++ tailWord_1513465).sum := by decide
  have hdescent : baseEnd_1513465 < baseStart_1513465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513488 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_1513488 : Nat := 118140960795 + 1513488 * 2 ^ 59
def prefixEnd_1513488 : Nat := 4983230072969 + 3 ^ 40 * 1513488 * 2
def baseEnd_1513488 : Nat := 259048936270693234979867

theorem tailTrace_1513488 : CollatzResearch.WordTrace tailWord_1513488 prefixEnd_1513488 259048936270693234979867 := by
  unfold tailWord_1513488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27600721170449467008306559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36800961560599289344408745 27600721170449467008306559)
  ·
    refine ⟨41401081755674200512459839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27600721170449467008306559 41401081755674200512459839)
    ·
      refine ⟨62101622633511300768689759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41401081755674200512459839 62101622633511300768689759)
      ·
        refine ⟨93152433950266951153034639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62101622633511300768689759 93152433950266951153034639)
        ·
          refine ⟨139728650925400426729551959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93152433950266951153034639 139728650925400426729551959)
          ·
            refine ⟨209592976388100640094327939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139728650925400426729551959 209592976388100640094327939)
            ·
              refine ⟨314389464582150960141491909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209592976388100640094327939 314389464582150960141491909)
              ·
                refine ⟨58948024609153305026529733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314389464582150960141491909 58948024609153305026529733)
                ·
                  refine ⟨11052754614216244692474325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58948024609153305026529733 11052754614216244692474325)
                  ·
                    refine ⟨259048936270693234979867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11052754614216244692474325 259048936270693234979867)
                    ·
                      rfl

theorem cell23_1513488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_1513488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513488 prefixEnd_1513488 := by exact prefixLift 1513488
  have htrace : WordTrace (prefixWord ++ tailWord_1513488) baseStart_1513488 baseEnd_1513488 := by
    simpa [prefixWord, tailWord_1513488, baseEnd_1513488] using wordTrace_append hprefix tailTrace_1513488
  have hstable : (prefixWord ++ tailWord_1513488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513488).length < 2 ^ (prefixWord ++ tailWord_1513488).sum := by decide
  have hdescent : baseEnd_1513488 < baseStart_1513488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513525 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1513525 : Nat := 118140960795 + 1513525 * 2 ^ 59
def prefixEnd_1513525 : Nat := 4983230072969 + 3 ^ 40 * 1513525 * 2
def baseEnd_1513525 : Nat := 777165807596296060176931

theorem tailTrace_1513525 : CollatzResearch.WordTrace tailWord_1513525 prefixEnd_1513525 777165807596296060176931 := by
  unfold tailWord_1513525
  simp only [CollatzResearch.WordTrace]
  refine ⟨55202791841764889335710029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36801861227843259557140019 55202791841764889335710029)
  ·
    refine ⟨20701046940661833500891261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55202791841764889335710029 20701046940661833500891261)
    ·
      refine ⟨7762892602748187562834223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20701046940661833500891261 7762892602748187562834223)
      ·
        refine ⟨11644338904122281344251335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762892602748187562834223 11644338904122281344251335)
        ·
          refine ⟨17466508356183422016377003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644338904122281344251335 17466508356183422016377003)
          ·
            refine ⟨26199762534275133024565505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17466508356183422016377003 26199762534275133024565505)
            ·
              refine ⟨19649821900706349768424129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26199762534275133024565505 19649821900706349768424129)
              ·
                refine ⟨14737366425529762326318097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19649821900706349768424129 14737366425529762326318097)
                ·
                  refine ⟨11053024819147321744738573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14737366425529762326318097 11053024819147321744738573)
                  ·
                    refine ⟨4144884307180245654276965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11053024819147321744738573 4144884307180245654276965)
                    ·
                      refine ⟨777165807596296060176931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4144884307180245654276965 777165807596296060176931)
                      ·
                        rfl

theorem cell23_1513525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1513525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513525 prefixEnd_1513525 := by exact prefixLift 1513525
  have htrace : WordTrace (prefixWord ++ tailWord_1513525) baseStart_1513525 baseEnd_1513525 := by
    simpa [prefixWord, tailWord_1513525, baseEnd_1513525] using wordTrace_append hprefix tailTrace_1513525
  have hstable : (prefixWord ++ tailWord_1513525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513525).length < 2 ^ (prefixWord ++ tailWord_1513525).sum := by decide
  have hdescent : baseEnd_1513525 < baseStart_1513525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513545 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_1513545 : Nat := 118140960795 + 1513545 * 2 ^ 59
def prefixEnd_1513545 : Nat := 4983230072969 + 3 ^ 40 * 1513545 * 2
def baseEnd_1513545 : Nat := 777176077209385981926839

theorem tailTrace_1513545 : CollatzResearch.WordTrace tailWord_1513545 prefixEnd_1513545 777176077209385981926839 := by
  unfold tailWord_1513545
  simp only [CollatzResearch.WordTrace]
  refine ⟨55203521301692432751438089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36802347534461621834292059 55203521301692432751438089)
  ·
    refine ⟨41402640976269324563578567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55203521301692432751438089 41402640976269324563578567)
    ·
      refine ⟨62103961464403986845367851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41402640976269324563578567 62103961464403986845367851)
      ·
        refine ⟨93155942196605980268051777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62103961464403986845367851 93155942196605980268051777)
        ·
          refine ⟨69866956647454485201038833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93155942196605980268051777 69866956647454485201038833)
          ·
            refine ⟨52400217485590863900779125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69866956647454485201038833 52400217485590863900779125)
            ·
              refine ⟨4912520389274143490698043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52400217485590863900779125 4912520389274143490698043)
              ·
                refine ⟨7368780583911215236047065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912520389274143490698043 7368780583911215236047065)
                ·
                  refine ⟨5526585437933411427035299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7368780583911215236047065 5526585437933411427035299)
                  ·
                    refine ⟨8289878156900117140552949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5526585437933411427035299 8289878156900117140552949)
                    ·
                      refine ⟨777176077209385981926839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8289878156900117140552949 777176077209385981926839)
                      ·
                        rfl

theorem cell23_1513545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_1513545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513545 prefixEnd_1513545 := by exact prefixLift 1513545
  have htrace : WordTrace (prefixWord ++ tailWord_1513545) baseStart_1513545 baseEnd_1513545 := by
    simpa [prefixWord, tailWord_1513545, baseEnd_1513545] using wordTrace_append hprefix tailTrace_1513545
  have hstable : (prefixWord ++ tailWord_1513545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513545).length < 2 ^ (prefixWord ++ tailWord_1513545).sum := by decide
  have hdescent : baseEnd_1513545 < baseStart_1513545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513559 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_1513559 : Nat := 118140960795 + 1513559 * 2 ^ 59
def prefixEnd_1513559 : Nat := 4983230072969 + 3 ^ 40 * 1513559 * 2
def baseEnd_1513559 : Nat := 777183265938548927151775

theorem tailTrace_1513559 : CollatzResearch.WordTrace tailWord_1513559 prefixEnd_1513559 777183265938548927151775 := by
  unfold tailWord_1513559
  simp only [CollatzResearch.WordTrace]
  refine ⟨55204031923641713142447731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36802687949094475428298487 55204031923641713142447731)
  ·
    refine ⟨82806047885462569713671597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55204031923641713142447731 82806047885462569713671597)
    ·
      refine ⟨31052267957048463642626849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82806047885462569713671597 31052267957048463642626849)
      ·
        refine ⟨23289200967786347731970137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31052267957048463642626849 23289200967786347731970137)
        ·
          refine ⟨17466900725839760798977603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23289200967786347731970137 17466900725839760798977603)
          ·
            refine ⟨26200351088759641198466405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17466900725839760798977603 26200351088759641198466405)
            ·
              refine ⟨4912565829142432724712451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26200351088759641198466405 4912565829142432724712451)
              ·
                refine ⟨7368848743713649087068677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912565829142432724712451 7368848743713649087068677)
                ·
                  refine ⟨1381659139446309203825377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7368848743713649087068677 1381659139446309203825377)
                  ·
                    refine ⟨1036244354584731902869033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381659139446309203825377 1036244354584731902869033)
                    ·
                      refine ⟨777183265938548927151775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036244354584731902869033 777183265938548927151775)
                      ·
                        rfl

theorem cell23_1513559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_1513559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513559 prefixEnd_1513559 := by exact prefixLift 1513559
  have htrace : WordTrace (prefixWord ++ tailWord_1513559) baseStart_1513559 baseEnd_1513559 := by
    simpa [prefixWord, tailWord_1513559, baseEnd_1513559] using wordTrace_append hprefix tailTrace_1513559
  have hstable : (prefixWord ++ tailWord_1513559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513559).length < 2 ^ (prefixWord ++ tailWord_1513559).sum := by decide
  have hdescent : baseEnd_1513559 < baseStart_1513559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513570 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1513570 : Nat := 118140960795 + 1513570 * 2 ^ 59
def prefixEnd_1513570 : Nat := 4983230072969 + 3 ^ 40 * 1513570 * 2
def baseEnd_1513570 : Nat := 777188914225748384114225

theorem tailTrace_1513570 : CollatzResearch.WordTrace tailWord_1513570 prefixEnd_1513570 777188914225748384114225 := by
  unfold tailWord_1513570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801108281650465505274541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36802955417734574680732109 13801108281650465505274541)
  ·
    refine ⟨5175415605618924564477953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13801108281650465505274541 5175415605618924564477953)
    ·
      refine ⟨3881561704214193423358465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5175415605618924564477953 3881561704214193423358465)
      ·
        refine ⟨2911171278160645067518849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3881561704214193423358465 2911171278160645067518849)
        ·
          refine ⟨2183378458620483800639137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911171278160645067518849 2183378458620483800639137)
          ·
            refine ⟨1637533843965362850479353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183378458620483800639137 1637533843965362850479353)
            ·
              refine ⟨1228150382974022137859515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637533843965362850479353 1228150382974022137859515)
              ·
                refine ⟨1842225574461033206789273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228150382974022137859515 1842225574461033206789273)
                ·
                  refine ⟨1381669180845774905091955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842225574461033206789273 1381669180845774905091955)
                  ·
                    refine ⟨2072503771268662357637933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1381669180845774905091955 2072503771268662357637933)
                    ·
                      refine ⟨777188914225748384114225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2072503771268662357637933 777188914225748384114225)
                      ·
                        rfl

theorem cell23_1513570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1513570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513570 prefixEnd_1513570 := by exact prefixLift 1513570
  have htrace : WordTrace (prefixWord ++ tailWord_1513570) baseStart_1513570 baseEnd_1513570 := by
    simpa [prefixWord, tailWord_1513570, baseEnd_1513570] using wordTrace_append hprefix tailTrace_1513570
  have hstable : (prefixWord ++ tailWord_1513570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513570).length < 2 ^ (prefixWord ++ tailWord_1513570).sum := by decide
  have hdescent : baseEnd_1513570 < baseStart_1513570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513646 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1513646 : Nat := 118140960795 + 1513646 * 2 ^ 59
def prefixEnd_1513646 : Nat := 4983230072969 + 3 ^ 40 * 1513646 * 2
def baseEnd_1513646 : Nat := 259075979585163362254625

theorem tailTrace_1513646 : CollatzResearch.WordTrace tailWord_1513646 prefixEnd_1513646 259075979585163362254625 := by
  unfold tailWord_1513646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900900634290815875108099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36804803382884351333909861 6900900634290815875108099)
  ·
    refine ⟨10351350951436223812662149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900900634290815875108099 10351350951436223812662149)
    ·
      refine ⟨1940878303394291964874153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10351350951436223812662149 1940878303394291964874153)
      ·
        refine ⟨1455658727545718973655615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1940878303394291964874153 1455658727545718973655615)
        ·
          refine ⟨2183488091318578460483423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455658727545718973655615 2183488091318578460483423)
          ·
            refine ⟨3275232136977867690725135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183488091318578460483423 3275232136977867690725135)
            ·
              refine ⟨4912848205466801536087703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275232136977867690725135 4912848205466801536087703)
              ·
                refine ⟨7369272308200202304131555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912848205466801536087703 7369272308200202304131555)
                ·
                  refine ⟨11053908462300303456197333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369272308200202304131555 11053908462300303456197333)
                  ·
                    refine ⟨259075979585163362254625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11053908462300303456197333 259075979585163362254625)
                    ·
                      rfl

theorem cell23_1513646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1513646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513646 prefixEnd_1513646 := by exact prefixLift 1513646
  have htrace : WordTrace (prefixWord ++ tailWord_1513646) baseStart_1513646 baseEnd_1513646 := by
    simpa [prefixWord, tailWord_1513646, baseEnd_1513646] using wordTrace_append hprefix tailTrace_1513646
  have hstable : (prefixWord ++ tailWord_1513646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513646).length < 2 ^ (prefixWord ++ tailWord_1513646).sum := by decide
  have hdescent : baseEnd_1513646 < baseStart_1513646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513649 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1513649 : Nat := 118140960795 + 1513649 * 2 ^ 59
def prefixEnd_1513649 : Nat := 4983230072969 + 3 ^ 40 * 1513649 * 2
def baseEnd_1513649 : Nat := 777229479197453575026361

theorem tailTrace_1513649 : CollatzResearch.WordTrace tailWord_1513649 prefixEnd_1513649 777229479197453575026361 := by
  unfold tailWord_1513649
  simp only [CollatzResearch.WordTrace]
  refine ⟨55207314493315658513224001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36804876328877105675482667 55207314493315658513224001)
  ·
    refine ⟨41405485869986743884918001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55207314493315658513224001 41405485869986743884918001)
    ·
      refine ⟨31054114402490057913688501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41405485869986743884918001 31054114402490057913688501)
      ·
        refine ⟨2911323225233442929408297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31054114402490057913688501 2911323225233442929408297)
        ·
          refine ⟨2183492418925082197056223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911323225233442929408297 2183492418925082197056223)
          ·
            refine ⟨3275238628387623295584335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183492418925082197056223 3275238628387623295584335)
            ·
              refine ⟨4912857942581434943376503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275238628387623295584335 4912857942581434943376503)
              ·
                refine ⟨7369286913872152415064755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912857942581434943376503 7369286913872152415064755)
                ·
                  refine ⟨11053930370808228622597133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369286913872152415064755 11053930370808228622597133)
                  ·
                    refine ⟨4145223889053085733473925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11053930370808228622597133 4145223889053085733473925)
                    ·
                      refine ⟨777229479197453575026361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4145223889053085733473925 777229479197453575026361)
                      ·
                        rfl

theorem cell23_1513649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1513649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513649 prefixEnd_1513649 := by exact prefixLift 1513649
  have htrace : WordTrace (prefixWord ++ tailWord_1513649) baseStart_1513649 baseEnd_1513649 := by
    simpa [prefixWord, tailWord_1513649, baseEnd_1513649] using wordTrace_append hprefix tailTrace_1513649
  have hstable : (prefixWord ++ tailWord_1513649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513649).length < 2 ^ (prefixWord ++ tailWord_1513649).sum := by decide
  have hdescent : baseEnd_1513649 < baseStart_1513649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513675 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_1513675 : Nat := 118140960795 + 1513675 * 2 ^ 59
def prefixEnd_1513675 : Nat := 4983230072969 + 3 ^ 40 * 1513675 * 2
def baseEnd_1513675 : Nat := 777242829694470473301241

theorem tailTrace_1513675 : CollatzResearch.WordTrace tailWord_1513675 prefixEnd_1513675 777242829694470473301241 := by
  unfold tailWord_1513675
  simp only [CollatzResearch.WordTrace]
  refine ⟨55208262791221464953670479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36805508527480976635780319 55208262791221464953670479)
  ·
    refine ⟨82812394186832197430505719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55208262791221464953670479 82812394186832197430505719)
    ·
      refine ⟨124218591280248296145758579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82812394186832197430505719 124218591280248296145758579)
      ·
        refine ⟨186327886920372444218637869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124218591280248296145758579 186327886920372444218637869)
        ·
          refine ⟨69872957595139666581989201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186327886920372444218637869 69872957595139666581989201)
          ·
            refine ⟨52404718196354749936491901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69872957595139666581989201 52404718196354749936491901)
            ·
              refine ⟨19651769323633031226184463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52404718196354749936491901 19651769323633031226184463)
              ·
                refine ⟨29477653985449546839276695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19651769323633031226184463 29477653985449546839276695)
                ·
                  refine ⟨44216480978174320258915043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29477653985449546839276695 44216480978174320258915043)
                  ·
                    refine ⟨66324721467261480388372565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44216480978174320258915043 66324721467261480388372565)
                    ·
                      refine ⟨777242829694470473301241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66324721467261480388372565 777242829694470473301241)
                      ·
                        rfl

theorem cell23_1513675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_1513675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513675 prefixEnd_1513675 := by exact prefixLift 1513675
  have htrace : WordTrace (prefixWord ++ tailWord_1513675) baseStart_1513675 baseEnd_1513675 := by
    simpa [prefixWord, tailWord_1513675, baseEnd_1513675] using wordTrace_append hprefix tailTrace_1513675
  have hstable : (prefixWord ++ tailWord_1513675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513675).length < 2 ^ (prefixWord ++ tailWord_1513675).sum := by decide
  have hdescent : baseEnd_1513675 < baseStart_1513675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513686 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1513686 : Nat := 118140960795 + 1513686 * 2 ^ 59
def prefixEnd_1513686 : Nat := 4983230072969 + 3 ^ 40 * 1513686 * 2
def baseEnd_1513686 : Nat := 777248477981669930263691

theorem tailTrace_1513686 : CollatzResearch.WordTrace tailWord_1513686 prefixEnd_1513686 777248477981669930263691 := by
  unfold tailWord_1513686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3450541499636350864520057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36805775996121075888213941 3450541499636350864520057)
  ·
    refine ⟨2587906124727263148390043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3450541499636350864520057 2587906124727263148390043)
    ·
      refine ⟨3881859187090894722585065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587906124727263148390043 3881859187090894722585065)
      ·
        refine ⟨2911394390318171041938799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3881859187090894722585065 2911394390318171041938799)
        ·
          refine ⟨4367091585477256562908199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911394390318171041938799 4367091585477256562908199)
          ·
            refine ⟨6550637378215884844362299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4367091585477256562908199 6550637378215884844362299)
            ·
              refine ⟨9825956067323827266543449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6550637378215884844362299 9825956067323827266543449)
              ·
                refine ⟨7369467050492870449907587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9825956067323827266543449 7369467050492870449907587)
                ·
                  refine ⟨11054200575739305674861381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369467050492870449907587 11054200575739305674861381)
                  ·
                    refine ⟨2072662607951119814036509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11054200575739305674861381 2072662607951119814036509)
                    ·
                      refine ⟨777248477981669930263691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2072662607951119814036509 777248477981669930263691)
                      ·
                        rfl

theorem cell23_1513686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1513686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513686 prefixEnd_1513686 := by exact prefixLift 1513686
  have htrace : WordTrace (prefixWord ++ tailWord_1513686) baseStart_1513686 baseEnd_1513686 := by
    simpa [prefixWord, tailWord_1513686, baseEnd_1513686] using wordTrace_append hprefix tailTrace_1513686
  have hstable : (prefixWord ++ tailWord_1513686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513686).length < 2 ^ (prefixWord ++ tailWord_1513686).sum := by decide
  have hdescent : baseEnd_1513686 < baseStart_1513686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513752 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1513752 : Nat := 118140960795 + 1513752 * 2 ^ 59
def prefixEnd_1513752 : Nat := 4983230072969 + 3 ^ 40 * 1513752 * 2
def baseEnd_1513752 : Nat := 777282367704866672038387

theorem tailTrace_1513752 : CollatzResearch.WordTrace tailWord_1513752 prefixEnd_1513752 777282367704866672038387 := by
  unfold tailWord_1513752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605535605971253552111755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36807380807961671402815673 27605535605971253552111755)
  ·
    refine ⟨41408303408956880328167633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27605535605971253552111755 41408303408956880328167633)
    ·
      refine ⟨31056227556717660246125725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41408303408956880328167633 31056227556717660246125725)
      ·
        refine ⟨11646085333769122592297147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31056227556717660246125725 11646085333769122592297147)
        ·
          refine ⟨17469128000653683888445721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11646085333769122592297147 17469128000653683888445721)
          ·
            refine ⟨13101846000490262916334291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17469128000653683888445721 13101846000490262916334291)
            ·
              refine ⟨19652769000735394374501437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101846000490262916334291 19652769000735394374501437)
              ·
                refine ⟨7369788375275772890438039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19652769000735394374501437 7369788375275772890438039)
                ·
                  refine ⟨11054682562913659335657059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7369788375275772890438039 11054682562913659335657059)
                  ·
                    refine ⟨16582023844370489003485589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11054682562913659335657059 16582023844370489003485589)
                    ·
                      refine ⟨777282367704866672038387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16582023844370489003485589 777282367704866672038387)
                      ·
                        rfl

theorem cell23_1513752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1513752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513752 prefixEnd_1513752 := by exact prefixLift 1513752
  have htrace : WordTrace (prefixWord ++ tailWord_1513752) baseStart_1513752 baseEnd_1513752 := by
    simpa [prefixWord, tailWord_1513752, baseEnd_1513752] using wordTrace_append hprefix tailTrace_1513752
  have hstable : (prefixWord ++ tailWord_1513752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513752).length < 2 ^ (prefixWord ++ tailWord_1513752).sum := by decide
  have hdescent : baseEnd_1513752 < baseStart_1513752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513756 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_1513756 : Nat := 118140960795 + 1513756 * 2 ^ 59
def prefixEnd_1513756 : Nat := 4983230072969 + 3 ^ 40 * 1513756 * 2
def baseEnd_1513756 : Nat := 777284421627484656388369

theorem tailTrace_1513756 : CollatzResearch.WordTrace tailWord_1513756 prefixEnd_1513756 777284421627484656388369 := by
  unfold tailWord_1513756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605608551964007893684561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36807478069285343858246081 27605608551964007893684561)
  ·
    refine ⟨20704206413973005920263421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27605608551964007893684561 20704206413973005920263421)
    ·
      refine ⟨7764077405239877220098783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20704206413973005920263421 7764077405239877220098783)
      ·
        refine ⟨11646116107859815830148175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7764077405239877220098783 11646116107859815830148175)
        ·
          refine ⟨17469174161789723745222263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11646116107859815830148175 17469174161789723745222263)
          ·
            refine ⟨26203761242684585617833395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17469174161789723745222263 26203761242684585617833395)
            ·
              refine ⟨39305641864026878426750093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26203761242684585617833395 39305641864026878426750093)
              ·
                refine ⟨14739615699010079410031285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39305641864026878426750093 14739615699010079410031285)
                ·
                  refine ⟨1381838971782194944690433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14739615699010079410031285 1381838971782194944690433)
                  ·
                    refine ⟨1036379228836646208517825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1381838971782194944690433 1036379228836646208517825)
                    ·
                      refine ⟨777284421627484656388369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036379228836646208517825 777284421627484656388369)
                      ·
                        rfl

theorem cell23_1513756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_1513756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513756 prefixEnd_1513756 := by exact prefixLift 1513756
  have htrace : WordTrace (prefixWord ++ tailWord_1513756) baseStart_1513756 baseEnd_1513756 := by
    simpa [prefixWord, tailWord_1513756, baseEnd_1513756] using wordTrace_append hprefix tailTrace_1513756
  have hstable : (prefixWord ++ tailWord_1513756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513756).length < 2 ^ (prefixWord ++ tailWord_1513756).sum := by decide
  have hdescent : baseEnd_1513756 < baseStart_1513756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513802 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1513802 : Nat := 118140960795 + 1513802 * 2 ^ 59
def prefixEnd_1513802 : Nat := 4983230072969 + 3 ^ 40 * 1513802 * 2
def baseEnd_1513802 : Nat := 777308041737591476413157

theorem tailTrace_1513802 : CollatzResearch.WordTrace tailWord_1513802 prefixEnd_1513802 777308041737591476413157 := by
  unfold tailWord_1513802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803223715440341410885915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36808596574507577095695773 13803223715440341410885915)
  ·
    refine ⟨20704835573160512116328873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13803223715440341410885915 20704835573160512116328873)
    ·
      refine ⟨15528626679870384087246655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20704835573160512116328873 15528626679870384087246655)
      ·
        refine ⟨23292940019805576130869983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15528626679870384087246655 23292940019805576130869983)
        ·
          refine ⟨34939410029708364196304975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23292940019805576130869983 34939410029708364196304975)
          ·
            refine ⟨52409115044562546294457463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34939410029708364196304975 52409115044562546294457463)
            ·
              refine ⟨78613672566843819441686195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52409115044562546294457463 78613672566843819441686195)
              ·
                refine ⟨117920508850265729162529293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78613672566843819441686195 117920508850265729162529293)
                ·
                  refine ⟨44220190818849648435948485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117920508850265729162529293 44220190818849648435948485)
                  ·
                    refine ⟨8291285778534309081740341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44220190818849648435948485 8291285778534309081740341)
                    ·
                      refine ⟨777308041737591476413157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8291285778534309081740341 777308041737591476413157)
                      ·
                        rfl

theorem cell23_1513802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1513802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513802 prefixEnd_1513802 := by exact prefixLift 1513802
  have htrace : WordTrace (prefixWord ++ tailWord_1513802) baseStart_1513802 baseEnd_1513802 := by
    simpa [prefixWord, tailWord_1513802, baseEnd_1513802] using wordTrace_append hprefix tailTrace_1513802
  have hstable : (prefixWord ++ tailWord_1513802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513802).length < 2 ^ (prefixWord ++ tailWord_1513802).sum := by decide
  have hdescent : baseEnd_1513802 < baseStart_1513802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513872 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_1513872 : Nat := 118140960795 + 1513872 * 2 ^ 59
def prefixEnd_1513872 : Nat := 4983230072969 + 3 ^ 40 * 1513872 * 2
def baseEnd_1513872 : Nat := 777343985383406202537835

theorem tailTrace_1513872 : CollatzResearch.WordTrace tailWord_1513872 prefixEnd_1513872 777343985383406202537835 := by
  unfold tailWord_1513872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27607723985753883799295935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36810298647671845065727913 27607723985753883799295935)
  ·
    refine ⟨41411585978630825698943903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27607723985753883799295935 41411585978630825698943903)
    ·
      refine ⟨62117378967946238548415855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41411585978630825698943903 62117378967946238548415855)
      ·
        refine ⟨93176068451919357822623783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62117378967946238548415855 93176068451919357822623783)
        ·
          refine ⟨139764102677879036733935675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93176068451919357822623783 139764102677879036733935675)
          ·
            refine ⟨209646154016818555100903513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139764102677879036733935675 209646154016818555100903513)
            ·
              refine ⟨157234615512613916325677635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209646154016818555100903513 157234615512613916325677635)
              ·
                refine ⟨235851923268920874488516453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157234615512613916325677635 235851923268920874488516453)
                ·
                  refine ⟨44222235612922663966596835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235851923268920874488516453 44222235612922663966596835)
                  ·
                    refine ⟨66333353419383995949895253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44222235612922663966596835 66333353419383995949895253)
                    ·
                      refine ⟨777343985383406202537835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 66333353419383995949895253 777343985383406202537835)
                      ·
                        rfl

theorem cell23_1513872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_1513872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513872 prefixEnd_1513872 := by exact prefixLift 1513872
  have htrace : WordTrace (prefixWord ++ tailWord_1513872) baseStart_1513872 baseEnd_1513872 := by
    simpa [prefixWord, tailWord_1513872, baseEnd_1513872] using wordTrace_append hprefix tailTrace_1513872
  have hstable : (prefixWord ++ tailWord_1513872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513872).length < 2 ^ (prefixWord ++ tailWord_1513872).sum := by decide
  have hdescent : baseEnd_1513872 < baseStart_1513872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513879 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1513879 : Nat := 118140960795 + 1513879 * 2 ^ 59
def prefixEnd_1513879 : Nat := 4983230072969 + 3 ^ 40 * 1513879 * 2
def baseEnd_1513879 : Nat := 777347579747987675150303

theorem tailTrace_1513879 : CollatzResearch.WordTrace tailWord_1513879 prefixEnd_1513879 777347579747987675150303 := by
  unfold tailWord_1513879
  simp only [CollatzResearch.WordTrace]
  refine ⟨55215703282482407794096691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36810468854988271862731127 55215703282482407794096691)
  ·
    refine ⟨82823554923723611691145037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55215703282482407794096691 82823554923723611691145037)
    ·
      refine ⟨31058833096396354384179389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82823554923723611691145037 31058833096396354384179389)
      ·
        refine ⟨11647062411148632894067271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31058833096396354384179389 11647062411148632894067271)
        ·
          refine ⟨17470593616722949341100907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11647062411148632894067271 17470593616722949341100907)
          ·
            refine ⟨26205890425084424011651361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17470593616722949341100907 26205890425084424011651361)
            ·
              refine ⟨19654417818813318008738521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26205890425084424011651361 19654417818813318008738521)
              ·
                refine ⟨14740813364109988506553891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19654417818813318008738521 14740813364109988506553891)
                ·
                  refine ⟨22111220046164982759830837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14740813364109988506553891 22111220046164982759830837)
                  ·
                    refine ⟨2072926879327967133734141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22111220046164982759830837 2072926879327967133734141)
                    ·
                      refine ⟨777347579747987675150303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2072926879327967133734141 777347579747987675150303)
                      ·
                        rfl

theorem cell23_1513879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1513879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513879 prefixEnd_1513879 := by exact prefixLift 1513879
  have htrace : WordTrace (prefixWord ++ tailWord_1513879) baseStart_1513879 baseEnd_1513879 := by
    simpa [prefixWord, tailWord_1513879, baseEnd_1513879] using wordTrace_append hprefix tailTrace_1513879
  have hstable : (prefixWord ++ tailWord_1513879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513879).length < 2 ^ (prefixWord ++ tailWord_1513879).sum := by decide
  have hdescent : baseEnd_1513879 < baseStart_1513879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513906 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_1513906 : Nat := 118140960795 + 1513906 * 2 ^ 59
def prefixEnd_1513906 : Nat := 4983230072969 + 3 ^ 40 * 1513906 * 2
def baseEnd_1513906 : Nat := 777361443725659069512679

theorem tailTrace_1513906 : CollatzResearch.WordTrace tailWord_1513906 prefixEnd_1513906 777361443725659069512679 := by
  unfold tailWord_1513906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804172013346147851332393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36811125368923060936886381 13804172013346147851332393)
  ·
    refine ⟨10353129010009610888499295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13804172013346147851332393 10353129010009610888499295)
    ·
      refine ⟨15529693515014416332748943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353129010009610888499295 15529693515014416332748943)
      ·
        refine ⟨23294540272521624499123415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15529693515014416332748943 23294540272521624499123415)
        ·
          refine ⟨34941810408782436748685123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23294540272521624499123415 34941810408782436748685123)
          ·
            refine ⟨52412715613173655123027685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34941810408782436748685123 52412715613173655123027685)
            ·
              refine ⟨9827384177470060335567691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52412715613173655123027685 9827384177470060335567691)
              ·
                refine ⟨14741076266205090503351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9827384177470060335567691 14741076266205090503351537)
                ·
                  refine ⟨11055807199653817877513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14741076266205090503351537 11055807199653817877513653)
                  ·
                    refine ⟨1036481924967545426016905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11055807199653817877513653 1036481924967545426016905)
                    ·
                      refine ⟨777361443725659069512679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036481924967545426016905 777361443725659069512679)
                      ·
                        rfl

theorem cell23_1513906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_1513906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513906 prefixEnd_1513906 := by exact prefixLift 1513906
  have htrace : WordTrace (prefixWord ++ tailWord_1513906) baseStart_1513906 baseEnd_1513906 := by
    simpa [prefixWord, tailWord_1513906, baseEnd_1513906] using wordTrace_append hprefix tailTrace_1513906
  have hstable : (prefixWord ++ tailWord_1513906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513906).length < 2 ^ (prefixWord ++ tailWord_1513906).sum := by decide
  have hdescent : baseEnd_1513906 < baseStart_1513906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513939 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3]
def baseStart_1513939 : Nat := 118140960795 + 1513939 * 2 ^ 59
def prefixEnd_1513939 : Nat := 4983230072969 + 3 ^ 40 * 1513939 * 2
def baseEnd_1513939 : Nat := 777378388587257440400027

theorem tailTrace_1513939 : CollatzResearch.WordTrace tailWord_1513939 prefixEnd_1513939 777378388587257440400027 := by
  unfold tailWord_1513939
  simp only [CollatzResearch.WordTrace]
  refine ⟨55217891662265038041280871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36811927774843358694187247 55217891662265038041280871)
  ·
    refine ⟨82826837493397557061921307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55217891662265038041280871 82826837493397557061921307)
    ·
      refine ⟨124240256240096335592881961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82826837493397557061921307 124240256240096335592881961)
      ·
        refine ⟨93180192180072251694661471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124240256240096335592881961 93180192180072251694661471)
        ·
          refine ⟨139770288270108377541992207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93180192180072251694661471 139770288270108377541992207)
          ·
            refine ⟨209655432405162566312988311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139770288270108377541992207 209655432405162566312988311)
            ·
              refine ⟨314483148607743849469482467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209655432405162566312988311 314483148607743849469482467)
              ·
                refine ⟨471724722911615774204223701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314483148607743849469482467 471724722911615774204223701)
                ·
                  refine ⟨11056048193240994707911493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 471724722911615774204223701 11056048193240994707911493)
                  ·
                    refine ⟨2073009036232686507733405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11056048193240994707911493 2073009036232686507733405)
                    ·
                      refine ⟨777378388587257440400027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2073009036232686507733405 777378388587257440400027)
                      ·
                        rfl

theorem cell23_1513939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_1513939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513939 prefixEnd_1513939 := by exact prefixLift 1513939
  have htrace : WordTrace (prefixWord ++ tailWord_1513939) baseStart_1513939 baseEnd_1513939 := by
    simpa [prefixWord, tailWord_1513939, baseEnd_1513939] using wordTrace_append hprefix tailTrace_1513939
  have hstable : (prefixWord ++ tailWord_1513939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513939).length < 2 ^ (prefixWord ++ tailWord_1513939).sum := by decide
  have hdescent : baseEnd_1513939 < baseStart_1513939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513954 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1513954 : Nat := 118140960795 + 1513954 * 2 ^ 59
def prefixEnd_1513954 : Nat := 4983230072969 + 3 ^ 40 * 1513954 * 2
def baseEnd_1513954 : Nat := 86376232310786097968051

theorem tailTrace_1513954 : CollatzResearch.WordTrace tailWord_1513954 prefixEnd_1513954 86376232310786097968051 := by
  unfold tailWord_1513954
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804609689302673900769229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36812292504807130402051277 13804609689302673900769229)
  ·
    refine ⟨5176728633488502712788461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13804609689302673900769229 5176728633488502712788461)
    ·
      refine ⟨1941273237558188517295673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5176728633488502712788461 1941273237558188517295673)
      ·
        refine ⟨1455954928168641387971755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1941273237558188517295673 1455954928168641387971755)
        ·
          refine ⟨2183932392252962081957633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455954928168641387971755 2183932392252962081957633)
          ·
            refine ⟨1637949294189721561468225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183932392252962081957633 1637949294189721561468225)
            ·
              refine ⟨1228461970642291171101169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637949294189721561468225 1228461970642291171101169)
              ·
                refine ⟨921346477981718378325877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228461970642291171101169 921346477981718378325877)
                ·
                  refine ⟨86376232310786097968051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 921346477981718378325877 86376232310786097968051)
                  ·
                    rfl

theorem cell23_1513954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1513954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513954 prefixEnd_1513954 := by exact prefixLift 1513954
  have htrace : WordTrace (prefixWord ++ tailWord_1513954) baseStart_1513954 baseEnd_1513954 := by
    simpa [prefixWord, tailWord_1513954, baseEnd_1513954] using wordTrace_append hprefix tailTrace_1513954
  have hstable : (prefixWord ++ tailWord_1513954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513954).length < 2 ^ (prefixWord ++ tailWord_1513954).sum := by decide
  have hdescent : baseEnd_1513954 < baseStart_1513954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513963 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 1, 4]
def baseStart_1513963 : Nat := 118140960795 + 1513963 * 2 ^ 59
def prefixEnd_1513963 : Nat := 4983230072969 + 3 ^ 40 * 1513963 * 2
def baseEnd_1513963 : Nat := 259130237374321782166639

theorem tailTrace_1513963 : CollatzResearch.WordTrace tailWord_1513963 prefixEnd_1513963 259130237374321782166639 := by
  unfold tailWord_1513963
  simp only [CollatzResearch.WordTrace]
  refine ⟨55218767014178090140154543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36812511342785393426769695 55218767014178090140154543)
  ·
    refine ⟨82828150521267135210231815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55218767014178090140154543 82828150521267135210231815)
    ·
      refine ⟨124242225781900702815347723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82828150521267135210231815 124242225781900702815347723)
      ·
        refine ⟨186363338672851054223021585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124242225781900702815347723 186363338672851054223021585)
        ·
          refine ⟨139772504004638290667266189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186363338672851054223021585 139772504004638290667266189)
          ·
            refine ⟨52414689001739359000224821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139772504004638290667266189 52414689001739359000224821)
            ·
              refine ⟨4913877093913064906271077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52414689001739359000224821 4913877093913064906271077)
              ·
                refine ⟨921351955108699669925827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4913877093913064906271077 921351955108699669925827)
                ·
                  refine ⟨1382027932663049504888741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921351955108699669925827 1382027932663049504888741)
                  ·
                    refine ⟨259130237374321782166639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382027932663049504888741 259130237374321782166639)
                    ·
                      rfl

theorem cell23_1513963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 4].length) (baseStart_1513963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513963 prefixEnd_1513963 := by exact prefixLift 1513963
  have htrace : WordTrace (prefixWord ++ tailWord_1513963) baseStart_1513963 baseEnd_1513963 := by
    simpa [prefixWord, tailWord_1513963, baseEnd_1513963] using wordTrace_append hprefix tailTrace_1513963
  have hstable : (prefixWord ++ tailWord_1513963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513963).length < 2 ^ (prefixWord ++ tailWord_1513963).sum := by decide
  have hdescent : baseEnd_1513963 < baseStart_1513963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513970 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1513970 : Nat := 118140960795 + 1513970 * 2 ^ 59
def prefixEnd_1513970 : Nat := 4983230072969 + 3 ^ 40 * 1513970 * 2
def baseEnd_1513970 : Nat := 777394306487546819112385

theorem tailTrace_1513970 : CollatzResearch.WordTrace tailWord_1513970 prefixEnd_1513970 777394306487546819112385 := by
  unfold tailWord_1513970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804755581288182583914841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36812681550101820223772909 13804755581288182583914841)
  ·
    refine ⟨10353566685966136937936131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13804755581288182583914841 10353566685966136937936131)
    ·
      refine ⟨15530350028949205406904197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353566685966136937936131 15530350028949205406904197)
      ·
        refine ⟨2911940630427976013794537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15530350028949205406904197 2911940630427976013794537)
        ·
          refine ⟨2183955472820982010345903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911940630427976013794537 2183955472820982010345903)
          ·
            refine ⟨3275933209231473015518855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183955472820982010345903 3275933209231473015518855)
            ·
              refine ⟨4913899813847209523278283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275933209231473015518855 4913899813847209523278283)
              ·
                refine ⟨7370849720770814284917425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913899813847209523278283 7370849720770814284917425)
                ·
                  refine ⟨5528137290578110713688069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7370849720770814284917425 5528137290578110713688069)
                  ·
                    refine ⟨1036525741983395758816513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5528137290578110713688069 1036525741983395758816513)
                    ·
                      refine ⟨777394306487546819112385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036525741983395758816513 777394306487546819112385)
                      ·
                        rfl

theorem cell23_1513970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1513970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1513970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1513970 prefixEnd_1513970 := by exact prefixLift 1513970
  have htrace : WordTrace (prefixWord ++ tailWord_1513970) baseStart_1513970 baseEnd_1513970 := by
    simpa [prefixWord, tailWord_1513970, baseEnd_1513970] using wordTrace_append hprefix tailTrace_1513970
  have hstable : (prefixWord ++ tailWord_1513970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513970).length < 2 ^ (prefixWord ++ tailWord_1513970).sum := by decide
  have hdescent : baseEnd_1513970 < baseStart_1513970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514043 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 9, 2, 2]
def baseStart_1514043 : Nat := 118140960795 + 1514043 * 2 ^ 59
def prefixEnd_1514043 : Nat := 4983230072969 + 3 ^ 40 * 1514043 * 2
def baseEnd_1514043 : Nat := 777431790575325033499549

theorem tailTrace_1514043 : CollatzResearch.WordTrace tailWord_1514043 prefixEnd_1514043 777431790575325033499549 := by
  unfold tailWord_1514043
  simp only [CollatzResearch.WordTrace]
  refine ⟨55221684853888263803066783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36814456569258842535377855 55221684853888263803066783)
  ·
    refine ⟨82832527280832395704600175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55221684853888263803066783 82832527280832395704600175)
    ·
      refine ⟨124248790921248593556900263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82832527280832395704600175 124248790921248593556900263)
      ·
        refine ⟨186373186381872890335350395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124248790921248593556900263 186373186381872890335350395)
        ·
          refine ⟨279559779572809335503025593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186373186381872890335350395 279559779572809335503025593)
          ·
            refine ⟨209669834679607001627269195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279559779572809335503025593 209669834679607001627269195)
            ·
              refine ⟨314504752019410502440903793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209669834679607001627269195 314504752019410502440903793)
              ·
                refine ⟨235878564014557876830677845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314504752019410502440903793 235878564014557876830677845)
                ·
                  refine ⟨1382100961022800059554753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 235878564014557876830677845 1382100961022800059554753)
                  ·
                    refine ⟨1036575720767100044666065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1382100961022800059554753 1036575720767100044666065)
                    ·
                      refine ⟨777431790575325033499549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036575720767100044666065 777431790575325033499549)
                      ·
                        rfl

theorem cell23_1514043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 2, 2].length) (baseStart_1514043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514043 prefixEnd_1514043 := by exact prefixLift 1514043
  have htrace : WordTrace (prefixWord ++ tailWord_1514043) baseStart_1514043 baseEnd_1514043 := by
    simpa [prefixWord, tailWord_1514043, baseEnd_1514043] using wordTrace_append hprefix tailTrace_1514043
  have hstable : (prefixWord ++ tailWord_1514043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514043).length < 2 ^ (prefixWord ++ tailWord_1514043).sum := by decide
  have hdescent : baseEnd_1514043 < baseStart_1514043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514056 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1514056 : Nat := 118140960795 + 1514056 * 2 ^ 59
def prefixEnd_1514056 : Nat := 4983230072969 + 3 ^ 40 * 1514056 * 2
def baseEnd_1514056 : Nat := 777438465823833482636989

theorem tailTrace_1514056 : CollatzResearch.WordTrace tailWord_1514056 prefixEnd_1514056 777438465823833482636989 := by
  unfold tailWord_1514056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611079501420583511645011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36814772668560778015526681 27611079501420583511645011)
  ·
    refine ⟨41416619252130875267467517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27611079501420583511645011 41416619252130875267467517)
    ·
      refine ⟨15531232219549078225300319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41416619252130875267467517 15531232219549078225300319)
      ·
        refine ⟨23296848329323617337950479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15531232219549078225300319 23296848329323617337950479)
        ·
          refine ⟨34945272493985426006925719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23296848329323617337950479 34945272493985426006925719)
          ·
            refine ⟨52417908740978139010388579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34945272493985426006925719 52417908740978139010388579)
            ·
              refine ⟨78626863111467208515582869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52417908740978139010388579 78626863111467208515582869)
              ·
                refine ⟨3685634208350025399167947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78626863111467208515582869 3685634208350025399167947)
                ·
                  refine ⟨5528451312525038098751921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685634208350025399167947 5528451312525038098751921)
                  ·
                    refine ⟨4146338484393778574063941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5528451312525038098751921 4146338484393778574063941)
                    ·
                      refine ⟨777438465823833482636989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4146338484393778574063941 777438465823833482636989)
                      ·
                        rfl

theorem cell23_1514056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1514056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514056 prefixEnd_1514056 := by exact prefixLift 1514056
  have htrace : WordTrace (prefixWord ++ tailWord_1514056) baseStart_1514056 baseEnd_1514056 := by
    simpa [prefixWord, tailWord_1514056, baseEnd_1514056] using wordTrace_append hprefix tailTrace_1514056
  have hstable : (prefixWord ++ tailWord_1514056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514056).length < 2 ^ (prefixWord ++ tailWord_1514056).sum := by decide
  have hdescent : baseEnd_1514056 < baseStart_1514056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514063 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_1514063 : Nat := 118140960795 + 1514063 * 2 ^ 59
def prefixEnd_1514063 : Nat := 4983230072969 + 3 ^ 40 * 1514063 * 2
def baseEnd_1514063 : Nat := 777442060188414955249457

theorem tailTrace_1514063 : CollatzResearch.WordTrace tailWord_1514063 prefixEnd_1514063 777442060188414955249457 := by
  unfold tailWord_1514063
  simp only [CollatzResearch.WordTrace]
  refine ⟨55222414313815807218794843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36814942875877204812529895 55222414313815807218794843)
  ·
    refine ⟨82833621470723710828192265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55222414313815807218794843 82833621470723710828192265)
    ·
      refine ⟨62125216103042783121144199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82833621470723710828192265 62125216103042783121144199)
      ·
        refine ⟨93187824154564174681716299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62125216103042783121144199 93187824154564174681716299)
        ·
          refine ⟨139781736231846262022574449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93187824154564174681716299 139781736231846262022574449)
          ·
            refine ⟨104836302173884696516930837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139781736231846262022574449 104836302173884696516930837)
            ·
              refine ⟨4914201664400845149231133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104836302173884696516930837 4914201664400845149231133)
              ·
                refine ⟨1842825624150316930961675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914201664400845149231133 1842825624150316930961675)
                ·
                  refine ⟨2764238436225475396442513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842825624150316930961675 2764238436225475396442513)
                  ·
                    refine ⟨2073178827169106547331885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2764238436225475396442513 2073178827169106547331885)
                    ·
                      refine ⟨777442060188414955249457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2073178827169106547331885 777442060188414955249457)
                      ·
                        rfl

theorem cell23_1514063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_1514063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514063 prefixEnd_1514063 := by exact prefixLift 1514063
  have htrace : WordTrace (prefixWord ++ tailWord_1514063) baseStart_1514063 baseEnd_1514063 := by
    simpa [prefixWord, tailWord_1514063, baseEnd_1514063] using wordTrace_append hprefix tailTrace_1514063
  have hstable : (prefixWord ++ tailWord_1514063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514063).length < 2 ^ (prefixWord ++ tailWord_1514063).sum := by decide
  have hdescent : baseEnd_1514063 < baseStart_1514063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514184 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_1514184 : Nat := 118140960795 + 1514184 * 2 ^ 59
def prefixEnd_1514184 : Nat := 4983230072969 + 3 ^ 40 * 1514184 * 2
def baseEnd_1514184 : Nat := 777504191347608981836401

theorem tailTrace_1514184 : CollatzResearch.WordTrace tailWord_1514184 prefixEnd_1514184 777504191347608981836401 := by
  unfold tailWord_1514184
  simp only [CollatzResearch.WordTrace]
  refine ⟨27613413773188722441974803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36817885030918296589299737 27613413773188722441974803)
  ·
    refine ⟨41420120659783083662962205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27613413773188722441974803 41420120659783083662962205)
    ·
      refine ⟨15532545247418656373610827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41420120659783083662962205 15532545247418656373610827)
      ·
        refine ⟨23298817871127984560416241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15532545247418656373610827 23298817871127984560416241)
        ·
          refine ⟨17474113403345988420312181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23298817871127984560416241 17474113403345988420312181)
          ·
            refine ⟨1638198131563686414404267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17474113403345988420312181 1638198131563686414404267)
            ·
              refine ⟨2457297197345529621606401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638198131563686414404267 2457297197345529621606401)
              ·
                refine ⟨1842972898009147216204801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457297197345529621606401 1842972898009147216204801)
                ·
                  refine ⟨1382229673506860412153601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842972898009147216204801 1382229673506860412153601)
                  ·
                    refine ⟨1036672255130145309115201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1382229673506860412153601 1036672255130145309115201)
                    ·
                      refine ⟨777504191347608981836401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036672255130145309115201 777504191347608981836401)
                      ·
                        rfl

theorem cell23_1514184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_1514184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514184 prefixEnd_1514184 := by exact prefixLift 1514184
  have htrace : WordTrace (prefixWord ++ tailWord_1514184) baseStart_1514184 baseEnd_1514184 := by
    simpa [prefixWord, tailWord_1514184, baseEnd_1514184] using wordTrace_append hprefix tailTrace_1514184
  have hstable : (prefixWord ++ tailWord_1514184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514184).length < 2 ^ (prefixWord ++ tailWord_1514184).sum := by decide
  have hdescent : baseEnd_1514184 < baseStart_1514184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514190 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_1514190 : Nat := 118140960795 + 1514190 * 2 ^ 59
def prefixEnd_1514190 : Nat := 4983230072969 + 3 ^ 40 * 1514190 * 2
def baseEnd_1514190 : Nat := 86389696914615106484597

theorem tailTrace_1514190 : CollatzResearch.WordTrace tailWord_1514190 prefixEnd_1514190 86389696914615106484597 := by
  unfold tailWord_1514190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903380798044463488583503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36818030922903805272445349 6903380798044463488583503)
  ·
    refine ⟨10355071197066695232875255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6903380798044463488583503 10355071197066695232875255)
    ·
      refine ⟨15532606795600042849312883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10355071197066695232875255 15532606795600042849312883)
      ·
        refine ⟨23298910193400064273969325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15532606795600042849312883 23298910193400064273969325)
        ·
          refine ⟨8737091322525024102738497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23298910193400064273969325 8737091322525024102738497)
          ·
            refine ⟨6552818491893768077053873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737091322525024102738497 6552818491893768077053873)
            ·
              refine ⟨4914613868920326057790405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552818491893768077053873 4914613868920326057790405)
              ·
                refine ⟨921490100422561135835701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4914613868920326057790405 921490100422561135835701)
                ·
                  refine ⟨86389696914615106484597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 921490100422561135835701 86389696914615106484597)
                  ·
                    rfl

theorem cell23_1514190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_1514190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514190 prefixEnd_1514190 := by exact prefixLift 1514190
  have htrace : WordTrace (prefixWord ++ tailWord_1514190) baseStart_1514190 baseEnd_1514190 := by
    simpa [prefixWord, tailWord_1514190, baseEnd_1514190] using wordTrace_append hprefix tailTrace_1514190
  have hstable : (prefixWord ++ tailWord_1514190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514190).length < 2 ^ (prefixWord ++ tailWord_1514190).sum := by decide
  have hdescent : baseEnd_1514190 < baseStart_1514190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514223 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_1514223 : Nat := 118140960795 + 1514223 * 2 ^ 59
def prefixEnd_1514223 : Nat := 4983230072969 + 3 ^ 40 * 1514223 * 2
def baseEnd_1514223 : Nat := 777524217093134329248721

theorem tailTrace_1514223 : CollatzResearch.WordTrace tailWord_1514223 prefixEnd_1514223 777524217093134329248721 := by
  unfold tailWord_1514223
  simp only [CollatzResearch.WordTrace]
  refine ⟨55228249993236154544619323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36818833328824103029746215 55228249993236154544619323)
  ·
    refine ⟨82842374989854231816928985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55228249993236154544619323 82842374989854231816928985)
    ·
      refine ⟨62131781242390673862696739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82842374989854231816928985 62131781242390673862696739)
      ·
        refine ⟨93197671863586010794045109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62131781242390673862696739 93197671863586010794045109)
        ·
          refine ⟨8737281737211188511941729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93197671863586010794045109 8737281737211188511941729)
          ·
            refine ⟨6552961302908391383956297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737281737211188511941729 6552961302908391383956297)
            ·
              refine ⟨4914720977181293537967223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552961302908391383956297 4914720977181293537967223)
              ·
                refine ⟨7372081465771940306950835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4914720977181293537967223 7372081465771940306950835)
                ·
                  refine ⟨11058122198657910460426253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7372081465771940306950835 11058122198657910460426253)
                  ·
                    refine ⟨4146795824496716422659845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11058122198657910460426253 4146795824496716422659845)
                    ·
                      refine ⟨777524217093134329248721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4146795824496716422659845 777524217093134329248721)
                      ·
                        rfl

theorem cell23_1514223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_1514223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514223 prefixEnd_1514223 := by exact prefixLift 1514223
  have htrace : WordTrace (prefixWord ++ tailWord_1514223) baseStart_1514223 baseEnd_1514223 := by
    simpa [prefixWord, tailWord_1514223, baseEnd_1514223] using wordTrace_append hprefix tailTrace_1514223
  have hstable : (prefixWord ++ tailWord_1514223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514223).length < 2 ^ (prefixWord ++ tailWord_1514223).sum := by decide
  have hdescent : baseEnd_1514223 < baseStart_1514223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514233 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_1514233 : Nat := 118140960795 + 1514233 * 2 ^ 59
def prefixEnd_1514233 : Nat := 4983230072969 + 3 ^ 40 * 1514233 * 2
def baseEnd_1514233 : Nat := 259176450633226430041225

theorem tailTrace_1514233 : CollatzResearch.WordTrace tailWord_1514233 prefixEnd_1514233 259176450633226430041225 := by
  unfold tailWord_1514233
  simp only [CollatzResearch.WordTrace]
  refine ⟨55228614723199926252483353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36819076482133284168322235 55228614723199926252483353)
  ·
    refine ⟨41421461042399944689362515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55228614723199926252483353 41421461042399944689362515)
    ·
      refine ⟨62132191563599917034043773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41421461042399944689362515 62132191563599917034043773)
      ·
        refine ⟨23299571836349968887766415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62132191563599917034043773 23299571836349968887766415)
        ·
          refine ⟨34949357754524953331649623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23299571836349968887766415 34949357754524953331649623)
          ·
            refine ⟨52424036631787429997474435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34949357754524953331649623 52424036631787429997474435)
            ·
              refine ⟨78636054947681144996211653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52424036631787429997474435 78636054947681144996211653)
              ·
                refine ⟨14744260302690214686789685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78636054947681144996211653 14744260302690214686789685)
                ·
                  refine ⟨1382274403377207626886533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14744260302690214686789685 1382274403377207626886533)
                  ·
                    refine ⟨259176450633226430041225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382274403377207626886533 259176450633226430041225)
                    ·
                      rfl

theorem cell23_1514233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_1514233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514233 prefixEnd_1514233 := by exact prefixLift 1514233
  have htrace : WordTrace (prefixWord ++ tailWord_1514233) baseStart_1514233 baseEnd_1514233 := by
    simpa [prefixWord, tailWord_1514233, baseEnd_1514233] using wordTrace_append hprefix tailTrace_1514233
  have hstable : (prefixWord ++ tailWord_1514233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514233).length < 2 ^ (prefixWord ++ tailWord_1514233).sum := by decide
  have hdescent : baseEnd_1514233 < baseStart_1514233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514300 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_1514300 : Nat := 118140960795 + 1514300 * 2 ^ 59
def prefixEnd_1514300 : Nat := 4983230072969 + 3 ^ 40 * 1514300 * 2
def baseEnd_1514300 : Nat := 777563755103530527985867

theorem tailTrace_1514300 : CollatzResearch.WordTrace tailWord_1514300 prefixEnd_1514300 777563755103530527985867 := by
  unfold tailWord_1514300
  simp only [CollatzResearch.WordTrace]
  refine ⟨27615529206978598347586177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36820705609304797796781569 27615529206978598347586177)
  ·
    refine ⟨20711646905233948760689633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27615529206978598347586177 20711646905233948760689633)
    ·
      refine ⟨15533735178925461570517225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20711646905233948760689633 15533735178925461570517225)
      ·
        refine ⟨11650301384194096177887919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15533735178925461570517225 11650301384194096177887919)
        ·
          refine ⟨17475452076291144266831879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11650301384194096177887919 17475452076291144266831879)
          ·
            refine ⟨26213178114436716400247819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17475452076291144266831879 26213178114436716400247819)
            ·
              refine ⟨39319767171655074600371729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26213178114436716400247819 39319767171655074600371729)
              ·
                refine ⟨29489825378741305950278797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39319767171655074600371729 29489825378741305950278797)
                ·
                  refine ⟨11058684517027989731354549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29489825378741305950278797 11058684517027989731354549)
                  ·
                    refine ⟨1036751673471374037314489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11058684517027989731354549 1036751673471374037314489)
                    ·
                      refine ⟨777563755103530527985867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036751673471374037314489 777563755103530527985867)
                      ·
                        rfl

theorem cell23_1514300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_1514300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514300 prefixEnd_1514300 := by exact prefixLift 1514300
  have htrace : WordTrace (prefixWord ++ tailWord_1514300) baseStart_1514300 baseEnd_1514300 := by
    simpa [prefixWord, tailWord_1514300, baseEnd_1514300] using wordTrace_append hprefix tailTrace_1514300
  have hstable : (prefixWord ++ tailWord_1514300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514300).length < 2 ^ (prefixWord ++ tailWord_1514300).sum := by decide
  have hdescent : baseEnd_1514300 < baseStart_1514300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514324 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1514324 : Nat := 118140960795 + 1514324 * 2 ^ 59
def prefixEnd_1514324 : Nat := 4983230072969 + 3 ^ 40 * 1514324 * 2
def baseEnd_1514324 : Nat := 777576078639238434085757

theorem tailTrace_1514324 : CollatzResearch.WordTrace tailWord_1514324 prefixEnd_1514324 777576078639238434085757 := by
  unfold tailWord_1514324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27615966882935124397023013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36821289177246832529364017 27615966882935124397023013)
  ·
    refine ⟨5177993790550335824441815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27615966882935124397023013 5177993790550335824441815)
    ·
      refine ⟨7766990685825503736662723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177993790550335824441815 7766990685825503736662723)
      ·
        refine ⟨11650486028738255604994085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766990685825503736662723 11650486028738255604994085)
        ·
          refine ⟨2184466130388422925936391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11650486028738255604994085 2184466130388422925936391)
          ·
            refine ⟨3276699195582634388904587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184466130388422925936391 3276699195582634388904587)
            ·
              refine ⟨4915048793373951583356881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276699195582634388904587 4915048793373951583356881)
              ·
                refine ⟨3686286595030463687517661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915048793373951583356881 3686286595030463687517661)
                ·
                  refine ⟨1382357473136423882819123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3686286595030463687517661 1382357473136423882819123)
                  ·
                    refine ⟨2073536209704635824228685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1382357473136423882819123 2073536209704635824228685)
                    ·
                      refine ⟨777576078639238434085757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2073536209704635824228685 777576078639238434085757)
                      ·
                        rfl

theorem cell23_1514324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1514324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514324 prefixEnd_1514324 := by exact prefixLift 1514324
  have htrace : WordTrace (prefixWord ++ tailWord_1514324) baseStart_1514324 baseEnd_1514324 := by
    simpa [prefixWord, tailWord_1514324, baseEnd_1514324] using wordTrace_append hprefix tailTrace_1514324
  have hstable : (prefixWord ++ tailWord_1514324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514324).length < 2 ^ (prefixWord ++ tailWord_1514324).sum := by decide
  have hdescent : baseEnd_1514324 < baseStart_1514324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514330 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1514330 : Nat := 118140960795 + 1514330 * 2 ^ 59
def prefixEnd_1514330 : Nat := 4983230072969 + 3 ^ 40 * 1514330 * 2
def baseEnd_1514330 : Nat := 777579159523165410610729

theorem tailTrace_1514330 : CollatzResearch.WordTrace tailWord_1514330 prefixEnd_1514330 777579159523165410610729 := by
  unfold tailWord_1514330
  simp only [CollatzResearch.WordTrace]
  refine ⟨13808038150962127954691111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36821435069232341212509629 13808038150962127954691111)
  ·
    refine ⟨20712057226443191932036667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13808038150962127954691111 20712057226443191932036667)
    ·
      refine ⟨31068085839664787898055001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20712057226443191932036667 31068085839664787898055001)
      ·
        refine ⟨23301064379748590923541251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31068085839664787898055001 23301064379748590923541251)
        ·
          refine ⟨34951596569622886385311877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23301064379748590923541251 34951596569622886385311877)
          ·
            refine ⟨6553424356804291197245977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34951596569622886385311877 6553424356804291197245977)
            ·
              refine ⟨4915068267603218397934483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553424356804291197245977 4915068267603218397934483)
              ·
                refine ⟨7372602401404827596901725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915068267603218397934483 7372602401404827596901725)
                ·
                  refine ⟨2764725900526810348838147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7372602401404827596901725 2764725900526810348838147)
                  ·
                    refine ⟨4147088850790215523257221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2764725900526810348838147 4147088850790215523257221)
                    ·
                      refine ⟨777579159523165410610729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4147088850790215523257221 777579159523165410610729)
                      ·
                        rfl

theorem cell23_1514330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1514330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514330 prefixEnd_1514330 := by exact prefixLift 1514330
  have htrace : WordTrace (prefixWord ++ tailWord_1514330) baseStart_1514330 baseEnd_1514330 := by
    simpa [prefixWord, tailWord_1514330, baseEnd_1514330] using wordTrace_append hprefix tailTrace_1514330
  have hstable : (prefixWord ++ tailWord_1514330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514330).length < 2 ^ (prefixWord ++ tailWord_1514330).sum := by decide
  have hdescent : baseEnd_1514330 < baseStart_1514330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514340 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1514340 : Nat := 118140960795 + 1514340 * 2 ^ 59
def prefixEnd_1514340 : Nat := 4983230072969 + 3 ^ 40 * 1514340 * 2
def baseEnd_1514340 : Nat := 259194764776570123828561

theorem tailTrace_1514340 : CollatzResearch.WordTrace tailWord_1514340 prefixEnd_1514340 259194764776570123828561 := by
  unfold tailWord_1514340
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616258666906141763314237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36821678222541522351085649 27616258666906141763314237)
  ·
    refine ⟨10356097000089803161242839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27616258666906141763314237 10356097000089803161242839)
    ·
      refine ⟨15534145500134704741864259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356097000089803161242839 15534145500134704741864259)
      ·
        refine ⟨23301218250202057112796389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15534145500134704741864259 23301218250202057112796389)
        ·
          refine ⟨4368978421912885708649323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23301218250202057112796389 4368978421912885708649323)
          ·
            refine ⟨6553467632869328562973985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4368978421912885708649323 6553467632869328562973985)
            ·
              refine ⟨4915100724651996422230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553467632869328562973985 4915100724651996422230489)
              ·
                refine ⟨3686325543488997316672867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915100724651996422230489 3686325543488997316672867)
                ·
                  refine ⟨5529488315233495975009301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686325543488997316672867 5529488315233495975009301)
                  ·
                    refine ⟨259194764776570123828561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5529488315233495975009301 259194764776570123828561)
                    ·
                      rfl

theorem cell23_1514340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1514340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514340 prefixEnd_1514340 := by exact prefixLift 1514340
  have htrace : WordTrace (prefixWord ++ tailWord_1514340) baseStart_1514340 baseEnd_1514340 := by
    simpa [prefixWord, tailWord_1514340, baseEnd_1514340] using wordTrace_append hprefix tailTrace_1514340
  have hstable : (prefixWord ++ tailWord_1514340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514340).length < 2 ^ (prefixWord ++ tailWord_1514340).sum := by decide
  have hdescent : baseEnd_1514340 < baseStart_1514340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514344 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1514344 : Nat := 118140960795 + 1514344 * 2 ^ 59
def prefixEnd_1514344 : Nat := 4983230072969 + 3 ^ 40 * 1514344 * 2
def baseEnd_1514344 : Nat := 259195449417442785278555

theorem tailTrace_1514344 : CollatzResearch.WordTrace tailWord_1514344 prefixEnd_1514344 259195449417442785278555 := by
  unfold tailWord_1514344
  simp only [CollatzResearch.WordTrace]
  refine ⟨27616331612898896104887043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36821775483865194806516057 27616331612898896104887043)
  ·
    refine ⟨41424497419348344157330565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27616331612898896104887043 41424497419348344157330565)
    ·
      refine ⟨7767093266127814529499481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41424497419348344157330565 7767093266127814529499481)
      ·
        refine ⟨5825319949595860897124611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7767093266127814529499481 5825319949595860897124611)
        ·
          refine ⟨8737979924393791345686917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5825319949595860897124611 8737979924393791345686917)
          ·
            refine ⟨1638371235823835877316297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8737979924393791345686917 1638371235823835877316297)
            ·
              refine ⟨1228778426867876907987223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638371235823835877316297 1228778426867876907987223)
              ·
                refine ⟨1843167640301815361980835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228778426867876907987223 1843167640301815361980835)
                ·
                  refine ⟨2764751460452723042971253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843167640301815361980835 2764751460452723042971253)
                  ·
                    refine ⟨259195449417442785278555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2764751460452723042971253 259195449417442785278555)
                    ·
                      rfl

theorem cell23_1514344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1514344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514344 prefixEnd_1514344 := by exact prefixLift 1514344
  have htrace : WordTrace (prefixWord ++ tailWord_1514344) baseStart_1514344 baseEnd_1514344 := by
    simpa [prefixWord, tailWord_1514344, baseEnd_1514344] using wordTrace_append hprefix tailTrace_1514344
  have hstable : (prefixWord ++ tailWord_1514344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514344).length < 2 ^ (prefixWord ++ tailWord_1514344).sum := by decide
  have hdescent : baseEnd_1514344 < baseStart_1514344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514347 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 1, 1, 4]
def baseStart_1514347 : Nat := 118140960795 + 1514347 * 2 ^ 59
def prefixEnd_1514347 : Nat := 4983230072969 + 3 ^ 40 * 1514347 * 2
def baseEnd_1514347 : Nat := 777587888694291844098151

theorem tailTrace_1514347 : CollatzResearch.WordTrace tailWord_1514347 prefixEnd_1514347 777587888694291844098151 := by
  unfold tailWord_1514347
  simp only [CollatzResearch.WordTrace]
  refine ⟨55232772644786923722133295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36821848429857949148088863 55232772644786923722133295)
  ·
    refine ⟨82849158967180385583199943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55232772644786923722133295 82849158967180385583199943)
    ·
      refine ⟨124273738450770578374799915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82849158967180385583199943 124273738450770578374799915)
      ·
        refine ⟨186410607676155867562199873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124273738450770578374799915 186410607676155867562199873)
        ·
          refine ⟨139807955757116900671649905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186410607676155867562199873 139807955757116900671649905)
          ·
            refine ⟨104855966817837675503737429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139807955757116900671649905 104855966817837675503737429)
            ·
              refine ⟨1228780861146535259809423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 104855966817837675503737429 1228780861146535259809423)
              ·
                refine ⟨1843171291719802889714135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228780861146535259809423 1843171291719802889714135)
                ·
                  refine ⟨2764756937579704334571203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843171291719802889714135 2764756937579704334571203)
                  ·
                    refine ⟨4147135406369556501856805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2764756937579704334571203 4147135406369556501856805)
                    ·
                      refine ⟨777587888694291844098151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4147135406369556501856805 777587888694291844098151)
                      ·
                        rfl

theorem cell23_1514347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 1, 4].length) (baseStart_1514347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514347 prefixEnd_1514347 := by exact prefixLift 1514347
  have htrace : WordTrace (prefixWord ++ tailWord_1514347) baseStart_1514347 baseEnd_1514347 := by
    simpa [prefixWord, tailWord_1514347, baseEnd_1514347] using wordTrace_append hprefix tailTrace_1514347
  have hstable : (prefixWord ++ tailWord_1514347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514347).length < 2 ^ (prefixWord ++ tailWord_1514347).sum := by decide
  have hdescent : baseEnd_1514347 < baseStart_1514347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514353 : List Nat := [1, 2, 2, 2, 1, 5, 10]
def baseStart_1514353 : Nat := 118140960795 + 1514353 * 2 ^ 59
def prefixEnd_1514353 : Nat := 4983230072969 + 3 ^ 40 * 1514353 * 2
def baseEnd_1514353 : Nat := 9599888513311343464483

theorem tailTrace_1514353 : CollatzResearch.WordTrace tailWord_1514353 prefixEnd_1514353 9599888513311343464483 := by
  unfold tailWord_1514353
  simp only [CollatzResearch.WordTrace]
  refine ⟨55232991482765186746851713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36821994321843457831234475 55232991482765186746851713)
  ·
    refine ⟨41424743612073890060138785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55232991482765186746851713 41424743612073890060138785)
    ·
      refine ⟨31068557709055417545104089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41424743612073890060138785 31068557709055417545104089)
      ·
        refine ⟨23301418281791563158828067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31068557709055417545104089 23301418281791563158828067)
        ·
          refine ⟨34952127422687344738242101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23301418281791563158828067 34952127422687344738242101)
          ·
            refine ⟨3276761945876938569210197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34952127422687344738242101 3276761945876938569210197)
            ·
              refine ⟨9599888513311343464483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3276761945876938569210197 9599888513311343464483)
              ·
                rfl

theorem cell23_1514353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 10].length) (baseStart_1514353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514353 prefixEnd_1514353 := by exact prefixLift 1514353
  have htrace : WordTrace (prefixWord ++ tailWord_1514353) baseStart_1514353 baseEnd_1514353 := by
    simpa [prefixWord, tailWord_1514353, baseEnd_1514353] using wordTrace_append hprefix tailTrace_1514353
  have hstable : (prefixWord ++ tailWord_1514353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514353).length < 2 ^ (prefixWord ++ tailWord_1514353).sum := by decide
  have hdescent : baseEnd_1514353 < baseStart_1514353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514357 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1514357 : Nat := 118140960795 + 1514357 * 2 ^ 59
def prefixEnd_1514357 : Nat := 4983230072969 + 3 ^ 40 * 1514357 * 2
def baseEnd_1514357 : Nat := 259197674500278934991035

theorem tailTrace_1514357 : CollatzResearch.WordTrace tailWord_1514357 prefixEnd_1514357 259197674500278934991035 := by
  unfold tailWord_1514357
  simp only [CollatzResearch.WordTrace]
  refine ⟨55233137374750695429997325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36822091583167130286664883 55233137374750695429997325)
  ·
    refine ⟨20712426515531510786248997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55233137374750695429997325 20712426515531510786248997)
    ·
      refine ⟨3883579971662158272421687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20712426515531510786248997 3883579971662158272421687)
      ·
        refine ⟨5825369957493237408632531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883579971662158272421687 5825369957493237408632531)
        ·
          refine ⟨8738054936239856112948797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5825369957493237408632531 8738054936239856112948797)
          ·
            refine ⟨3276770601089946042355799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8738054936239856112948797 3276770601089946042355799)
            ·
              refine ⟨4915155901634919063533699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276770601089946042355799 4915155901634919063533699)
              ·
                refine ⟨7372733852452378595300549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915155901634919063533699 7372733852452378595300549)
                ·
                  refine ⟨1382387597334820986618853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7372733852452378595300549 1382387597334820986618853)
                  ·
                    refine ⟨259197674500278934991035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382387597334820986618853 259197674500278934991035)
                    ·
                      rfl

theorem cell23_1514357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1514357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514357 prefixEnd_1514357 := by exact prefixLift 1514357
  have htrace : WordTrace (prefixWord ++ tailWord_1514357) baseStart_1514357 baseEnd_1514357 := by
    simpa [prefixWord, tailWord_1514357, baseEnd_1514357] using wordTrace_append hprefix tailTrace_1514357
  have hstable : (prefixWord ++ tailWord_1514357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514357).length < 2 ^ (prefixWord ++ tailWord_1514357).sum := by decide
  have hdescent : baseEnd_1514357 < baseStart_1514357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514377 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_1514377 : Nat := 118140960795 + 1514377 * 2 ^ 59
def prefixEnd_1514377 : Nat := 4983230072969 + 3 ^ 40 * 1514377 * 2
def baseEnd_1514377 : Nat := 777603293113926726723013

theorem tailTrace_1514377 : CollatzResearch.WordTrace tailWord_1514377 prefixEnd_1514377 777603293113926726723013 := by
  unfold tailWord_1514377
  simp only [CollatzResearch.WordTrace]
  refine ⟨55233866834678238845725385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36822577889785492563816923 55233866834678238845725385)
  ·
    refine ⟨41425400126008679134294039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55233866834678238845725385 41425400126008679134294039)
    ·
      refine ⟨62138100189013018701441059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41425400126008679134294039 62138100189013018701441059)
      ·
        refine ⟨93207150283519528052161589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62138100189013018701441059 93207150283519528052161589)
        ·
          refine ⟨8738170339079955754890149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93207150283519528052161589 8738170339079955754890149)
          ·
            refine ⟨1638406938577491704041903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8738170339079955754890149 1638406938577491704041903)
            ·
              refine ⟨2457610407866237556062855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638406938577491704041903 2457610407866237556062855)
              ·
                refine ⟨3686415611799356334094283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457610407866237556062855 3686415611799356334094283)
                ·
                  refine ⟨5529623417699034501141425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686415611799356334094283 5529623417699034501141425)
                  ·
                    refine ⟨4147217563274275875856069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5529623417699034501141425 4147217563274275875856069)
                    ·
                      refine ⟨777603293113926726723013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4147217563274275875856069 777603293113926726723013)
                      ·
                        rfl

theorem cell23_1514377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_1514377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514377 prefixEnd_1514377 := by exact prefixLift 1514377
  have htrace : WordTrace (prefixWord ++ tailWord_1514377) baseStart_1514377 baseEnd_1514377 := by
    simpa [prefixWord, tailWord_1514377, baseEnd_1514377] using wordTrace_append hprefix tailTrace_1514377
  have hstable : (prefixWord ++ tailWord_1514377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514377).length < 2 ^ (prefixWord ++ tailWord_1514377).sum := by decide
  have hdescent : baseEnd_1514377 < baseStart_1514377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514397 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1514397 : Nat := 118140960795 + 1514397 * 2 ^ 59
def prefixEnd_1514397 : Nat := 4983230072969 + 3 ^ 40 * 1514397 * 2
def baseEnd_1514397 : Nat := 777613562727016648472921

theorem tailTrace_1514397 : CollatzResearch.WordTrace tailWord_1514397 prefixEnd_1514397 777613562727016648472921 := by
  unfold tailWord_1514397
  simp only [CollatzResearch.WordTrace]
  refine ⟨55234596294605782261453445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36823064196403854840968963 55234596294605782261453445)
  ·
    refine ⟨10356486805238584174022521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55234596294605782261453445 10356486805238584174022521)
    ·
      refine ⟨7767365103928938130516891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10356486805238584174022521 7767365103928938130516891)
      ·
        refine ⟨11651047655893407195775337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767365103928938130516891 11651047655893407195775337)
        ·
          refine ⟨8738285741920055396831503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11651047655893407195775337 8738285741920055396831503)
          ·
            refine ⟨13107428612880083095247255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8738285741920055396831503 13107428612880083095247255)
            ·
              refine ⟨19661142919320124642870883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13107428612880083095247255 19661142919320124642870883)
              ·
                refine ⟨29491714378980186964306325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19661142919320124642870883 29491714378980186964306325)
                ·
                  refine ⟨1382424111514696263951859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29491714378980186964306325 1382424111514696263951859)
                  ·
                    refine ⟨2073636167272044395927789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1382424111514696263951859 2073636167272044395927789)
                    ·
                      refine ⟨777613562727016648472921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2073636167272044395927789 777613562727016648472921)
                      ·
                        rfl

theorem cell23_1514397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1514397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514397 prefixEnd_1514397 := by exact prefixLift 1514397
  have htrace : WordTrace (prefixWord ++ tailWord_1514397) baseStart_1514397 baseEnd_1514397 := by
    simpa [prefixWord, tailWord_1514397, baseEnd_1514397] using wordTrace_append hprefix tailTrace_1514397
  have hstable : (prefixWord ++ tailWord_1514397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514397).length < 2 ^ (prefixWord ++ tailWord_1514397).sum := by decide
  have hdescent : baseEnd_1514397 < baseStart_1514397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514430 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1514430 : Nat := 118140960795 + 1514430 * 2 ^ 59
def prefixEnd_1514430 : Nat := 4983230072969 + 3 ^ 40 * 1514430 * 2
def baseEnd_1514430 : Nat := 259210169196205006453423

theorem tailTrace_1514430 : CollatzResearch.WordTrace tailWord_1514430 prefixEnd_1514430 259210169196205006453423 := by
  unfold tailWord_1514430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904474987935778612175593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36823866602324152598269829 6904474987935778612175593)
  ·
    refine ⟨5178356240951833959131695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6904474987935778612175593 5178356240951833959131695)
    ·
      refine ⟨7767534361427750938697543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178356240951833959131695 7767534361427750938697543)
      ·
        refine ⟨11651301542141626408046315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767534361427750938697543 11651301542141626408046315)
        ·
          refine ⟨17476952313212439612069473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11651301542141626408046315 17476952313212439612069473)
          ·
            refine ⟨13107714234909329709052105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17476952313212439612069473 13107714234909329709052105)
            ·
              refine ⟨9830785676181997281789079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13107714234909329709052105 9830785676181997281789079)
              ·
                refine ⟨14746178514272995922683619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9830785676181997281789079 14746178514272995922683619)
                ·
                  refine ⟨22119267771409493884025429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14746178514272995922683619 22119267771409493884025429)
                  ·
                    refine ⟨259210169196205006453423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22119267771409493884025429 259210169196205006453423)
                    ·
                      rfl

theorem cell23_1514430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1514430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514430 prefixEnd_1514430 := by exact prefixLift 1514430
  have htrace : WordTrace (prefixWord ++ tailWord_1514430) baseStart_1514430 baseEnd_1514430 := by
    simpa [prefixWord, tailWord_1514430, baseEnd_1514430] using wordTrace_append hprefix tailTrace_1514430
  have hstable : (prefixWord ++ tailWord_1514430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514430).length < 2 ^ (prefixWord ++ tailWord_1514430).sum := by decide
  have hdescent : baseEnd_1514430 < baseStart_1514430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514471 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1514471 : Nat := 118140960795 + 1514471 * 2 ^ 59
def prefixEnd_1514471 : Nat := 4983230072969 + 3 ^ 40 * 1514471 * 2
def baseEnd_1514471 : Nat := 777651560295449358947581

theorem tailTrace_1514471 : CollatzResearch.WordTrace tailWord_1514471 prefixEnd_1514471 777651560295449358947581 := by
  unfold tailWord_1514471
  simp only [CollatzResearch.WordTrace]
  refine ⟨55237295296337692899647267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36824863530891795266431511 55237295296337692899647267)
  ·
    refine ⟨82855942944506539349470901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55237295296337692899647267 82855942944506539349470901)
    ·
      refine ⟨7767744651047488064012897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82855942944506539349470901 7767744651047488064012897)
      ·
        refine ⟨5825808488285616048009673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7767744651047488064012897 5825808488285616048009673)
        ·
          refine ⟨4369356366214212036007255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5825808488285616048009673 4369356366214212036007255)
          ·
            refine ⟨6554034549321318054010883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369356366214212036007255 6554034549321318054010883)
            ·
              refine ⟨9831051823981977081016325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6554034549321318054010883 9831051823981977081016325)
              ·
                refine ⟨1843322216996620702690561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9831051823981977081016325 1843322216996620702690561)
                ·
                  refine ⟨1382491662747465527017921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1843322216996620702690561 1382491662747465527017921)
                  ·
                    refine ⟨1036868747060599145263441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1382491662747465527017921 1036868747060599145263441)
                    ·
                      refine ⟨777651560295449358947581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036868747060599145263441 777651560295449358947581)
                      ·
                        rfl

theorem cell23_1514471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1514471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514471 prefixEnd_1514471 := by exact prefixLift 1514471
  have htrace : WordTrace (prefixWord ++ tailWord_1514471) baseStart_1514471 baseEnd_1514471 := by
    simpa [prefixWord, tailWord_1514471, baseEnd_1514471] using wordTrace_append hprefix tailTrace_1514471
  have hstable : (prefixWord ++ tailWord_1514471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514471).length < 2 ^ (prefixWord ++ tailWord_1514471).sum := by decide
  have hdescent : baseEnd_1514471 < baseStart_1514471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514490 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_1514490 : Nat := 118140960795 + 1514490 * 2 ^ 59
def prefixEnd_1514490 : Nat := 4983230072969 + 3 ^ 40 * 1514490 * 2
def baseEnd_1514490 : Nat := 259220438809294928203331

theorem tailTrace_1514490 : CollatzResearch.WordTrace tailWord_1514490 prefixEnd_1514490 259220438809294928203331 := by
  unfold tailWord_1514490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809497070817214786147231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36825325522179239429725949 13809497070817214786147231)
  ·
    refine ⟨20714245606225822179220847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13809497070817214786147231 20714245606225822179220847)
    ·
      refine ⟨31071368409338733268831271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20714245606225822179220847 31071368409338733268831271)
      ·
        refine ⟨46607052614008099903246907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31071368409338733268831271 46607052614008099903246907)
        ·
          refine ⟨69910578921012149854870361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46607052614008099903246907 69910578921012149854870361)
          ·
            refine ⟨52432934190759112391152771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69910578921012149854870361 52432934190759112391152771)
            ·
              refine ⟨78649401286138668586729157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52432934190759112391152771 78649401286138668586729157)
              ·
                refine ⟨14746762741151000360011717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78649401286138668586729157 14746762741151000360011717)
                ·
                  refine ⟨2765018013965812567502197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14746762741151000360011717 2765018013965812567502197)
                  ·
                    refine ⟨259220438809294928203331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2765018013965812567502197 259220438809294928203331)
                    ·
                      rfl

theorem cell23_1514490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_1514490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514490 prefixEnd_1514490 := by exact prefixLift 1514490
  have htrace : WordTrace (prefixWord ++ tailWord_1514490) baseStart_1514490 baseEnd_1514490 := by
    simpa [prefixWord, tailWord_1514490, baseEnd_1514490] using wordTrace_append hprefix tailTrace_1514490
  have hstable : (prefixWord ++ tailWord_1514490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514490).length < 2 ^ (prefixWord ++ tailWord_1514490).sum := by decide
  have hdescent : baseEnd_1514490 < baseStart_1514490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514494 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_1514494 : Nat := 118140960795 + 1514494 * 2 ^ 59
def prefixEnd_1514494 : Nat := 4983230072969 + 3 ^ 40 * 1514494 * 2
def baseEnd_1514494 : Nat := 86407041150055863217775

theorem tailTrace_1514494 : CollatzResearch.WordTrace tailWord_1514494 prefixEnd_1514494 86407041150055863217775 := by
  unfold tailWord_1514494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904766771906795978466817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36825422783502911885156357 6904766771906795978466817)
  ·
    refine ⟨5178575078930096983850113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6904766771906795978466817 5178575078930096983850113)
    ·
      refine ⟨3883931309197572737887585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5178575078930096983850113 3883931309197572737887585)
      ·
        refine ⟨2912948481898179553415689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3883931309197572737887585 2912948481898179553415689)
        ·
          refine ⟨2184711361423634665061767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2912948481898179553415689 2184711361423634665061767)
          ·
            refine ⟨3277067042135451997592651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184711361423634665061767 3277067042135451997592651)
            ·
              refine ⟨4915600563203177996388977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277067042135451997592651 4915600563203177996388977)
              ·
                refine ⟨3686700422402383497291733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915600563203177996388977 3686700422402383497291733)
                ·
                  refine ⟨86407041150055863217775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3686700422402383497291733 86407041150055863217775)
                  ·
                    rfl

theorem cell23_1514494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_1514494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514494 prefixEnd_1514494 := by exact prefixLift 1514494
  have htrace : WordTrace (prefixWord ++ tailWord_1514494) baseStart_1514494 baseEnd_1514494 := by
    simpa [prefixWord, tailWord_1514494, baseEnd_1514494] using wordTrace_append hprefix tailTrace_1514494
  have hstable : (prefixWord ++ tailWord_1514494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514494).length < 2 ^ (prefixWord ++ tailWord_1514494).sum := by decide
  have hdescent : baseEnd_1514494 < baseStart_1514494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514507 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 2, 5]
def baseStart_1514507 : Nat := 118140960795 + 1514507 * 2 ^ 59
def prefixEnd_1514507 : Nat := 4983230072969 + 3 ^ 40 * 1514507 * 2
def baseEnd_1514507 : Nat := 259223348533003739365805

theorem tailTrace_1514507 : CollatzResearch.WordTrace tailWord_1514507 prefixEnd_1514507 259223348533003739365805 := by
  unfold tailWord_1514507
  simp only [CollatzResearch.WordTrace]
  refine ⟨55238608324207271047957775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36825738882804847365305183 55238608324207271047957775)
  ·
    refine ⟨82857912486310906571936663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55238608324207271047957775 82857912486310906571936663)
    ·
      refine ⟨124286868729466359857904995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82857912486310906571936663 124286868729466359857904995)
      ·
        refine ⟨186430303094199539786857493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124286868729466359857904995 186430303094199539786857493)
        ·
          refine ⟨8738920457540603427508945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186430303094199539786857493 8738920457540603427508945)
          ·
            refine ⟨6554190343155452570631709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8738920457540603427508945 6554190343155452570631709)
            ·
              refine ⟨2457821378683294713986891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6554190343155452570631709 2457821378683294713986891)
              ·
                refine ⟨3686732068024942070980337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457821378683294713986891 3686732068024942070980337)
                ·
                  refine ⟨2765049051018706553235253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3686732068024942070980337 2765049051018706553235253)
                  ·
                    refine ⟨259223348533003739365805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2765049051018706553235253 259223348533003739365805)
                    ·
                      rfl

theorem cell23_1514507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 5].length) (baseStart_1514507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514507 prefixEnd_1514507 := by exact prefixLift 1514507
  have htrace : WordTrace (prefixWord ++ tailWord_1514507) baseStart_1514507 baseEnd_1514507 := by
    simpa [prefixWord, tailWord_1514507, baseEnd_1514507] using wordTrace_append hprefix tailTrace_1514507
  have hstable : (prefixWord ++ tailWord_1514507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514507).length < 2 ^ (prefixWord ++ tailWord_1514507).sum := by decide
  have hdescent : baseEnd_1514507 < baseStart_1514507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514540 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1514540 : Nat := 118140960795 + 1514540 * 2 ^ 59
def prefixEnd_1514540 : Nat := 4983230072969 + 3 ^ 40 * 1514540 * 2
def baseEnd_1514540 : Nat := 777686990460609588984763

theorem tailTrace_1514540 : CollatzResearch.WordTrace tailWord_1514540 prefixEnd_1514540 777686990460609588984763 := by
  unfold tailWord_1514540
  simp only [CollatzResearch.WordTrace]
  refine ⟨27619905966543858841954537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36826541288725145122606049 27619905966543858841954537)
  ·
    refine ⟨20714929474907894131465903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27619905966543858841954537 20714929474907894131465903)
    ·
      refine ⟨31072394212361841197198855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20714929474907894131465903 31072394212361841197198855)
      ·
        refine ⟨46608591318542761795798283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31072394212361841197198855 46608591318542761795798283)
        ·
          refine ⟨69912886977814142693697425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46608591318542761795798283 69912886977814142693697425)
          ·
            refine ⟨52434665233360607020273069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69912886977814142693697425 52434665233360607020273069)
            ·
              refine ⟨19662999462510227632602401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52434665233360607020273069 19662999462510227632602401)
              ·
                refine ⟨14747249596882670724451801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19662999462510227632602401 14747249596882670724451801)
                ·
                  refine ⟨11060437197662003043338851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14747249596882670724451801 11060437197662003043338851)
                  ·
                    refine ⟨16590655796493004565008277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11060437197662003043338851 16590655796493004565008277)
                    ·
                      refine ⟨777686990460609588984763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16590655796493004565008277 777686990460609588984763)
                      ·
                        rfl

theorem cell23_1514540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1514540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514540 prefixEnd_1514540 := by exact prefixLift 1514540
  have htrace : WordTrace (prefixWord ++ tailWord_1514540) baseStart_1514540 baseEnd_1514540 := by
    simpa [prefixWord, tailWord_1514540, baseEnd_1514540] using wordTrace_append hprefix tailTrace_1514540
  have hstable : (prefixWord ++ tailWord_1514540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514540).length < 2 ^ (prefixWord ++ tailWord_1514540).sum := by decide
  have hdescent : baseEnd_1514540 < baseStart_1514540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514588 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1514588 : Nat := 118140960795 + 1514588 * 2 ^ 59
def prefixEnd_1514588 : Nat := 4983230072969 + 3 ^ 40 * 1514588 * 2
def baseEnd_1514588 : Nat := 259237212510675133728181

theorem tailTrace_1514588 : CollatzResearch.WordTrace tailWord_1514588 prefixEnd_1514588 259237212510675133728181 := by
  unfold tailWord_1514588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27620781318456910940828209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36827708424609214587770945 27620781318456910940828209)
  ·
    refine ⟨20715585988842683205621157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27620781318456910940828209 20715585988842683205621157)
    ·
      refine ⟨3884172372908003101053967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20715585988842683205621157 3884172372908003101053967)
      ·
        refine ⟨5826258559362004651580951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884172372908003101053967 5826258559362004651580951)
        ·
          refine ⟨8739387839043006977371427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826258559362004651580951 8739387839043006977371427)
          ·
            refine ⟨13109081758564510466057141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739387839043006977371427 13109081758564510466057141)
            ·
              refine ⟨1228976414865422856192857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13109081758564510466057141 1228976414865422856192857)
              ·
                refine ⟨921732311149067142144643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228976414865422856192857 921732311149067142144643)
                ·
                  refine ⟨1382598466723600713216965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921732311149067142144643 1382598466723600713216965)
                  ·
                    refine ⟨259237212510675133728181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382598466723600713216965 259237212510675133728181)
                    ·
                      rfl

theorem cell23_1514588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1514588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514588 prefixEnd_1514588 := by exact prefixLift 1514588
  have htrace : WordTrace (prefixWord ++ tailWord_1514588) baseStart_1514588 baseEnd_1514588 := by
    simpa [prefixWord, tailWord_1514588, baseEnd_1514588] using wordTrace_append hprefix tailTrace_1514588
  have hstable : (prefixWord ++ tailWord_1514588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514588).length < 2 ^ (prefixWord ++ tailWord_1514588).sum := by decide
  have hdescent : baseEnd_1514588 < baseStart_1514588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514597 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1514597 : Nat := 118140960795 + 1514597 * 2 ^ 59
def prefixEnd_1514597 : Nat := 4983230072969 + 3 ^ 40 * 1514597 * 2
def baseEnd_1514597 : Nat := 259238752952638621990667

theorem tailTrace_1514597 : CollatzResearch.WordTrace tailWord_1514597 prefixEnd_1514597 259238752952638621990667 := by
  unfold tailWord_1514597
  simp only [CollatzResearch.WordTrace]
  refine ⟨55241890893881216418734045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36827927262587477612489363 55241890893881216418734045)
  ·
    refine ⟨20715709085205456157025267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55241890893881216418734045 20715709085205456157025267)
    ·
      refine ⟨31073563627808184235537901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715709085205456157025267 31073563627808184235537901)
      ·
        refine ⟨11652586360428069088326713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31073563627808184235537901 11652586360428069088326713)
        ·
          refine ⟨8739439770321051816245035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11652586360428069088326713 8739439770321051816245035)
          ·
            refine ⟨13109159655481577724367553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739439770321051816245035 13109159655481577724367553)
            ·
              refine ⟨9831869741611183293275665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13109159655481577724367553 9831869741611183293275665)
              ·
                refine ⟨7373902306208387469956749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9831869741611183293275665 7373902306208387469956749)
                ·
                  refine ⟨2765213364828145301233781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7373902306208387469956749 2765213364828145301233781)
                  ·
                    refine ⟨259238752952638621990667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2765213364828145301233781 259238752952638621990667)
                    ·
                      rfl

theorem cell23_1514597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1514597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514597 prefixEnd_1514597 := by exact prefixLift 1514597
  have htrace : WordTrace (prefixWord ++ tailWord_1514597) baseStart_1514597 baseEnd_1514597 := by
    simpa [prefixWord, tailWord_1514597, baseEnd_1514597] using wordTrace_append hprefix tailTrace_1514597
  have hstable : (prefixWord ++ tailWord_1514597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514597).length < 2 ^ (prefixWord ++ tailWord_1514597).sum := by decide
  have hdescent : baseEnd_1514597 < baseStart_1514597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514604 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_1514604 : Nat := 118140960795 + 1514604 * 2 ^ 59
def prefixEnd_1514604 : Nat := 4983230072969 + 3 ^ 40 * 1514604 * 2
def baseEnd_1514604 : Nat := 777719853222497338584469

theorem tailTrace_1514604 : CollatzResearch.WordTrace tailWord_1514604 prefixEnd_1514604 777719853222497338584469 := by
  unfold tailWord_1514604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27621073102427928307119433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36828097469903904409492577 27621073102427928307119433)
  ·
    refine ⟨20715804826820946230339575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27621073102427928307119433 20715804826820946230339575)
    ·
      refine ⟨31073707240231419345509363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20715804826820946230339575 31073707240231419345509363)
      ·
        refine ⟨46610560860347129018264045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31073707240231419345509363 46610560860347129018264045)
        ·
          refine ⟨17478960322630173381849017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46610560860347129018264045 17478960322630173381849017)
          ·
            refine ⟨13109220241972630036386763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17478960322630173381849017 13109220241972630036386763)
            ·
              refine ⟨19663830362958945054580145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13109220241972630036386763 19663830362958945054580145)
              ·
                refine ⟨14747872772219208790935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19663830362958945054580145 14747872772219208790935109)
                ·
                  refine ⟨2765226144791101648300333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14747872772219208790935109 2765226144791101648300333)
                  ·
                    refine ⟨1036959804296663118112625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765226144791101648300333 1036959804296663118112625)
                    ·
                      refine ⟨777719853222497338584469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036959804296663118112625 777719853222497338584469)
                      ·
                        rfl

theorem cell23_1514604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_1514604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514604 prefixEnd_1514604 := by exact prefixLift 1514604
  have htrace : WordTrace (prefixWord ++ tailWord_1514604) baseStart_1514604 baseEnd_1514604 := by
    simpa [prefixWord, tailWord_1514604, baseEnd_1514604] using wordTrace_append hprefix tailTrace_1514604
  have hstable : (prefixWord ++ tailWord_1514604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514604).length < 2 ^ (prefixWord ++ tailWord_1514604).sum := by decide
  have hdescent : baseEnd_1514604 < baseStart_1514604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514614 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1514614 : Nat := 118140960795 + 1514614 * 2 ^ 59
def prefixEnd_1514614 : Nat := 4983230072969 + 3 ^ 40 * 1514614 * 2
def baseEnd_1514614 : Nat := 259241662676347433153141

theorem tailTrace_1514614 : CollatzResearch.WordTrace tailWord_1514614 prefixEnd_1514614 259241662676347433153141 := by
  unfold tailWord_1514614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3452656933426226770131431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36828340623213085548068597 3452656933426226770131431)
  ·
    refine ⟨5178985400139340155197147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3452656933426226770131431 5178985400139340155197147)
    ·
      refine ⟨7768478100209010232795721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5178985400139340155197147 7768478100209010232795721)
      ·
        refine ⟨5826358575156757674596791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768478100209010232795721 5826358575156757674596791)
        ·
          refine ⟨8739537862735136511895187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826358575156757674596791 8739537862735136511895187)
          ·
            refine ⟨13109306794102704767842781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739537862735136511895187 13109306794102704767842781)
            ·
              refine ⟨4915990047788514287941043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13109306794102704767842781 4915990047788514287941043)
              ·
                refine ⟨7373985071682771431911565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4915990047788514287941043 7373985071682771431911565)
                ·
                  refine ⟨2765244401881039286966837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7373985071682771431911565 2765244401881039286966837)
                  ·
                    refine ⟨259241662676347433153141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2765244401881039286966837 259241662676347433153141)
                    ·
                      rfl

theorem cell23_1514614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1514614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514614 prefixEnd_1514614 := by exact prefixLift 1514614
  have htrace : WordTrace (prefixWord ++ tailWord_1514614) baseStart_1514614 baseEnd_1514614 := by
    simpa [prefixWord, tailWord_1514614, baseEnd_1514614] using wordTrace_append hprefix tailTrace_1514614
  have hstable : (prefixWord ++ tailWord_1514614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514614).length < 2 ^ (prefixWord ++ tailWord_1514614).sum := by decide
  have hdescent : baseEnd_1514614 < baseStart_1514614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514621 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_1514621 : Nat := 118140960795 + 1514621 * 2 ^ 59
def prefixEnd_1514621 : Nat := 4983230072969 + 3 ^ 40 * 1514621 * 2
def baseEnd_1514621 : Nat := 777728582393623772071891

theorem tailTrace_1514621 : CollatzResearch.WordTrace tailWord_1514621 prefixEnd_1514621 777728582393623772071891 := by
  unfold tailWord_1514621
  simp only [CollatzResearch.WordTrace]
  refine ⟨55242766245794268517607717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36828510830529512345071811 55242766245794268517607717)
  ·
    refine ⟨10358018671086425347051447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55242766245794268517607717 10358018671086425347051447)
    ·
      refine ⟨15537028006629638020577171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10358018671086425347051447 15537028006629638020577171)
      ·
        refine ⟨23305542009944457030865757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537028006629638020577171 23305542009944457030865757)
        ·
          refine ⟨8739578253729171386574659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23305542009944457030865757 8739578253729171386574659)
          ·
            refine ⟨13109367380593757079861989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8739578253729171386574659 13109367380593757079861989)
            ·
              refine ⟨2458006383861329452474123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13109367380593757079861989 2458006383861329452474123)
              ·
                refine ⟨3687009575791994178711185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458006383861329452474123 3687009575791994178711185)
                ·
                  refine ⟨2765257181843995634033389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687009575791994178711185 2765257181843995634033389)
                  ·
                    refine ⟨1036971443191498362762521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765257181843995634033389 1036971443191498362762521)
                    ·
                      refine ⟨777728582393623772071891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1036971443191498362762521 777728582393623772071891)
                      ·
                        rfl

theorem cell23_1514621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_1514621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514621 prefixEnd_1514621 := by exact prefixLift 1514621
  have htrace : WordTrace (prefixWord ++ tailWord_1514621) baseStart_1514621 baseEnd_1514621 := by
    simpa [prefixWord, tailWord_1514621, baseEnd_1514621] using wordTrace_append hprefix tailTrace_1514621
  have hstable : (prefixWord ++ tailWord_1514621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514621).length < 2 ^ (prefixWord ++ tailWord_1514621).sum := by decide
  have hdescent : baseEnd_1514621 < baseStart_1514621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514627 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 1, 6]
def baseStart_1514627 : Nat := 118140960795 + 1514627 * 2 ^ 59
def prefixEnd_1514627 : Nat := 4983230072969 + 3 ^ 40 * 1514627 * 2
def baseEnd_1514627 : Nat := 259243887759183582865621

theorem tailTrace_1514627 : CollatzResearch.WordTrace tailWord_1514627 prefixEnd_1514627 259243887759183582865621 := by
  unfold tailWord_1514627
  simp only [CollatzResearch.WordTrace]
  refine ⟨55242985083772531542326135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36828656722515021028217423 55242985083772531542326135)
  ·
    refine ⟨82864477625658797313489203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55242985083772531542326135 82864477625658797313489203)
    ·
      refine ⟨124296716438488195970233805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82864477625658797313489203 124296716438488195970233805)
      ·
        refine ⟨46611268664433073488837677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124296716438488195970233805 46611268664433073488837677)
        ·
          refine ⟨17479225749162402558314129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46611268664433073488837677 17479225749162402558314129)
          ·
            refine ⟨13109419311871801918735597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17479225749162402558314129 13109419311871801918735597)
            ·
              refine ⟨4916032241951925719525849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13109419311871801918735597 4916032241951925719525849)
              ·
                refine ⟨3687024181463944289644387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4916032241951925719525849 3687024181463944289644387)
                ·
                  refine ⟨5530536272195916434466581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687024181463944289644387 5530536272195916434466581)
                  ·
                    refine ⟨259243887759183582865621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5530536272195916434466581 259243887759183582865621)
                    ·
                      rfl

theorem cell23_1514627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 6].length) (baseStart_1514627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514627 prefixEnd_1514627 := by exact prefixLift 1514627
  have htrace : WordTrace (prefixWord ++ tailWord_1514627) baseStart_1514627 baseEnd_1514627 := by
    simpa [prefixWord, tailWord_1514627, baseEnd_1514627] using wordTrace_append hprefix tailTrace_1514627
  have hstable : (prefixWord ++ tailWord_1514627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514627).length < 2 ^ (prefixWord ++ tailWord_1514627).sum := by decide
  have hdescent : baseEnd_1514627 < baseStart_1514627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514674 : List Nat := [3, 2, 1, 1, 1, 5, 3, 7]
def baseStart_1514674 : Nat := 118140960795 + 1514674 * 2 ^ 59
def prefixEnd_1514674 : Nat := 4983230072969 + 3 ^ 40 * 1514674 * 2
def baseEnd_1514674 : Nat := 28805770254381928322561

theorem tailTrace_1514674 : CollatzResearch.WordTrace tailWord_1514674 prefixEnd_1514674 28805770254381928322561 := by
  unfold tailWord_1514674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811174828650564642321769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36829799543068172379524717 13811174828650564642321769)
  ·
    refine ⟨10358381121487923481741327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13811174828650564642321769 10358381121487923481741327)
    ·
      refine ⟨15537571682231885222611991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10358381121487923481741327 15537571682231885222611991)
      ·
        refine ⟨23306357523347827833917987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537571682231885222611991 23306357523347827833917987)
        ·
          refine ⟨34959536285021741750876981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23306357523347827833917987 34959536285021741750876981)
          ·
            refine ⟨3277456526720788289144717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34959536285021741750876981 3277456526720788289144717)
            ·
              refine ⟨1229046197520295608429269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3277456526720788289144717 1229046197520295608429269)
              ·
                refine ⟨28805770254381928322561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1229046197520295608429269 28805770254381928322561)
                ·
                  rfl

theorem cell23_1514674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_1514674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514674 prefixEnd_1514674 := by exact prefixLift 1514674
  have htrace : WordTrace (prefixWord ++ tailWord_1514674) baseStart_1514674 baseEnd_1514674 := by
    simpa [prefixWord, tailWord_1514674, baseEnd_1514674] using wordTrace_append hprefix tailTrace_1514674
  have hstable : (prefixWord ++ tailWord_1514674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514674).length < 2 ^ (prefixWord ++ tailWord_1514674).sum := by decide
  have hdescent : baseEnd_1514674 < baseStart_1514674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514728 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1514728 : Nat := 118140960795 + 1514728 * 2 ^ 59
def prefixEnd_1514728 : Nat := 4983230072969 + 3 ^ 40 * 1514728 * 2
def baseEnd_1514728 : Nat := 777783524823654853433899

theorem tailTrace_1514728 : CollatzResearch.WordTrace tailWord_1514728 prefixEnd_1514728 777783524823654853433899 := by
  unfold tailWord_1514728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623334428203312895876419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36831112570937750527835225 27623334428203312895876419)
  ·
    refine ⟨41435001642304969343814629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623334428203312895876419 41435001642304969343814629)
    ·
      refine ⟨7769062807932181751965243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41435001642304969343814629 7769062807932181751965243)
      ·
        refine ⟨11653594211898272627947865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769062807932181751965243 11653594211898272627947865)
        ·
          refine ⟨8740195658923704470960899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11653594211898272627947865 8740195658923704470960899)
          ·
            refine ⟨13110293488385556706441349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8740195658923704470960899 13110293488385556706441349)
            ·
              refine ⟨2458180029072291882457753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13110293488385556706441349 2458180029072291882457753)
              ·
                refine ⟨1843635021804218911843315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458180029072291882457753 1843635021804218911843315)
                ·
                  refine ⟨2765452532706328367764973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843635021804218911843315 2765452532706328367764973)
                  ·
                    refine ⟨1037044699764873137911865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765452532706328367764973 1037044699764873137911865)
                    ·
                      refine ⟨777783524823654853433899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037044699764873137911865 777783524823654853433899)
                      ·
                        rfl

theorem cell23_1514728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1514728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514728 prefixEnd_1514728 := by exact prefixLift 1514728
  have htrace : WordTrace (prefixWord ++ tailWord_1514728) baseStart_1514728 baseEnd_1514728 := by
    simpa [prefixWord, tailWord_1514728, baseEnd_1514728] using wordTrace_append hprefix tailTrace_1514728
  have hstable : (prefixWord ++ tailWord_1514728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514728).length < 2 ^ (prefixWord ++ tailWord_1514728).sum := by decide
  have hdescent : baseEnd_1514728 < baseStart_1514728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514757 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1514757 : Nat := 118140960795 + 1514757 * 2 ^ 59
def prefixEnd_1514757 : Nat := 4983230072969 + 3 ^ 40 * 1514757 * 2
def baseEnd_1514757 : Nat := 777798415762635239971265

theorem tailTrace_1514757 : CollatzResearch.WordTrace tailWord_1514757 prefixEnd_1514757 777798415762635239971265 := by
  unfold tailWord_1514757
  simp only [CollatzResearch.WordTrace]
  refine ⟨55247726573301563744558525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36831817715534375829705683 55247726573301563744558525)
  ·
    refine ⟨20717897464988086404209447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55247726573301563744558525 20717897464988086404209447)
    ·
      refine ⟨31076846197482129606314171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717897464988086404209447 31076846197482129606314171)
      ·
        refine ⟨46615269296223194409471257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31076846197482129606314171 46615269296223194409471257)
        ·
          refine ⟨34961451972167395807103443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46615269296223194409471257 34961451972167395807103443)
          ·
            refine ⟨52442177958251093710655165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34961451972167395807103443 52442177958251093710655165)
            ·
              refine ⟨19665816734344160141495687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52442177958251093710655165 19665816734344160141495687)
              ·
                refine ⟨29498725101516240212243531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19665816734344160141495687 29498725101516240212243531)
                ·
                  refine ⟨44248087652274360318365297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29498725101516240212243531 44248087652274360318365297)
                  ·
                    refine ⟨33186065739205770238773973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44248087652274360318365297 33186065739205770238773973)
                    ·
                      refine ⟨777798415762635239971265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33186065739205770238773973 777798415762635239971265)
                      ·
                        rfl

theorem cell23_1514757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1514757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514757 prefixEnd_1514757 := by exact prefixLift 1514757
  have htrace : WordTrace (prefixWord ++ tailWord_1514757) baseStart_1514757 baseEnd_1514757 := by
    simpa [prefixWord, tailWord_1514757, baseEnd_1514757] using wordTrace_append hprefix tailTrace_1514757
  have hstable : (prefixWord ++ tailWord_1514757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514757).length < 2 ^ (prefixWord ++ tailWord_1514757).sum := by decide
  have hdescent : baseEnd_1514757 < baseStart_1514757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514764 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 7]
def baseStart_1514764 : Nat := 118140960795 + 1514764 * 2 ^ 59
def prefixEnd_1514764 : Nat := 4983230072969 + 3 ^ 40 * 1514764 * 2
def baseEnd_1514764 : Nat := 86422445569690745842637

theorem tailTrace_1514764 : CollatzResearch.WordTrace tailWord_1514764 prefixEnd_1514764 86422445569690745842637 := by
  unfold tailWord_1514764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623990942138101970031673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36831987922850802626708897 27623990942138101970031673)
  ·
    refine ⟨20717993206603576477523755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27623990942138101970031673 20717993206603576477523755)
    ·
      refine ⟨31076989809905364716285633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20717993206603576477523755 31076989809905364716285633)
      ·
        refine ⟨23307742357429023537214225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31076989809905364716285633 23307742357429023537214225)
        ·
          refine ⟨17480806768071767652910669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23307742357429023537214225 17480806768071767652910669)
          ·
            refine ⟨6555302538026912869841501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17480806768071767652910669 6555302538026912869841501)
            ·
              refine ⟨2458238451760092326190563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6555302538026912869841501 2458238451760092326190563)
              ·
                refine ⟨3687357677640138489285845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458238451760092326190563 3687357677640138489285845)
                ·
                  refine ⟨86422445569690745842637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3687357677640138489285845 86422445569690745842637)
                  ·
                    rfl

theorem cell23_1514764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_1514764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514764 prefixEnd_1514764 := by exact prefixLift 1514764
  have htrace : WordTrace (prefixWord ++ tailWord_1514764) baseStart_1514764 baseEnd_1514764 := by
    simpa [prefixWord, tailWord_1514764, baseEnd_1514764] using wordTrace_append hprefix tailTrace_1514764
  have hstable : (prefixWord ++ tailWord_1514764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514764).length < 2 ^ (prefixWord ++ tailWord_1514764).sum := by decide
  have hdescent : baseEnd_1514764 < baseStart_1514764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514845 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1514845 : Nat := 118140960795 + 1514845 * 2 ^ 59
def prefixEnd_1514845 : Nat := 4983230072969 + 3 ^ 40 * 1514845 * 2
def baseEnd_1514845 : Nat := 259281200686743631890287

theorem tailTrace_1514845 : CollatzResearch.WordTrace tailWord_1514845 prefixEnd_1514845 259281200686743631890287 := by
  unfold tailWord_1514845
  simp only [CollatzResearch.WordTrace]
  refine ⟨55250936196982754773761989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36833957464655169849174659 55250936196982754773761989)
  ·
    refine ⟨10359550536934266520080373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55250936196982754773761989 10359550536934266520080373)
    ·
      refine ⟨971207862837587486257535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10359550536934266520080373 971207862837587486257535)
      ·
        refine ⟨1456811794256381229386303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971207862837587486257535 1456811794256381229386303)
        ·
          refine ⟨2185217691384571844079455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456811794256381229386303 2185217691384571844079455)
          ·
            refine ⟨3277826537076857766119183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185217691384571844079455 3277826537076857766119183)
            ·
              refine ⟨4916739805615286649178775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277826537076857766119183 4916739805615286649178775)
              ·
                refine ⟨7375109708422929973768163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4916739805615286649178775 7375109708422929973768163)
                ·
                  refine ⟨11062664562634394960652245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375109708422929973768163 11062664562634394960652245)
                  ·
                    refine ⟨259281200686743631890287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11062664562634394960652245 259281200686743631890287)
                    ·
                      rfl

theorem cell23_1514845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1514845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514845 prefixEnd_1514845 := by exact prefixLift 1514845
  have htrace : WordTrace (prefixWord ++ tailWord_1514845) baseStart_1514845 baseEnd_1514845 := by
    simpa [prefixWord, tailWord_1514845, baseEnd_1514845] using wordTrace_append hprefix tailTrace_1514845
  have hstable : (prefixWord ++ tailWord_1514845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514845).length < 2 ^ (prefixWord ++ tailWord_1514845).sum := by decide
  have hdescent : baseEnd_1514845 < baseStart_1514845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514848 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1514848 : Nat := 118140960795 + 1514848 * 2 ^ 59
def prefixEnd_1514848 : Nat := 4983230072969 + 3 ^ 40 * 1514848 * 2
def baseEnd_1514848 : Nat := 777845142502194383933347

theorem tailTrace_1514848 : CollatzResearch.WordTrace tailWord_1514848 prefixEnd_1514848 777845142502194383933347 := by
  unfold tailWord_1514848
  simp only [CollatzResearch.WordTrace]
  refine ⟨27625522807985943143060599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36834030410647924190747465 27625522807985943143060599)
  ·
    refine ⟨41438284211978914714590899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27625522807985943143060599 41438284211978914714590899)
    ·
      refine ⟨62157426317968372071886349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41438284211978914714590899 62157426317968372071886349)
      ·
        refine ⟨23309034869238139526957381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62157426317968372071886349 23309034869238139526957381)
        ·
          refine ⟨4370444037982151161304509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23309034869238139526957381 4370444037982151161304509)
          ·
            refine ⟨1638916514243306685489191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4370444037982151161304509 1638916514243306685489191)
            ·
              refine ⟨2458374771364960028233787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638916514243306685489191 2458374771364960028233787)
              ·
                refine ⟨3687562157047440042350681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458374771364960028233787 3687562157047440042350681)
                ·
                  refine ⟨2765671617785580031763011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687562157047440042350681 2765671617785580031763011)
                  ·
                    refine ⟨4148507426678370047644517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2765671617785580031763011 4148507426678370047644517)
                    ·
                      refine ⟨777845142502194383933347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4148507426678370047644517 777845142502194383933347)
                      ·
                        rfl

theorem cell23_1514848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1514848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514848 prefixEnd_1514848 := by exact prefixLift 1514848
  have htrace : WordTrace (prefixWord ++ tailWord_1514848) baseStart_1514848 baseEnd_1514848 := by
    simpa [prefixWord, tailWord_1514848, baseEnd_1514848] using wordTrace_append hprefix tailTrace_1514848
  have hstable : (prefixWord ++ tailWord_1514848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514848).length < 2 ^ (prefixWord ++ tailWord_1514848).sum := by decide
  have hdescent : baseEnd_1514848 < baseStart_1514848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514851 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1514851 : Nat := 118140960795 + 1514851 * 2 ^ 59
def prefixEnd_1514851 : Nat := 4983230072969 + 3 ^ 40 * 1514851 * 2
def baseEnd_1514851 : Nat := 777846682944157872195833

theorem tailTrace_1514851 : CollatzResearch.WordTrace tailWord_1514851 prefixEnd_1514851 777846682944157872195833 := by
  unfold tailWord_1514851
  simp only [CollatzResearch.WordTrace]
  refine ⟨55251155034961017798480407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36834103356640678532320271 55251155034961017798480407)
  ·
    refine ⟨82876732552441526697720611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55251155034961017798480407 82876732552441526697720611)
    ·
      refine ⟨124315098828662290046580917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82876732552441526697720611 124315098828662290046580917)
      ·
        refine ⟨11654540515187089691866961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124315098828662290046580917 11654540515187089691866961)
        ·
          refine ⟨8740905386390317268900221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11654540515187089691866961 8740905386390317268900221)
          ·
            refine ⟨3277839519896368975837583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8740905386390317268900221 3277839519896368975837583)
            ·
              refine ⟨4916759279844553463756375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277839519896368975837583 4916759279844553463756375)
              ·
                refine ⟨7375138919766830195634563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4916759279844553463756375 7375138919766830195634563)
                ·
                  refine ⟨11062708379650245293451845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7375138919766830195634563 11062708379650245293451845)
                  ·
                    refine ⟨2074257821184420992522221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11062708379650245293451845 2074257821184420992522221)
                    ·
                      refine ⟨777846682944157872195833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074257821184420992522221 777846682944157872195833)
                      ·
                        rfl

theorem cell23_1514851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1514851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514851 prefixEnd_1514851 := by exact prefixLift 1514851
  have htrace : WordTrace (prefixWord ++ tailWord_1514851) baseStart_1514851 baseEnd_1514851 := by
    simpa [prefixWord, tailWord_1514851, baseEnd_1514851] using wordTrace_append hprefix tailTrace_1514851
  have hstable : (prefixWord ++ tailWord_1514851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514851).length < 2 ^ (prefixWord ++ tailWord_1514851).sum := by decide
  have hdescent : baseEnd_1514851 < baseStart_1514851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514888 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 6]
def baseStart_1514888 : Nat := 118140960795 + 1514888 * 2 ^ 59
def prefixEnd_1514888 : Nat := 4983230072969 + 3 ^ 40 * 1514888 * 2
def baseEnd_1514888 : Nat := 86429520192041580825907

theorem tailTrace_1514888 : CollatzResearch.WordTrace tailWord_1514888 prefixEnd_1514888 86429520192041580825907 := by
  unfold tailWord_1514888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27626252267913486558788659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36835003023884648745051545 27626252267913486558788659)
  ·
    refine ⟨41439378401870229838182989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27626252267913486558788659 41439378401870229838182989)
    ·
      refine ⟨15539766900701336189318621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41439378401870229838182989 15539766900701336189318621)
      ·
        refine ⟨5827412587763001070994483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15539766900701336189318621 5827412587763001070994483)
        ·
          refine ⟨8741118881644501606491725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5827412587763001070994483 8741118881644501606491725)
          ·
            refine ⟨3277919580616688102434397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8741118881644501606491725 3277919580616688102434397)
            ·
              refine ⟨1229219842731258038412899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3277919580616688102434397 1229219842731258038412899)
              ·
                refine ⟨1843829764096887057619349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229219842731258038412899 1843829764096887057619349)
                ·
                  refine ⟨86429520192041580825907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1843829764096887057619349 86429520192041580825907)
                  ·
                    rfl

theorem cell23_1514888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 6].length) (baseStart_1514888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514888 prefixEnd_1514888 := by exact prefixLift 1514888
  have htrace : WordTrace (prefixWord ++ tailWord_1514888) baseStart_1514888 baseEnd_1514888 := by
    simpa [prefixWord, tailWord_1514888, baseEnd_1514888] using wordTrace_append hprefix tailTrace_1514888
  have hstable : (prefixWord ++ tailWord_1514888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514888).length < 2 ^ (prefixWord ++ tailWord_1514888).sum := by decide
  have hdescent : baseEnd_1514888 < baseStart_1514888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514891 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 5, 2]
def baseStart_1514891 : Nat := 118140960795 + 1514891 * 2 ^ 59
def prefixEnd_1514891 : Nat := 4983230072969 + 3 ^ 40 * 1514891 * 2
def baseEnd_1514891 : Nat := 777867222170337715695649

theorem tailTrace_1514891 : CollatzResearch.WordTrace tailWord_1514891 prefixEnd_1514891 777867222170337715695649 := by
  unfold tailWord_1514891
  simp only [CollatzResearch.WordTrace]
  refine ⟨55252613954816104629936527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36835075969877403086624351 55252613954816104629936527)
  ·
    refine ⟨82878920932224156944904791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55252613954816104629936527 82878920932224156944904791)
    ·
      refine ⟨124318381398336235417357187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82878920932224156944904791 124318381398336235417357187)
      ·
        refine ⟨186477572097504353126035781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124318381398336235417357187 186477572097504353126035781)
        ·
          refine ⟨34964544768282066211131709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186477572097504353126035781 34964544768282066211131709)
          ·
            refine ⟨13111704288105774829174391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34964544768282066211131709 13111704288105774829174391)
            ·
              refine ⟨19667556432158662243761587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13111704288105774829174391 19667556432158662243761587)
              ·
                refine ⟨29501334648237993365642381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19667556432158662243761587 29501334648237993365642381)
                ·
                  refine ⟨11063000493089247512115893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29501334648237993365642381 11063000493089247512115893)
                  ·
                    refine ⟨1037156296227116954260865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11063000493089247512115893 1037156296227116954260865)
                    ·
                      refine ⟨777867222170337715695649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037156296227116954260865 777867222170337715695649)
                      ·
                        rfl

theorem cell23_1514891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 5, 2].length) (baseStart_1514891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514891 prefixEnd_1514891 := by exact prefixLift 1514891
  have htrace : WordTrace (prefixWord ++ tailWord_1514891) baseStart_1514891 baseEnd_1514891 := by
    simpa [prefixWord, tailWord_1514891, baseEnd_1514891] using wordTrace_append hprefix tailTrace_1514891
  have hstable : (prefixWord ++ tailWord_1514891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514891).length < 2 ^ (prefixWord ++ tailWord_1514891).sum := by decide
  have hdescent : baseEnd_1514891 < baseStart_1514891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514901 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1514901 : Nat := 118140960795 + 1514901 * 2 ^ 59
def prefixEnd_1514901 : Nat := 4983230072969 + 3 ^ 40 * 1514901 * 2
def baseEnd_1514901 : Nat := 259290785658960892190201

theorem tailTrace_1514901 : CollatzResearch.WordTrace tailWord_1514901 prefixEnd_1514901 259290785658960892190201 := by
  unfold tailWord_1514901
  simp only [CollatzResearch.WordTrace]
  refine ⟨55252978684779876337800557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36835319123186584225200371 55252978684779876337800557)
  ·
    refine ⟨20719867006792453626675209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55252978684779876337800557 20719867006792453626675209)
    ·
      refine ⟨15539900255094340220006407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20719867006792453626675209 15539900255094340220006407)
      ·
        refine ⟨23309850382641510330009611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15539900255094340220006407 23309850382641510330009611)
        ·
          refine ⟨34964775573962265495014417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23309850382641510330009611 34964775573962265495014417)
          ·
            refine ⟨26223581680471699121260813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34964775573962265495014417 26223581680471699121260813)
            ·
              refine ⟨9833843130176887170472805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26223581680471699121260813 9833843130176887170472805)
              ·
                refine ⟨1843845586908166344463651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9833843130176887170472805 1843845586908166344463651)
                ·
                  refine ⟨2765768380362249516695477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843845586908166344463651 2765768380362249516695477)
                  ·
                    refine ⟨259290785658960892190201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2765768380362249516695477 259290785658960892190201)
                    ·
                      rfl

theorem cell23_1514901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1514901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514901 prefixEnd_1514901 := by exact prefixLift 1514901
  have htrace : WordTrace (prefixWord ++ tailWord_1514901) baseStart_1514901 baseEnd_1514901 := by
    simpa [prefixWord, tailWord_1514901, baseEnd_1514901] using wordTrace_append hprefix tailTrace_1514901
  have hstable : (prefixWord ++ tailWord_1514901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514901).length < 2 ^ (prefixWord ++ tailWord_1514901).sum := by decide
  have hdescent : baseEnd_1514901 < baseStart_1514901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514925 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1514925 : Nat := 118140960795 + 1514925 * 2 ^ 59
def prefixEnd_1514925 : Nat := 4983230072969 + 3 ^ 40 * 1514925 * 2
def baseEnd_1514925 : Nat := 777884680512590582670493

theorem tailTrace_1514925 : CollatzResearch.WordTrace tailWord_1514925 prefixEnd_1514925 777884680512590582670493 := by
  unfold tailWord_1514925
  simp only [CollatzResearch.WordTrace]
  refine ⟨55253854036692928436674229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36835902691128618957782819 55253854036692928436674229)
  ·
    refine ⟨5180048815939962040938209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55253854036692928436674229 5180048815939962040938209)
    ·
      refine ⟨3885036611954971530703657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5180048815939962040938209 3885036611954971530703657)
      ·
        refine ⟨2913777458966228648027743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3885036611954971530703657 2913777458966228648027743)
        ·
          refine ⟨4370666188449342972041615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913777458966228648027743 4370666188449342972041615)
          ·
            refine ⟨6555999282674014458062423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370666188449342972041615 6555999282674014458062423)
            ·
              refine ⟨9833998924011021687093635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6555999282674014458062423 9833998924011021687093635)
              ·
                refine ⟨14750998386016532530640453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9833998924011021687093635 14750998386016532530640453)
                ·
                  refine ⟨2765812197378099849495085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14750998386016532530640453 2765812197378099849495085)
                  ·
                    refine ⟨1037179574016787443560657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2765812197378099849495085 1037179574016787443560657)
                    ·
                      refine ⟨777884680512590582670493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1037179574016787443560657 777884680512590582670493)
                      ·
                        rfl

theorem cell23_1514925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1514925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514925 prefixEnd_1514925 := by exact prefixLift 1514925
  have htrace : WordTrace (prefixWord ++ tailWord_1514925) baseStart_1514925 baseEnd_1514925 := by
    simpa [prefixWord, tailWord_1514925, baseEnd_1514925] using wordTrace_append hprefix tailTrace_1514925
  have hstable : (prefixWord ++ tailWord_1514925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514925).length < 2 ^ (prefixWord ++ tailWord_1514925).sum := by decide
  have hdescent : baseEnd_1514925 < baseStart_1514925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514941 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1514941 : Nat := 118140960795 + 1514941 * 2 ^ 59
def prefixEnd_1514941 : Nat := 4983230072969 + 3 ^ 40 * 1514941 * 2
def baseEnd_1514941 : Nat := 777892896203062520070419

theorem tailTrace_1514941 : CollatzResearch.WordTrace tailWord_1514941 prefixEnd_1514941 777892896203062520070419 := by
  unfold tailWord_1514941
  simp only [CollatzResearch.WordTrace]
  refine ⟨55254437604634963169256677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36836291736423308779504451 55254437604634963169256677)
  ·
    refine ⟨10360207050869055594235627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55254437604634963169256677 10360207050869055594235627)
    ·
      refine ⟨15540310576303583391353441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10360207050869055594235627 15540310576303583391353441)
      ·
        refine ⟨11655232932227687543515081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15540310576303583391353441 11655232932227687543515081)
        ·
          refine ⟨8741424699170765657636311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11655232932227687543515081 8741424699170765657636311)
          ·
            refine ⟨13112137048756148486454467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741424699170765657636311 13112137048756148486454467)
            ·
              refine ⟨19668205573134222729681701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13112137048756148486454467 19668205573134222729681701)
              ·
                refine ⟨3687788544962666761815319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19668205573134222729681701 3687788544962666761815319)
                ·
                  refine ⟨5531682817444000142722979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687788544962666761815319 5531682817444000142722979)
                  ·
                    refine ⟨8297524226166000214084469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5531682817444000142722979 8297524226166000214084469)
                    ·
                      refine ⟨777892896203062520070419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8297524226166000214084469 777892896203062520070419)
                      ·
                        rfl

theorem cell23_1514941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1514941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514941 prefixEnd_1514941 := by exact prefixLift 1514941
  have htrace : WordTrace (prefixWord ++ tailWord_1514941) baseStart_1514941 baseEnd_1514941 := by
    simpa [prefixWord, tailWord_1514941, baseEnd_1514941] using wordTrace_append hprefix tailTrace_1514941
  have hstable : (prefixWord ++ tailWord_1514941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514941).length < 2 ^ (prefixWord ++ tailWord_1514941).sum := by decide
  have hdescent : baseEnd_1514941 < baseStart_1514941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514944 : List Nat := [2, 1, 1, 2, 3, 1, 3, 10]
def baseStart_1514944 : Nat := 118140960795 + 1514944 * 2 ^ 59
def prefixEnd_1514944 : Nat := 4983230072969 + 3 ^ 40 * 1514944 * 2
def baseEnd_1514944 : Nat := 28810905060926889197515

theorem tailTrace_1514944 : CollatzResearch.WordTrace tailWord_1514944 prefixEnd_1514944 28810905060926889197515 := by
  unfold tailWord_1514944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627273511812047340807943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36836364682416063121077257 27627273511812047340807943)
  ·
    refine ⟨41440910267718071011211915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27627273511812047340807943 41440910267718071011211915)
    ·
      refine ⟨62161365401577106516817873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41440910267718071011211915 62161365401577106516817873)
      ·
        refine ⟨46621024051182829887613405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62161365401577106516817873 46621024051182829887613405)
        ·
          refine ⟨17482884019193561207855027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46621024051182829887613405 17482884019193561207855027)
          ·
            refine ⟨26224326028790341811782541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17482884019193561207855027 26224326028790341811782541)
            ·
              refine ⟨9834122260796378179418453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26224326028790341811782541 9834122260796378179418453)
              ·
                refine ⟨28810905060926889197515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9834122260796378179418453 28810905060926889197515)
                ·
                  rfl

theorem cell23_1514944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 10].length) (baseStart_1514944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514944 prefixEnd_1514944 := by exact prefixLift 1514944
  have htrace : WordTrace (prefixWord ++ tailWord_1514944) baseStart_1514944 baseEnd_1514944 := by
    simpa [prefixWord, tailWord_1514944, baseEnd_1514944] using wordTrace_append hprefix tailTrace_1514944
  have hstable : (prefixWord ++ tailWord_1514944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514944).length < 2 ^ (prefixWord ++ tailWord_1514944).sum := by decide
  have hdescent : baseEnd_1514944 < baseStart_1514944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514951 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1514951 : Nat := 118140960795 + 1514951 * 2 ^ 59
def prefixEnd_1514951 : Nat := 4983230072969 + 3 ^ 40 * 1514951 * 2
def baseEnd_1514951 : Nat := 777898031009607480945373

theorem tailTrace_1514951 : CollatzResearch.WordTrace tailWord_1514951 prefixEnd_1514951 777898031009607480945373 := by
  unfold tailWord_1514951
  simp only [CollatzResearch.WordTrace]
  refine ⟨55254802334598734877120707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36836534889732489918080471 55254802334598734877120707)
  ·
    refine ⟨82882203501898102315681061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55254802334598734877120707 82882203501898102315681061)
    ·
      refine ⟨15540413156605894184190199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82882203501898102315681061 15540413156605894184190199)
      ·
        refine ⟨23310619734908841276285299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15540413156605894184190199 23310619734908841276285299)
        ·
          refine ⟨34965929602363261914427949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23310619734908841276285299 34965929602363261914427949)
          ·
            refine ⟨13112223600886223217910481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34965929602363261914427949 13112223600886223217910481)
            ·
              refine ⟨9834167700664667413432861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13112223600886223217910481 9834167700664667413432861)
              ·
                refine ⟨3687812887749250280037323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9834167700664667413432861 3687812887749250280037323)
                ·
                  refine ⟨5531719331623875420055985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687812887749250280037323 5531719331623875420055985)
                  ·
                    refine ⟨4148789498717906565041989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5531719331623875420055985 4148789498717906565041989)
                    ·
                      refine ⟨777898031009607480945373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4148789498717906565041989 777898031009607480945373)
                      ·
                        rfl

theorem cell23_1514951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1514951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514951 prefixEnd_1514951 := by exact prefixLift 1514951
  have htrace : WordTrace (prefixWord ++ tailWord_1514951) baseStart_1514951 baseEnd_1514951 := by
    simpa [prefixWord, tailWord_1514951, baseEnd_1514951] using wordTrace_append hprefix tailTrace_1514951
  have hstable : (prefixWord ++ tailWord_1514951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514951).length < 2 ^ (prefixWord ++ tailWord_1514951).sum := by decide
  have hdescent : baseEnd_1514951 < baseStart_1514951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514975 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 1, 2, 3]
def baseStart_1514975 : Nat := 118140960795 + 1514975 * 2 ^ 59
def prefixEnd_1514975 : Nat := 4983230072969 + 3 ^ 40 * 1514975 * 2
def baseEnd_1514975 : Nat := 777910354545315387045263

theorem tailTrace_1514975 : CollatzResearch.WordTrace tailWord_1514975 prefixEnd_1514975 777910354545315387045263 := by
  unfold tailWord_1514975
  simp only [CollatzResearch.WordTrace]
  refine ⟨55255677686511786975994379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36837118457674524650662919 55255677686511786975994379)
  ·
    refine ⟨82883516529767680463991569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55255677686511786975994379 82883516529767680463991569)
    ·
      refine ⟨62162637397325760347993677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82883516529767680463991569 62162637397325760347993677)
      ·
        refine ⟨23310989023997160130497629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62162637397325760347993677 23310989023997160130497629)
        ·
          refine ⟨8741620883998935048936611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23310989023997160130497629 8741620883998935048936611)
          ·
            refine ⟨13112431325998402573404917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8741620883998935048936611 13112431325998402573404917)
            ·
              refine ⟨1229290436812350241256711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13112431325998402573404917 1229290436812350241256711)
              ·
                refine ⟨1843935655218525361885067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229290436812350241256711 1843935655218525361885067)
                ·
                  refine ⟨2765903482827788042827601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843935655218525361885067 2765903482827788042827601)
                  ·
                    refine ⟨2074427612120841032120701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765903482827788042827601 2074427612120841032120701)
                    ·
                      refine ⟨777910354545315387045263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074427612120841032120701 777910354545315387045263)
                      ·
                        rfl

theorem cell23_1514975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_1514975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1514975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1514975 prefixEnd_1514975 := by exact prefixLift 1514975
  have htrace : WordTrace (prefixWord ++ tailWord_1514975) baseStart_1514975 baseEnd_1514975 := by
    simpa [prefixWord, tailWord_1514975, baseEnd_1514975] using wordTrace_append hprefix tailTrace_1514975
  have hstable : (prefixWord ++ tailWord_1514975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514975).length < 2 ^ (prefixWord ++ tailWord_1514975).sum := by decide
  have hdescent : baseEnd_1514975 < baseStart_1514975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515005 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1515005 : Nat := 118140960795 + 1515005 * 2 ^ 59
def prefixEnd_1515005 : Nat := 4983230072969 + 3 ^ 40 * 1515005 * 2
def baseEnd_1515005 : Nat := 777925758964950269670125

theorem tailTrace_1515005 : CollatzResearch.WordTrace tailWord_1515005 prefixEnd_1515005 777925758964950269670125 := by
  unfold tailWord_1515005
  simp only [CollatzResearch.WordTrace]
  refine ⟨55256771876403102099586469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36837847917602068066390979 55256771876403102099586469)
  ·
    refine ⟨10360644726825581643672463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55256771876403102099586469 10360644726825581643672463)
    ·
      refine ⟨15540967090238372465508695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10360644726825581643672463 15540967090238372465508695)
      ·
        refine ⟨23311450635357558698263043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15540967090238372465508695 23311450635357558698263043)
        ·
          refine ⟨34967175953036338047394565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23311450635357558698263043 34967175953036338047394565)
          ·
            refine ⟨6556345491194313383886481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34967175953036338047394565 6556345491194313383886481)
            ·
              refine ⟨4917259118395735037914861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6556345491194313383886481 4917259118395735037914861)
              ·
                refine ⟨1843972169398400639218073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4917259118395735037914861 1843972169398400639218073)
                ·
                  refine ⟨1382979127048800479413555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1843972169398400639218073 1382979127048800479413555)
                  ·
                    refine ⟨2074468690573200719120333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1382979127048800479413555 2074468690573200719120333)
                    ·
                      refine ⟨777925758964950269670125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2074468690573200719120333 777925758964950269670125)
                      ·
                        rfl

theorem cell23_1515005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1515005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1515005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1515005 prefixEnd_1515005 := by exact prefixLift 1515005
  have htrace : WordTrace (prefixWord ++ tailWord_1515005) baseStart_1515005 baseEnd_1515005 := by
    simpa [prefixWord, tailWord_1515005, baseEnd_1515005] using wordTrace_append hprefix tailTrace_1515005
  have hstable : (prefixWord ++ tailWord_1515005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515005).length < 2 ^ (prefixWord ++ tailWord_1515005).sum := by decide
  have hdescent : baseEnd_1515005 < baseStart_1515005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
