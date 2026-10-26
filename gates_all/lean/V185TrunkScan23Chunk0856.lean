import V185TrunkScan23Chunk0855

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5066105 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_5066105 : Nat := 118140960795 + 5066105 * 2 ^ 59
def prefixEnd_5066105 : Nat := 4983230072969 + 3 ^ 40 * 5066105 * 2
def baseEnd_5066105 : Nat := 2601346911146006574588913

theorem tailTrace_5066105 : CollatzResearch.WordTrace tailWord_5066105 prefixEnd_5066105 2601346911146006574588913 := by
  unfold tailWord_5066105
  simp only [CollatzResearch.WordTrace]
  refine ⟨184776029311374281695279769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123184019540916187796853179 184776029311374281695279769)
  ·
    refine ⟨138582021983530711271459827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184776029311374281695279769 138582021983530711271459827)
    ·
      refine ⟨207873032975296066907189741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138582021983530711271459827 207873032975296066907189741)
      ·
        refine ⟨77952387365736025090196153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207873032975296066907189741 77952387365736025090196153)
        ·
          refine ⟨58464290524302018817647115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77952387365736025090196153 58464290524302018817647115)
          ·
            refine ⟨87696435786453028226470673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58464290524302018817647115 87696435786453028226470673)
            ·
              refine ⟨65772326839839771169853005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87696435786453028226470673 65772326839839771169853005)
              ·
                refine ⟨24664622564939914188694877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65772326839839771169853005 24664622564939914188694877)
                ·
                  refine ⟨9249233461852467820760579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24664622564939914188694877 9249233461852467820760579)
                  ·
                    refine ⟨13873850192778701731140869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9249233461852467820760579 13873850192778701731140869)
                    ·
                      refine ⟨2601346911146006574588913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13873850192778701731140869 2601346911146006574588913)
                      ·
                        rfl

theorem cell23_5066105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_5066105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066105 prefixEnd_5066105 := by exact prefixLift 5066105
  have htrace : WordTrace (prefixWord ++ tailWord_5066105) baseStart_5066105 baseEnd_5066105 := by
    simpa [prefixWord, tailWord_5066105, baseEnd_5066105] using wordTrace_append hprefix tailTrace_5066105
  have hstable : (prefixWord ++ tailWord_5066105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066105).length < 2 ^ (prefixWord ++ tailWord_5066105).sum := by decide
  have hdescent : baseEnd_5066105 < baseStart_5066105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066110 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5066110 : Nat := 118140960795 + 5066110 * 2 ^ 59
def prefixEnd_5066110 : Nat := 4983230072969 + 3 ^ 40 * 5066110 * 2
def baseEnd_5066110 : Nat := 867116492849759685008797

theorem tailTrace_5066110 : CollatzResearch.WordTrace tailWord_5066110 prefixEnd_5066110 867116492849759685008797 := by
  unfold tailWord_5066110
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097026459544520943651473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123184141117570778366141189 23097026459544520943651473)
  ·
    refine ⟨17322769844658390707738605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23097026459544520943651473 17322769844658390707738605)
    ·
      refine ⟨6496038691746896515401977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17322769844658390707738605 6496038691746896515401977)
      ·
        refine ⟨4872029018810172386551483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6496038691746896515401977 4872029018810172386551483)
        ·
          refine ⟨7308043528215258579827225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872029018810172386551483 7308043528215258579827225)
          ·
            refine ⟨5481032646161443934870419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7308043528215258579827225 5481032646161443934870419)
            ·
              refine ⟨8221548969242165902305629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481032646161443934870419 8221548969242165902305629)
              ·
                refine ⟨3083080863465812213364611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8221548969242165902305629 3083080863465812213364611)
                ·
                  refine ⟨4624621295198718320046917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083080863465812213364611 4624621295198718320046917)
                  ·
                    refine ⟨867116492849759685008797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624621295198718320046917 867116492849759685008797)
                    ·
                      rfl

theorem cell23_5066110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5066110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066110 prefixEnd_5066110 := by exact prefixLift 5066110
  have htrace : WordTrace (prefixWord ++ tailWord_5066110) baseStart_5066110 baseEnd_5066110 := by
    simpa [prefixWord, tailWord_5066110, baseEnd_5066110] using wordTrace_append hprefix tailTrace_5066110
  have hstable : (prefixWord ++ tailWord_5066110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066110).length < 2 ^ (prefixWord ++ tailWord_5066110).sum := by decide
  have hdescent : baseEnd_5066110 < baseStart_5066110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066116 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_5066116 : Nat := 118140960795 + 5066116 * 2 ^ 59
def prefixEnd_5066116 : Nat := 4983230072969 + 3 ^ 40 * 5066116 * 2
def baseEnd_5066116 : Nat := 2601352559433206031551363

theorem tailTrace_5066116 : CollatzResearch.WordTrace tailWord_5066116 prefixEnd_5066116 2601352559433206031551363 := by
  unfold tailWord_5066116
  simp only [CollatzResearch.WordTrace]
  refine ⟨92388215257167215286965101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123184287009556287049286801 92388215257167215286965101)
  ·
    refine ⟨34645580721437705732611913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92388215257167215286965101 34645580721437705732611913)
    ·
      refine ⟨25984185541078279299458935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34645580721437705732611913 25984185541078279299458935)
      ·
        refine ⟨38976278311617418949188403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25984185541078279299458935 38976278311617418949188403)
        ·
          refine ⟨58464417467426128423782605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38976278311617418949188403 58464417467426128423782605)
          ·
            refine ⟨21924156550284798158918477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58464417467426128423782605 21924156550284798158918477)
            ·
              refine ⟨8221558706356799309594429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21924156550284798158918477 8221558706356799309594429)
              ·
                refine ⟨3083084514883799741097911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8221558706356799309594429 3083084514883799741097911)
                ·
                  refine ⟨4624626772325699611646867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083084514883799741097911 4624626772325699611646867)
                  ·
                    refine ⟨6936940158488549417470301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624626772325699611646867 6936940158488549417470301)
                    ·
                      refine ⟨2601352559433206031551363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6936940158488549417470301 2601352559433206031551363)
                      ·
                        rfl

theorem cell23_5066116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_5066116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066116 prefixEnd_5066116 := by exact prefixLift 5066116
  have htrace : WordTrace (prefixWord ++ tailWord_5066116) baseStart_5066116 baseEnd_5066116 := by
    simpa [prefixWord, tailWord_5066116, baseEnd_5066116] using wordTrace_append hprefix tailTrace_5066116
  have hstable : (prefixWord ++ tailWord_5066116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066116).length < 2 ^ (prefixWord ++ tailWord_5066116).sum := by decide
  have hdescent : baseEnd_5066116 < baseStart_5066116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066126 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5066126 : Nat := 118140960795 + 5066126 * 2 ^ 59
def prefixEnd_5066126 : Nat := 4983230072969 + 3 ^ 40 * 5066126 * 2
def baseEnd_5066126 : Nat := 2601357694239750992426317

theorem tailTrace_5066126 : CollatzResearch.WordTrace tailWord_5066126 prefixEnd_5066126 2601357694239750992426317 := by
  unfold tailWord_5066126
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097099405537275285224279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123184530162865468187862821 23097099405537275285224279)
  ·
    refine ⟨34645649108305912927836419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23097099405537275285224279 34645649108305912927836419)
    ·
      refine ⟨51968473662458869391754629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34645649108305912927836419 51968473662458869391754629)
      ·
        refine ⟨9744088811711038010953993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51968473662458869391754629 9744088811711038010953993)
        ·
          refine ⟨7308066608783278508215495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9744088811711038010953993 7308066608783278508215495)
          ·
            refine ⟨10962099913174917762323243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308066608783278508215495 10962099913174917762323243)
            ·
              refine ⟨16443149869762376643484865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10962099913174917762323243 16443149869762376643484865)
              ·
                refine ⟨12332362402321782482613649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16443149869762376643484865 12332362402321782482613649)
                ·
                  refine ⟨9249271801741336861960237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332362402321782482613649 9249271801741336861960237)
                  ·
                    refine ⟨3468476925653001323235089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9249271801741336861960237 3468476925653001323235089)
                    ·
                      refine ⟨2601357694239750992426317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468476925653001323235089 2601357694239750992426317)
                      ·
                        rfl

theorem cell23_5066126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5066126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066126 prefixEnd_5066126 := by exact prefixLift 5066126
  have htrace : WordTrace (prefixWord ++ tailWord_5066126) baseStart_5066126 baseEnd_5066126 := by
    simpa [prefixWord, tailWord_5066126, baseEnd_5066126] using wordTrace_append hprefix tailTrace_5066126
  have hstable : (prefixWord ++ tailWord_5066126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066126).length < 2 ^ (prefixWord ++ tailWord_5066126).sum := by decide
  have hdescent : baseEnd_5066126 < baseStart_5066126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066282 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5066282 : Nat := 118140960795 + 5066282 * 2 ^ 59
def prefixEnd_5066282 : Nat := 4983230072969 + 3 ^ 40 * 5066282 * 2
def baseEnd_5066282 : Nat := 867145932407284127358533

theorem tailTrace_5066282 : CollatzResearch.WordTrace tailWord_5066282 prefixEnd_5066282 867145932407284127358533 := by
  unfold tailWord_5066282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195621257933260231118275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123188323354488693949648733 46195621257933260231118275)
  ·
    refine ⟨69293431886899890346677413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46195621257933260231118275 69293431886899890346677413)
    ·
      refine ⟨12992518478793729440002015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69293431886899890346677413 12992518478793729440002015)
      ·
        refine ⟨19488777718190594160003023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12992518478793729440002015 19488777718190594160003023)
        ·
          refine ⟨29233166577285891240004535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19488777718190594160003023 29233166577285891240004535)
          ·
            refine ⟨43849749865928836860006803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29233166577285891240004535 43849749865928836860006803)
            ·
              refine ⟨65774624798893255290010205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43849749865928836860006803 65774624798893255290010205)
              ·
                refine ⟨24665484299584970733753827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65774624798893255290010205 24665484299584970733753827)
                ·
                  refine ⟨36998226449377456100630741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24665484299584970733753827 36998226449377456100630741)
                  ·
                    refine ⟨867145932407284127358533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36998226449377456100630741 867145932407284127358533)
                    ·
                      rfl

theorem cell23_5066282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5066282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066282 prefixEnd_5066282 := by exact prefixLift 5066282
  have htrace : WordTrace (prefixWord ++ tailWord_5066282) baseStart_5066282 baseEnd_5066282 := by
    simpa [prefixWord, tailWord_5066282, baseEnd_5066282] using wordTrace_append hprefix tailTrace_5066282
  have hstable : (prefixWord ++ tailWord_5066282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066282).length < 2 ^ (prefixWord ++ tailWord_5066282).sum := by decide
  have hdescent : baseEnd_5066282 < baseStart_5066282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066286 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_5066286 : Nat := 118140960795 + 5066286 * 2 ^ 59
def prefixEnd_5066286 : Nat := 4983230072969 + 3 ^ 40 * 5066286 * 2
def baseEnd_5066286 : Nat := 289048872349385596269509

theorem tailTrace_5066286 : CollatzResearch.WordTrace tailWord_5066286 prefixEnd_5066286 289048872349385596269509 := by
  unfold tailWord_5066286
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097828865464818700952339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123188420615812366405079141 23097828865464818700952339)
  ·
    refine ⟨34646743298197228051428509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23097828865464818700952339 34646743298197228051428509)
    ·
      refine ⟨12992528736823960519285691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34646743298197228051428509 12992528736823960519285691)
      ·
        refine ⟨19488793105235940778928537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12992528736823960519285691 19488793105235940778928537)
        ·
          refine ⟨14616594828926955584196403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19488793105235940778928537 14616594828926955584196403)
          ·
            refine ⟨21924892243390433376294605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14616594828926955584196403 21924892243390433376294605)
            ·
              refine ⟨8221834591271412516110477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21924892243390433376294605 8221834591271412516110477)
              ·
                refine ⟨3083187971726779693541429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8221834591271412516110477 3083187971726779693541429)
                ·
                  refine ⟨289048872349385596269509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083187971726779693541429 289048872349385596269509)
                  ·
                    rfl

theorem cell23_5066286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_5066286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066286 prefixEnd_5066286 := by exact prefixLift 5066286
  have htrace : WordTrace (prefixWord ++ tailWord_5066286) baseStart_5066286 baseEnd_5066286 := by
    simpa [prefixWord, tailWord_5066286, baseEnd_5066286] using wordTrace_append hprefix tailTrace_5066286
  have hstable : (prefixWord ++ tailWord_5066286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066286).length < 2 ^ (prefixWord ++ tailWord_5066286).sum := by decide
  have hdescent : baseEnd_5066286 < baseStart_5066286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066333 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5066333 : Nat := 118140960795 + 5066333 * 2 ^ 59
def prefixEnd_5066333 : Nat := 4983230072969 + 3 ^ 40 * 5066333 * 2
def baseEnd_5066333 : Nat := 867154661578410560845955

theorem tailTrace_5066333 : CollatzResearch.WordTrace tailWord_5066333 prefixEnd_5066333 867154661578410560845955 := by
  unfold tailWord_5066333
  simp only [CollatzResearch.WordTrace]
  refine ⟨184784345154548276634579653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123189563436365517756386435 184784345154548276634579653)
  ·
    refine ⟨34647064716477801868983685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184784345154548276634579653 34647064716477801868983685)
    ·
      refine ⟨6496324634339587850434441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34647064716477801868983685 6496324634339587850434441)
      ·
        refine ⟨4872243475754690887825831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6496324634339587850434441 4872243475754690887825831)
        ·
          refine ⟨7308365213632036331738747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872243475754690887825831 7308365213632036331738747)
          ·
            refine ⟨10962547820448054497608121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308365213632036331738747 10962547820448054497608121)
            ·
              refine ⟨8221910865336040873206091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10962547820448054497608121 8221910865336040873206091)
              ·
                refine ⟨12332866298004061309809137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8221910865336040873206091 12332866298004061309809137)
                ·
                  refine ⟨9249649723503045982356853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332866298004061309809137 9249649723503045982356853)
                  ·
                    refine ⟨867154661578410560845955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9249649723503045982356853 867154661578410560845955)
                    ·
                      rfl

theorem cell23_5066333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5066333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066333 prefixEnd_5066333 := by exact prefixLift 5066333
  have htrace : WordTrace (prefixWord ++ tailWord_5066333) baseStart_5066333 baseEnd_5066333 := by
    simpa [prefixWord, tailWord_5066333, baseEnd_5066333] using wordTrace_append hprefix tailTrace_5066333
  have hstable : (prefixWord ++ tailWord_5066333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066333).length < 2 ^ (prefixWord ++ tailWord_5066333).sum := by decide
  have hdescent : baseEnd_5066333 < baseStart_5066333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066339 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3]
def baseStart_5066339 : Nat := 118140960795 + 5066339 * 2 ^ 59
def prefixEnd_5066339 : Nat := 4983230072969 + 3 ^ 40 * 5066339 * 2
def baseEnd_5066339 : Nat := 2601467065619158659062837

theorem tailTrace_5066339 : CollatzResearch.WordTrace tailWord_5066339 prefixEnd_5066339 2601467065619158659062837 := by
  unfold tailWord_5066339
  simp only [CollatzResearch.WordTrace]
  refine ⟨184784563992526539659298071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123189709328351026439532047 184784563992526539659298071)
  ·
    refine ⟨277176845988789809488947107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184784563992526539659298071 277176845988789809488947107)
    ·
      refine ⟨415765268983184714233420661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277176845988789809488947107 415765268983184714233420661)
      ·
        refine ⟨38977993967173566959383187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 415765268983184714233420661 38977993967173566959383187)
        ·
          refine ⟨58466990950760350439074781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38977993967173566959383187 58466990950760350439074781)
          ·
            refine ⟨21925121606535131414653043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58466990950760350439074781 21925121606535131414653043)
            ·
              refine ⟨32887682409802697121979565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21925121606535131414653043 32887682409802697121979565)
              ·
                refine ⟨12332880903676011420742337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32887682409802697121979565 12332880903676011420742337)
                ·
                  refine ⟨9249660677757008565556753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332880903676011420742337 9249660677757008565556753)
                  ·
                    refine ⟨6937245508317756424167565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9249660677757008565556753 6937245508317756424167565)
                    ·
                      refine ⟨2601467065619158659062837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937245508317756424167565 2601467065619158659062837)
                      ·
                        rfl

theorem cell23_5066339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_5066339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066339 prefixEnd_5066339 := by exact prefixLift 5066339
  have htrace : WordTrace (prefixWord ++ tailWord_5066339) baseStart_5066339 baseEnd_5066339 := by
    simpa [prefixWord, tailWord_5066339, baseEnd_5066339] using wordTrace_append hprefix tailTrace_5066339
  have hstable : (prefixWord ++ tailWord_5066339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066339).length < 2 ^ (prefixWord ++ tailWord_5066339).sum := by decide
  have hdescent : baseEnd_5066339 < baseStart_5066339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066379 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 5, 2]
def baseStart_5066379 : Nat := 118140960795 + 5066379 * 2 ^ 59
def prefixEnd_5066379 : Nat := 4983230072969 + 3 ^ 40 * 5066379 * 2
def baseEnd_5066379 : Nat := 2601487604845338502562653

theorem tailTrace_5066379 : CollatzResearch.WordTrace tailWord_5066379 prefixEnd_5066379 2601487604845338502562653 := by
  unfold tailWord_5066379
  simp only [CollatzResearch.WordTrace]
  refine ⟨184786022912381626490754191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123190681941587750993836127 184786022912381626490754191)
  ·
    refine ⟨277179034368572439736131287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184786022912381626490754191 277179034368572439736131287)
    ·
      refine ⟨415768551552858659604196931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277179034368572439736131287 415768551552858659604196931)
      ·
        refine ⟨623652827329287989406295397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415768551552858659604196931 623652827329287989406295397)
        ·
          refine ⟨116934905124241498013680387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 623652827329287989406295397 116934905124241498013680387)
          ·
            refine ⟨175402357686362247020520581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116934905124241498013680387 175402357686362247020520581)
            ·
              refine ⟨32887942066192921316347609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175402357686362247020520581 32887942066192921316347609)
              ·
                refine ⟨24665956549644690987260707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32887942066192921316347609 24665956549644690987260707)
                ·
                  refine ⟨36998934824467036480891061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24665956549644690987260707 36998934824467036480891061)
                  ·
                    refine ⟨3468650139793784670083537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36998934824467036480891061 3468650139793784670083537)
                    ·
                      refine ⟨2601487604845338502562653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468650139793784670083537 2601487604845338502562653)
                      ·
                        rfl

theorem cell23_5066379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5, 2].length) (baseStart_5066379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066379 prefixEnd_5066379 := by exact prefixLift 5066379
  have htrace : WordTrace (prefixWord ++ tailWord_5066379) baseStart_5066379 baseEnd_5066379 := by
    simpa [prefixWord, tailWord_5066379, baseEnd_5066379] using wordTrace_append hprefix tailTrace_5066379
  have hstable : (prefixWord ++ tailWord_5066379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066379).length < 2 ^ (prefixWord ++ tailWord_5066379).sum := by decide
  have hdescent : baseEnd_5066379 < baseStart_5066379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066403 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 1, 1, 3]
def baseStart_5066403 : Nat := 118140960795 + 5066403 * 2 ^ 59
def prefixEnd_5066403 : Nat := 4983230072969 + 3 ^ 40 * 5066403 * 2
def baseEnd_5066403 : Nat := 2601499928381046408662543

theorem tailTrace_5066403 : CollatzResearch.WordTrace tailWord_5066403 prefixEnd_5066403 2601499928381046408662543 := by
  unfold tailWord_5066403
  simp only [CollatzResearch.WordTrace]
  refine ⟨184786898264294678589627863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123191265509529785726418575 184786898264294678589627863)
  ·
    refine ⟨277180347396442017884441795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184786898264294678589627863 277180347396442017884441795)
    ·
      refine ⟨415770521094663026826662693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277180347396442017884441795 415770521094663026826662693)
      ·
        refine ⟨77956972705249317529999255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 415770521094663026826662693 77956972705249317529999255)
        ·
          refine ⟨116935459057873976294998883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77956972705249317529999255 116935459057873976294998883)
          ·
            refine ⟨175403188586810964442498325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116935459057873976294998883 175403188586810964442498325)
            ·
              refine ⟨8222024465006763958242109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175403188586810964442498325 8222024465006763958242109)
              ·
                refine ⟨3083259174377536484340791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8222024465006763958242109 3083259174377536484340791)
                ·
                  refine ⟨4624888761566304726511187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083259174377536484340791 4624888761566304726511187)
                  ·
                    refine ⟨6937333142349457089766781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624888761566304726511187 6937333142349457089766781)
                    ·
                      refine ⟨2601499928381046408662543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937333142349457089766781 2601499928381046408662543)
                      ·
                        rfl

theorem cell23_5066403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_5066403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066403 prefixEnd_5066403 := by exact prefixLift 5066403
  have htrace : WordTrace (prefixWord ++ tailWord_5066403) baseStart_5066403 baseEnd_5066403 := by
    simpa [prefixWord, tailWord_5066403, baseEnd_5066403] using wordTrace_append hprefix tailTrace_5066403
  have hstable : (prefixWord ++ tailWord_5066403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066403).length < 2 ^ (prefixWord ++ tailWord_5066403).sum := by decide
  have hdescent : baseEnd_5066403 < baseStart_5066403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066412 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_5066412 : Nat := 118140960795 + 5066412 * 2 ^ 59
def prefixEnd_5066412 : Nat := 4983230072969 + 3 ^ 40 * 5066412 * 2
def baseEnd_5066412 : Nat := 2601504549706936873450001

theorem tailTrace_5066412 : CollatzResearch.WordTrace tailWord_5066412 prefixEnd_5066412 2601504549706936873450001 := by
  unfold tailWord_5066412
  simp only [CollatzResearch.WordTrace]
  refine ⟨92393613260631036563352745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123191484347508048751136993 92393613260631036563352745)
  ·
    refine ⟨69295209945473277422514559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92393613260631036563352745 69295209945473277422514559)
    ·
      refine ⟨103942814918209916133771839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69295209945473277422514559 103942814918209916133771839)
      ·
        refine ⟨155914222377314874200657759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103942814918209916133771839 155914222377314874200657759)
        ·
          refine ⟨233871333565972311300986639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155914222377314874200657759 233871333565972311300986639)
          ·
            refine ⟨350807000348958466951479959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233871333565972311300986639 350807000348958466951479959)
            ·
              refine ⟨526210500523437700427219939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350807000348958466951479959 526210500523437700427219939)
              ·
                refine ⟨789315750785156550640829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526210500523437700427219939 789315750785156550640829909)
                ·
                  refine ⟨18499587909027106655644451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 789315750785156550640829909 18499587909027106655644451)
                  ·
                    refine ⟨27749381863540659983466677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18499587909027106655644451 27749381863540659983466677)
                    ·
                      refine ⟨2601504549706936873450001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27749381863540659983466677 2601504549706936873450001)
                      ·
                        rfl

theorem cell23_5066412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_5066412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066412 prefixEnd_5066412 := by exact prefixLift 5066412
  have htrace : WordTrace (prefixWord ++ tailWord_5066412) baseStart_5066412 baseEnd_5066412 := by
    simpa [prefixWord, tailWord_5066412, baseEnd_5066412] using wordTrace_append hprefix tailTrace_5066412
  have hstable : (prefixWord ++ tailWord_5066412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066412).length < 2 ^ (prefixWord ++ tailWord_5066412).sum := by decide
  have hdescent : baseEnd_5066412 < baseStart_5066412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066419 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 4, 4]
def baseStart_5066419 : Nat := 118140960795 + 5066419 * 2 ^ 59
def prefixEnd_5066419 : Nat := 4983230072969 + 3 ^ 40 * 5066419 * 2
def baseEnd_5066419 : Nat := 867169381357172782020823

theorem tailTrace_5066419 : CollatzResearch.WordTrace tailWord_5066419 prefixEnd_5066419 867169381357172782020823 := by
  unfold tailWord_5066419
  simp only [CollatzResearch.WordTrace]
  refine ⟨184787481832236713322210311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123191654554824475548140207 184787481832236713322210311)
  ·
    refine ⟨277181222748355069983315467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184787481832236713322210311 277181222748355069983315467)
    ·
      refine ⟨415771834122532604974973201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277181222748355069983315467 415771834122532604974973201)
      ·
        refine ⟨311828875591899453731229901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415771834122532604974973201 311828875591899453731229901)
        ·
          refine ⟨116935828346962295149211213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311828875591899453731229901 116935828346962295149211213)
          ·
            refine ⟨43850935630110860680954205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116935828346962295149211213 43850935630110860680954205)
            ·
              refine ⟨16444100861291572755357827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43850935630110860680954205 16444100861291572755357827)
              ·
                refine ⟨24666151291937359133036741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16444100861291572755357827 24666151291937359133036741)
                ·
                  refine ⟨4624903367238254837444389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24666151291937359133036741 4624903367238254837444389)
                  ·
                    refine ⟨867169381357172782020823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624903367238254837444389 867169381357172782020823)
                    ·
                      rfl

theorem cell23_5066419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 4].length) (baseStart_5066419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066419 prefixEnd_5066419 := by exact prefixLift 5066419
  have htrace : WordTrace (prefixWord ++ tailWord_5066419) baseStart_5066419 baseEnd_5066419 := by
    simpa [prefixWord, tailWord_5066419, baseEnd_5066419] using wordTrace_append hprefix tailTrace_5066419
  have hstable : (prefixWord ++ tailWord_5066419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066419).length < 2 ^ (prefixWord ++ tailWord_5066419).sum := by decide
  have hdescent : baseEnd_5066419 < baseStart_5066419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066429 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_5066429 : Nat := 118140960795 + 5066429 * 2 ^ 59
def prefixEnd_5066429 : Nat := 4983230072969 + 3 ^ 40 * 5066429 * 2
def baseEnd_5066429 : Nat := 2601513278878063306937423

theorem tailTrace_5066429 : CollatzResearch.WordTrace tailWord_5066429 prefixEnd_5066429 2601513278878063306937423 := by
  unfold tailWord_5066429
  simp only [CollatzResearch.WordTrace]
  refine ⟨184787846562200485030074341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123191897708133656686716227 184787846562200485030074341)
  ·
    refine ⟨34647721230412590943138939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184787846562200485030074341 34647721230412590943138939)
    ·
      refine ⟨51971581845618886414708409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34647721230412590943138939 51971581845618886414708409)
      ·
        refine ⟨38978686384214164811031307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51971581845618886414708409 38978686384214164811031307)
        ·
          refine ⟨58468029576321247216546961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38978686384214164811031307 58468029576321247216546961)
          ·
            refine ⟨43851022182240935412410221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58468029576321247216546961 43851022182240935412410221)
            ·
              refine ⟨16444133318340350779653833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43851022182240935412410221 16444133318340350779653833)
              ·
                refine ⟨12333099988755263084740375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16444133318340350779653833 12333099988755263084740375)
                ·
                  refine ⟨18499649983132894627110563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12333099988755263084740375 18499649983132894627110563)
                  ·
                    refine ⟨27749474974699341940665845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18499649983132894627110563 27749474974699341940665845)
                    ·
                      refine ⟨2601513278878063306937423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27749474974699341940665845 2601513278878063306937423)
                      ·
                        rfl

theorem cell23_5066429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_5066429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066429 prefixEnd_5066429 := by exact prefixLift 5066429
  have htrace : WordTrace (prefixWord ++ tailWord_5066429) baseStart_5066429 baseEnd_5066429 := by
    simpa [prefixWord, tailWord_5066429, baseEnd_5066429] using wordTrace_append hprefix tailTrace_5066429
  have hstable : (prefixWord ++ tailWord_5066429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066429).length < 2 ^ (prefixWord ++ tailWord_5066429).sum := by decide
  have hdescent : baseEnd_5066429 < baseStart_5066429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066432 : List Nat := [2, 1, 1, 2, 4, 1, 2, 10]
def baseStart_5066432 : Nat := 118140960795 + 5066432 * 2 ^ 59
def prefixEnd_5066432 : Nat := 4983230072969 + 3 ^ 40 * 5066432 * 2
def baseEnd_5066432 : Nat := 96352400715556547970367

theorem tailTrace_5066432 : CollatzResearch.WordTrace tailWord_5066432 prefixEnd_5066432 96352400715556547970367 := by
  unfold tailWord_5066432
  simp only [CollatzResearch.WordTrace]
  refine ⟨92393977990594808271216775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123191970654126411028289033 92393977990594808271216775)
  ·
    refine ⟨138590966985892212406825163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92393977990594808271216775 138590966985892212406825163)
    ·
      refine ⟨207886450478838318610237745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138590966985892212406825163 207886450478838318610237745)
      ·
        refine ⟨155914837859128738957678309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207886450478838318610237745 155914837859128738957678309)
        ·
          refine ⟨29234032098586638554564683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155914837859128738957678309 29234032098586638554564683)
          ·
            refine ⟨43851048147879957831847025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29234032098586638554564683 43851048147879957831847025)
            ·
              refine ⟨32888286110909968373885269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43851048147879957831847025 32888286110909968373885269)
              ·
                refine ⟨96352400715556547970367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32888286110909968373885269 96352400715556547970367)
                ·
                  rfl

theorem cell23_5066432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 10].length) (baseStart_5066432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066432 prefixEnd_5066432 := by exact prefixLift 5066432
  have htrace : WordTrace (prefixWord ++ tailWord_5066432) baseStart_5066432 baseEnd_5066432 := by
    simpa [prefixWord, tailWord_5066432, baseEnd_5066432] using wordTrace_append hprefix tailTrace_5066432
  have hstable : (prefixWord ++ tailWord_5066432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066432).length < 2 ^ (prefixWord ++ tailWord_5066432).sum := by decide
  have hdescent : baseEnd_5066432 < baseStart_5066432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066449 : List Nat := [1, 2, 2, 1, 2, 4, 4, 7]
def baseStart_5066449 : Nat := 118140960795 + 5066449 * 2 ^ 59
def prefixEnd_5066449 : Nat := 4983230072969 + 3 ^ 40 * 5066449 * 2
def baseEnd_5066449 : Nat := 96352724018190860321753

theorem tailTrace_5066449 : CollatzResearch.WordTrace tailWord_5066449 prefixEnd_5066449 96352724018190860321753 := by
  unfold tailWord_5066449
  simp only [CollatzResearch.WordTrace]
  refine ⟨184788576022128028445802401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123192384014752018963868267 184788576022128028445802401)
  ·
    refine ⟨138591432016596021334351801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184788576022128028445802401 138591432016596021334351801)
    ·
      refine ⟨103943574012447016000763851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138591432016596021334351801 103943574012447016000763851)
      ·
        refine ⟨155915361018670524001145777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103943574012447016000763851 155915361018670524001145777)
        ·
          refine ⟨116936520764002893000859333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155915361018670524001145777 116936520764002893000859333)
          ·
            refine ⟨21925597643250542437661125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116936520764002893000859333 21925597643250542437661125)
            ·
              refine ⟨4111049558109476707061461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21925597643250542437661125 4111049558109476707061461)
              ·
                refine ⟨96352724018190860321753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4111049558109476707061461 96352724018190860321753)
                ·
                  rfl

theorem cell23_5066449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 7].length) (baseStart_5066449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066449 prefixEnd_5066449 := by exact prefixLift 5066449
  have htrace : WordTrace (prefixWord ++ tailWord_5066449) baseStart_5066449 baseEnd_5066449 := by
    simpa [prefixWord, tailWord_5066449, baseEnd_5066449] using wordTrace_append hprefix tailTrace_5066449
  have hstable : (prefixWord ++ tailWord_5066449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066449).length < 2 ^ (prefixWord ++ tailWord_5066449).sum := by decide
  have hdescent : baseEnd_5066449 < baseStart_5066449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066476 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_5066476 : Nat := 118140960795 + 5066476 * 2 ^ 59
def prefixEnd_5066476 : Nat := 4983230072969 + 3 ^ 40 * 5066476 * 2
def baseEnd_5066476 : Nat := 2601537412468824623049707

theorem tailTrace_5066476 : CollatzResearch.WordTrace tailWord_5066476 prefixEnd_5066476 2601537412468824623049707 := by
  unfold tailWord_5066476
  simp only [CollatzResearch.WordTrace]
  refine ⟨92394780396515106028517641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123193040528686808038023521 92394780396515106028517641)
  ·
    refine ⟨69296085297386329521388231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92394780396515106028517641 69296085297386329521388231)
    ·
      refine ⟨103944127946079494282082347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69296085297386329521388231 103944127946079494282082347)
      ·
        refine ⟨155916191919119241423123521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103944127946079494282082347 155916191919119241423123521)
        ·
          refine ⟨116937143939339431067342641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155916191919119241423123521 116937143939339431067342641)
          ·
            refine ⟨87702857954504573300506981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116937143939339431067342641 87702857954504573300506981)
            ·
              refine ⟨16444285866469607493845059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87702857954504573300506981 16444285866469607493845059)
              ·
                refine ⟨24666428799704411240767589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16444285866469607493845059 24666428799704411240767589)
                ·
                  refine ⟨4624955399944577107643923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24666428799704411240767589 4624955399944577107643923)
                  ·
                    refine ⟨6937433099916865661465885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624955399944577107643923 6937433099916865661465885)
                    ·
                      refine ⟨2601537412468824623049707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937433099916865661465885 2601537412468824623049707)
                      ·
                        rfl

theorem cell23_5066476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_5066476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066476 prefixEnd_5066476 := by exact prefixLift 5066476
  have htrace : WordTrace (prefixWord ++ tailWord_5066476) baseStart_5066476 baseEnd_5066476 := by
    simpa [prefixWord, tailWord_5066476, baseEnd_5066476] using wordTrace_append hprefix tailTrace_5066476
  have hstable : (prefixWord ++ tailWord_5066476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066476).length < 2 ^ (prefixWord ++ tailWord_5066476).sum := by decide
  have hdescent : baseEnd_5066476 < baseStart_5066476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066536 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_5066536 : Nat := 118140960795 + 5066536 * 2 ^ 59
def prefixEnd_5066536 : Nat := 4983230072969 + 3 ^ 40 * 5066536 * 2
def baseEnd_5066536 : Nat := 2601568221308094388299431

theorem tailTrace_5066536 : CollatzResearch.WordTrace tailWord_5066536 prefixEnd_5066536 2601568221308094388299431 := by
  unfold tailWord_5066536
  simp only [CollatzResearch.WordTrace]
  refine ⟨92395874586406421152109731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123194499448541894869479641 92395874586406421152109731)
  ·
    refine ⟨138593811879609631728164597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92395874586406421152109731 138593811879609631728164597)
    ·
      refine ⟨12993169863713402974515431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138593811879609631728164597 12993169863713402974515431)
      ·
        refine ⟨19489754795570104461773147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12993169863713402974515431 19489754795570104461773147)
        ·
          refine ⟨29234632193355156692659721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19489754795570104461773147 29234632193355156692659721)
          ·
            refine ⟨21925974145016367519494791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29234632193355156692659721 21925974145016367519494791)
            ·
              refine ⟨32888961217524551279242187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21925974145016367519494791 32888961217524551279242187)
              ·
                refine ⟨49333441826286826918863281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32888961217524551279242187 49333441826286826918863281)
                ·
                  refine ⟨37000081369715120189147461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49333441826286826918863281 37000081369715120189147461)
                  ·
                    refine ⟨6937515256821585035465149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37000081369715120189147461 6937515256821585035465149)
                    ·
                      refine ⟨2601568221308094388299431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937515256821585035465149 2601568221308094388299431)
                      ·
                        rfl

theorem cell23_5066536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_5066536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066536 prefixEnd_5066536 := by exact prefixLift 5066536
  have htrace : WordTrace (prefixWord ++ tailWord_5066536) baseStart_5066536 baseEnd_5066536 := by
    simpa [prefixWord, tailWord_5066536, baseEnd_5066536] using wordTrace_append hprefix tailTrace_5066536
  have hstable : (prefixWord ++ tailWord_5066536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066536).length < 2 ^ (prefixWord ++ tailWord_5066536).sum := by decide
  have hdescent : baseEnd_5066536 < baseStart_5066536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066546 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_5066546 : Nat := 118140960795 + 5066546 * 2 ^ 59
def prefixEnd_5066546 : Nat := 4983230072969 + 3 ^ 40 * 5066546 * 2
def baseEnd_5066546 : Nat := 2601573356114639349174385

theorem tailTrace_5066546 : CollatzResearch.WordTrace tailWord_5066546 prefixEnd_5066546 2601573356114639349174385 := by
  unfold tailWord_5066546
  simp only [CollatzResearch.WordTrace]
  refine ⟨46198028475694153503020873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123194742601851076008055661 46198028475694153503020873)
  ·
    refine ⟨34648521356770615127265655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46198028475694153503020873 34648521356770615127265655)
    ·
      refine ⟨51972782035155922690898483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34648521356770615127265655 51972782035155922690898483)
      ·
        refine ⟨77959173052733884036347725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51972782035155922690898483 77959173052733884036347725)
        ·
          refine ⟨29234689894775206513630397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77959173052733884036347725 29234689894775206513630397)
          ·
            refine ⟨10963008710540702442611399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29234689894775206513630397 10963008710540702442611399)
            ·
              refine ⟨16444513065811053663917099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10963008710540702442611399 16444513065811053663917099)
              ·
                refine ⟨24666769598716580495875649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16444513065811053663917099 24666769598716580495875649)
                ·
                  refine ⟨18500077199037435371906737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24666769598716580495875649 18500077199037435371906737)
                  ·
                    refine ⟨13875057899278076528930053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18500077199037435371906737 13875057899278076528930053)
                    ·
                      refine ⟨2601573356114639349174385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13875057899278076528930053 2601573356114639349174385)
                      ·
                        rfl

theorem cell23_5066546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_5066546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066546 prefixEnd_5066546 := by exact prefixLift 5066546
  have htrace : WordTrace (prefixWord ++ tailWord_5066546) baseStart_5066546 baseEnd_5066546 := by
    simpa [prefixWord, tailWord_5066546, baseEnd_5066546] using wordTrace_append hprefix tailTrace_5066546
  have hstable : (prefixWord ++ tailWord_5066546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066546).length < 2 ^ (prefixWord ++ tailWord_5066546).sum := by decide
  have hdescent : baseEnd_5066546 < baseStart_5066546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066550 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5066550 : Nat := 118140960795 + 5066550 * 2 ^ 59
def prefixEnd_5066550 : Nat := 4983230072969 + 3 ^ 40 * 5066550 * 2
def baseEnd_5066550 : Nat := 2601575410037257333524367

theorem tailTrace_5066550 : CollatzResearch.WordTrace tailWord_5066550 prefixEnd_5066550 2601575410037257333524367 := by
  unfold tailWord_5066550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11549516237172632668451819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123194839863174748463486069 11549516237172632668451819)
  ·
    refine ⟨17324274355758949002677729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11549516237172632668451819 17324274355758949002677729)
    ·
      refine ⟨12993205766819211752008297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17324274355758949002677729 12993205766819211752008297)
      ·
        refine ⟨9744904325114408814006223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12993205766819211752008297 9744904325114408814006223)
        ·
          refine ⟨14617356487671613221009335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9744904325114408814006223 14617356487671613221009335)
          ·
            refine ⟨21926034731507419831514003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14617356487671613221009335 21926034731507419831514003)
            ·
              refine ⟨32889052097261129747271005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21926034731507419831514003 32889052097261129747271005)
              ·
                refine ⟨12333394536472923655226627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32889052097261129747271005 12333394536472923655226627)
                ·
                  refine ⟨18500091804709385482839941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12333394536472923655226627 18500091804709385482839941)
                  ·
                    refine ⟨3468767213383009778032489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18500091804709385482839941 3468767213383009778032489)
                    ·
                      refine ⟨2601575410037257333524367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468767213383009778032489 2601575410037257333524367)
                      ·
                        rfl

theorem cell23_5066550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5066550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066550 prefixEnd_5066550 := by exact prefixLift 5066550
  have htrace : WordTrace (prefixWord ++ tailWord_5066550) baseStart_5066550 baseEnd_5066550 := by
    simpa [prefixWord, tailWord_5066550, baseEnd_5066550] using wordTrace_append hprefix tailTrace_5066550
  have hstable : (prefixWord ++ tailWord_5066550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066550).length < 2 ^ (prefixWord ++ tailWord_5066550).sum := by decide
  have hdescent : baseEnd_5066550 < baseStart_5066550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066569 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_5066569 : Nat := 118140960795 + 5066569 * 2 ^ 59
def prefixEnd_5066569 : Nat := 4983230072969 + 3 ^ 40 * 5066569 * 2
def baseEnd_5066569 : Nat := 867195055389897586395593

theorem tailTrace_5066569 : CollatzResearch.WordTrace tailWord_5066569 prefixEnd_5066569 867195055389897586395593 := by
  unfold tailWord_5066569
  simp only [CollatzResearch.WordTrace]
  refine ⟨184792952781693288940170761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123195301854462192626780507 184792952781693288940170761)
  ·
    refine ⟨138594714586269966705128071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184792952781693288940170761 138594714586269966705128071)
    ·
      refine ⟨207892071879404950057692107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138594714586269966705128071 207892071879404950057692107)
      ·
        refine ⟨311838107819107425086538161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207892071879404950057692107 311838107819107425086538161)
        ·
          refine ⟨233878580864330568814903621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311838107819107425086538161 233878580864330568814903621)
          ·
            refine ⟨43852233912061981652794429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233878580864330568814903621 43852233912061981652794429)
            ·
              refine ⟨16444587717023243119797911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43852233912061981652794429 16444587717023243119797911)
              ·
                refine ⟨24666881575534864679696867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16444587717023243119797911 24666881575534864679696867)
                ·
                  refine ⟨37000322363302297019545301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24666881575534864679696867 37000322363302297019545301)
                  ·
                    refine ⟨867195055389897586395593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37000322363302297019545301 867195055389897586395593)
                    ·
                      rfl

theorem cell23_5066569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_5066569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066569 prefixEnd_5066569 := by exact prefixLift 5066569
  have htrace : WordTrace (prefixWord ++ tailWord_5066569) baseStart_5066569 baseEnd_5066569 := by
    simpa [prefixWord, tailWord_5066569, baseEnd_5066569] using wordTrace_append hprefix tailTrace_5066569
  have hstable : (prefixWord ++ tailWord_5066569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066569).length < 2 ^ (prefixWord ++ tailWord_5066569).sum := by decide
  have hdescent : baseEnd_5066569 < baseStart_5066569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066619 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_5066619 : Nat := 118140960795 + 5066619 * 2 ^ 59
def prefixEnd_5066619 : Nat := 4983230072969 + 3 ^ 40 * 5066619 * 2
def baseEnd_5066619 : Nat := 2601610840202417563561549

theorem tailTrace_5066619 : CollatzResearch.WordTrace tailWord_5066619 prefixEnd_5066619 2601610840202417563561549 := by
  unfold tailWord_5066619
  simp only [CollatzResearch.WordTrace]
  refine ⟨184794776431512147479490911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123196517621008098319660607 184794776431512147479490911)
  ·
    refine ⟨277192164647268221219236367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184794776431512147479490911 277192164647268221219236367)
    ·
      refine ⟨415788246970902331828854551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277192164647268221219236367 415788246970902331828854551)
      ·
        refine ⟨623682370456353497743281827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415788246970902331828854551 623682370456353497743281827)
        ·
          refine ⟨935523555684530246614922741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623682370456353497743281827 935523555684530246614922741)
          ·
            refine ⟨87705333345424710620149007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 935523555684530246614922741 87705333345424710620149007)
            ·
              refine ⟨131558000018137065930223511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87705333345424710620149007 131558000018137065930223511)
              ·
                refine ⟨197337000027205598895335267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131558000018137065930223511 197337000027205598895335267)
                ·
                  refine ⟨296005500040808398343002901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197337000027205598895335267 296005500040808398343002901)
                  ·
                    refine ⟨13875257814412893672328261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 296005500040808398343002901 13875257814412893672328261)
                    ·
                      refine ⟨2601610840202417563561549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13875257814412893672328261 2601610840202417563561549)
                      ·
                        rfl

theorem cell23_5066619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_5066619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066619 prefixEnd_5066619 := by exact prefixLift 5066619
  have htrace : WordTrace (prefixWord ++ tailWord_5066619) baseStart_5066619 baseEnd_5066619 := by
    simpa [prefixWord, tailWord_5066619, baseEnd_5066619] using wordTrace_append hprefix tailTrace_5066619
  have hstable : (prefixWord ++ tailWord_5066619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066619).length < 2 ^ (prefixWord ++ tailWord_5066619).sum := by decide
  have hdescent : baseEnd_5066619 < baseStart_5066619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066629 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 10]
def baseStart_5066629 : Nat := 118140960795 + 5066629 * 2 ^ 59
def prefixEnd_5066629 : Nat := 4983230072969 + 3 ^ 40 * 5066629 * 2
def baseEnd_5066629 : Nat := 289068441667662502715167

theorem tailTrace_5066629 : CollatzResearch.WordTrace tailWord_5066629 prefixEnd_5066629 289068441667662502715167 := by
  unfold tailWord_5066629
  simp only [CollatzResearch.WordTrace]
  refine ⟨184795141161475919187354941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123196760774317279458236627 184795141161475919187354941)
  ·
    refine ⟨69298177935553469695258103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184795141161475919187354941 69298177935553469695258103)
    ·
      refine ⟨103947266903330204542887155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69298177935553469695258103 103947266903330204542887155)
      ·
        refine ⟨155920900354995306814330733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103947266903330204542887155 155920900354995306814330733)
        ·
          refine ⟨58470337633123240055374025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155920900354995306814330733 58470337633123240055374025)
          ·
            refine ⟨43852753224842430041530519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58470337633123240055374025 43852753224842430041530519)
            ·
              refine ⟨65779129837263645062295779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43852753224842430041530519 65779129837263645062295779)
              ·
                refine ⟨98668694755895467593443669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65779129837263645062295779 98668694755895467593443669)
                ·
                  refine ⟨289068441667662502715167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98668694755895467593443669 289068441667662502715167)
                  ·
                    rfl

theorem cell23_5066629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_5066629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066629 prefixEnd_5066629 := by exact prefixLift 5066629
  have htrace : WordTrace (prefixWord ++ tailWord_5066629) baseStart_5066629 baseEnd_5066629 := by
    simpa [prefixWord, tailWord_5066629, baseEnd_5066629] using wordTrace_append hprefix tailTrace_5066629
  have hstable : (prefixWord ++ tailWord_5066629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066629).length < 2 ^ (prefixWord ++ tailWord_5066629).sum := by decide
  have hdescent : baseEnd_5066629 < baseStart_5066629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066649 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_5066649 : Nat := 118140960795 + 5066649 * 2 ^ 59
def prefixEnd_5066649 : Nat := 4983230072969 + 3 ^ 40 * 5066649 * 2
def baseEnd_5066649 : Nat := 2601626244622052446186411

theorem tailTrace_5066649 : CollatzResearch.WordTrace tailWord_5066649 prefixEnd_5066649 2601626244622052446186411 := by
  unfold tailWord_5066649
  simp only [CollatzResearch.WordTrace]
  refine ⟨184795870621403462603083001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123197247080935641735388667 184795870621403462603083001)
  ·
    refine ⟨138596902966052596952312251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184795870621403462603083001 138596902966052596952312251)
    ·
      refine ⟨207895354449078895428468377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138596902966052596952312251 207895354449078895428468377)
      ·
        refine ⟨155921515836809171571351283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207895354449078895428468377 155921515836809171571351283)
        ·
          refine ⟨233882273755213757357026925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155921515836809171571351283 233882273755213757357026925)
          ·
            refine ⟨87705852658205159008885097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233882273755213757357026925 87705852658205159008885097)
            ·
              refine ⟨65779389493653869256663823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87705852658205159008885097 65779389493653869256663823)
              ·
                refine ⟨98669084240480803884995735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65779389493653869256663823 98669084240480803884995735)
                ·
                  refine ⟨148003626360721205827493603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98669084240480803884995735 148003626360721205827493603)
                  ·
                    refine ⟨222005439541081808741240405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148003626360721205827493603 222005439541081808741240405)
                    ·
                      refine ⟨2601626244622052446186411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 222005439541081808741240405 2601626244622052446186411)
                      ·
                        rfl

theorem cell23_5066649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_5066649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066649 prefixEnd_5066649 := by exact prefixLift 5066649
  have htrace : WordTrace (prefixWord ++ tailWord_5066649) baseStart_5066649 baseEnd_5066649 := by
    simpa [prefixWord, tailWord_5066649, baseEnd_5066649] using wordTrace_append hprefix tailTrace_5066649
  have hstable : (prefixWord ++ tailWord_5066649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066649).length < 2 ^ (prefixWord ++ tailWord_5066649).sum := by decide
  have hdescent : baseEnd_5066649 < baseStart_5066649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066650 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_5066650 : Nat := 118140960795 + 5066650 * 2 ^ 59
def prefixEnd_5066650 : Nat := 4983230072969 + 3 ^ 40 * 5066650 * 2
def baseEnd_5066650 : Nat := 867208919367568980757969

theorem tailTrace_5066650 : CollatzResearch.WordTrace tailWord_5066650 prefixEnd_5066650 867208919367568980757969 := by
  unfold tailWord_5066650
  simp only [CollatzResearch.WordTrace]
  refine ⟨46198976773599959943467351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123197271396266559849246269 46198976773599959943467351)
  ·
    refine ⟨69298465160399939915201027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46198976773599959943467351 69298465160399939915201027)
    ·
      refine ⟨103947697740599909872801541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69298465160399939915201027 103947697740599909872801541)
      ·
        refine ⟨19490193326362483101150289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103947697740599909872801541 19490193326362483101150289)
        ·
          refine ⟨14617644994771862325862717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19490193326362483101150289 14617644994771862325862717)
          ·
            refine ⟨5481616873039448372198519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14617644994771862325862717 5481616873039448372198519)
            ·
              refine ⟨8222425309559172558297779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481616873039448372198519 8222425309559172558297779)
              ·
                refine ⟨12333637964338758837446669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222425309559172558297779 12333637964338758837446669)
                ·
                  refine ⟨4625114236627034564042501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12333637964338758837446669 4625114236627034564042501)
                  ·
                    refine ⟨867208919367568980757969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625114236627034564042501 867208919367568980757969)
                    ·
                      rfl

theorem cell23_5066650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_5066650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066650 prefixEnd_5066650 := by exact prefixLift 5066650
  have htrace : WordTrace (prefixWord ++ tailWord_5066650) baseStart_5066650 baseEnd_5066650 := by
    simpa [prefixWord, tailWord_5066650, baseEnd_5066650] using wordTrace_append hprefix tailTrace_5066650
  have hstable : (prefixWord ++ tailWord_5066650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066650).length < 2 ^ (prefixWord ++ tailWord_5066650).sum := by decide
  have hdescent : baseEnd_5066650 < baseStart_5066650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066659 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 9]
def baseStart_5066659 : Nat := 118140960795 + 5066659 * 2 ^ 59
def prefixEnd_5066659 : Nat := 4983230072969 + 3 ^ 40 * 5066659 * 2
def baseEnd_5066659 : Nat := 867210459809532469020455

theorem tailTrace_5066659 : CollatzResearch.WordTrace tailWord_5066659 prefixEnd_5066659 867210459809532469020455 := by
  unfold tailWord_5066659
  simp only [CollatzResearch.WordTrace]
  refine ⟨184796235351367234310947031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123197490234244822873964687 184796235351367234310947031)
  ·
    refine ⟨277194353027050851466420547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184796235351367234310947031 277194353027050851466420547)
    ·
      refine ⟨415791529540576277199630821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277194353027050851466420547 415791529540576277199630821)
      ·
        refine ⟨77960911788858051974930779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 415791529540576277199630821 77960911788858051974930779)
        ·
          refine ⟨116941367683287077962396169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77960911788858051974930779 116941367683287077962396169)
          ·
            refine ⟨87706025762465308471797127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116941367683287077962396169 87706025762465308471797127)
            ·
              refine ⟨131559038643697962707695691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87706025762465308471797127 131559038643697962707695691)
              ·
                refine ⟨197338557965546944061543537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131559038643697962707695691 197338557965546944061543537)
                ·
                  refine ⟨148003918474160208046157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197338557965546944061543537 148003918474160208046157653)
                  ·
                    refine ⟨867210459809532469020455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 148003918474160208046157653 867210459809532469020455)
                    ·
                      rfl

theorem cell23_5066659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_5066659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066659 prefixEnd_5066659 := by exact prefixLift 5066659
  have htrace : WordTrace (prefixWord ++ tailWord_5066659) baseStart_5066659 baseEnd_5066659 := by
    simpa [prefixWord, tailWord_5066659, baseEnd_5066659] using wordTrace_append hprefix tailTrace_5066659
  have hstable : (prefixWord ++ tailWord_5066659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066659).length < 2 ^ (prefixWord ++ tailWord_5066659).sum := by decide
  have hdescent : baseEnd_5066659 < baseStart_5066659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066663 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 6]
def baseStart_5066663 : Nat := 118140960795 + 5066663 * 2 ^ 59
def prefixEnd_5066663 : Nat := 4983230072969 + 3 ^ 40 * 5066663 * 2
def baseEnd_5066663 : Nat := 289070381483468376823483

theorem tailTrace_5066663 : CollatzResearch.WordTrace tailWord_5066663 prefixEnd_5066663 289070381483468376823483 := by
  unfold tailWord_5066663
  simp only [CollatzResearch.WordTrace]
  refine ⟨184796381243352742994092643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123197587495568495329395095 184796381243352742994092643)
  ·
    refine ⟨277194571865029114491138965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184796381243352742994092643 277194571865029114491138965)
    ·
      refine ⟨12993495556173239741772139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 277194571865029114491138965 12993495556173239741772139)
      ·
        refine ⟨19490243334259859612658209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12993495556173239741772139 19490243334259859612658209)
        ·
          refine ⟨14617682500694894709493657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19490243334259859612658209 14617682500694894709493657)
          ·
            refine ⟨10963261875521171032120243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14617682500694894709493657 10963261875521171032120243)
            ·
              refine ⟨16444892813281756548180365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10963261875521171032120243 16444892813281756548180365)
              ·
                refine ⟨6166834804980658705567637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16444892813281756548180365 6166834804980658705567637)
                ·
                  refine ⟨289070381483468376823483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6166834804980658705567637 289070381483468376823483)
                  ·
                    rfl

theorem cell23_5066663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 6].length) (baseStart_5066663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066663 prefixEnd_5066663 := by exact prefixLift 5066663
  have htrace : WordTrace (prefixWord ++ tailWord_5066663) baseStart_5066663 baseEnd_5066663 := by
    simpa [prefixWord, tailWord_5066663, baseEnd_5066663] using wordTrace_append hprefix tailTrace_5066663
  have hstable : (prefixWord ++ tailWord_5066663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066663).length < 2 ^ (prefixWord ++ tailWord_5066663).sum := by decide
  have hdescent : baseEnd_5066663 < baseStart_5066663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066683 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 2, 3, 2]
def baseStart_5066683 : Nat := 118140960795 + 5066683 * 2 ^ 59
def prefixEnd_5066683 : Nat := 4983230072969 + 3 ^ 40 * 5066683 * 2
def baseEnd_5066683 : Nat := 2601643702964305313161255

theorem tailTrace_5066683 : CollatzResearch.WordTrace tailWord_5066683 prefixEnd_5066683 2601643702964305313161255 := by
  unfold tailWord_5066683
  simp only [CollatzResearch.WordTrace]
  refine ⟨184797110703280286409820703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123198073802186857606547135 184797110703280286409820703)
  ·
    refine ⟨277195666054920429614731055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184797110703280286409820703 277195666054920429614731055)
    ·
      refine ⟨415793499082380644422096583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277195666054920429614731055 415793499082380644422096583)
      ·
        refine ⟨623690248623570966633144875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415793499082380644422096583 623690248623570966633144875)
        ·
          refine ⟨935535372935356449949717313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623690248623570966633144875 935535372935356449949717313)
          ·
            refine ⟨701651529701517337462287985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935535372935356449949717313 701651529701517337462287985)
            ·
              refine ⟨526238647276138003096715989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701651529701517337462287985 526238647276138003096715989)
              ·
                refine ⟨12333718295534484447579281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 526238647276138003096715989 12333718295534484447579281)
                ·
                  refine ⟨9250288721650863335684461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12333718295534484447579281 9250288721650863335684461)
                  ·
                    refine ⟨3468858270619073750881673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9250288721650863335684461 3468858270619073750881673)
                    ·
                      refine ⟨2601643702964305313161255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468858270619073750881673 2601643702964305313161255)
                      ·
                        rfl

theorem cell23_5066683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3, 2].length) (baseStart_5066683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066683 prefixEnd_5066683 := by exact prefixLift 5066683
  have htrace : WordTrace (prefixWord ++ tailWord_5066683) baseStart_5066683 baseEnd_5066683 := by
    simpa [prefixWord, tailWord_5066683, baseEnd_5066683] using wordTrace_append hprefix tailTrace_5066683
  have hstable : (prefixWord ++ tailWord_5066683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066683).length < 2 ^ (prefixWord ++ tailWord_5066683).sum := by decide
  have hdescent : baseEnd_5066683 < baseStart_5066683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066700 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5066700 : Nat := 118140960795 + 5066700 * 2 ^ 59
def prefixEnd_5066700 : Nat := 4983230072969 + 3 ^ 40 * 5066700 * 2
def baseEnd_5066700 : Nat := 2601652432135431746648677

theorem tailTrace_5066700 : CollatzResearch.WordTrace tailWord_5066700 prefixEnd_5066700 2601652432135431746648677 := by
  unfold tailWord_5066700
  simp only [CollatzResearch.WordTrace]
  refine ⟨92398865372109349156594777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123198487162812465542126369 92398865372109349156594777)
  ·
    refine ⟨69299149029082011867446083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92398865372109349156594777 69299149029082011867446083)
    ·
      refine ⟨103948723543623017801169125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69299149029082011867446083 103948723543623017801169125)
      ·
        refine ⟨19490385664429315837719211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103948723543623017801169125 19490385664429315837719211)
        ·
          refine ⟨29235578496643973756578817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19490385664429315837719211 29235578496643973756578817)
          ·
            refine ⟨21926683872482980317434113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29235578496643973756578817 21926683872482980317434113)
            ·
              refine ⟨16445012904362235238075585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21926683872482980317434113 16445012904362235238075585)
              ·
                refine ⟨12333759678271676428556689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16445012904362235238075585 12333759678271676428556689)
                ·
                  refine ⟨9250319758703757321417517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12333759678271676428556689 9250319758703757321417517)
                  ·
                    refine ⟨3468869909513908995531569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9250319758703757321417517 3468869909513908995531569)
                    ·
                      refine ⟨2601652432135431746648677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468869909513908995531569 2601652432135431746648677)
                      ·
                        rfl

theorem cell23_5066700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5066700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066700 prefixEnd_5066700 := by exact prefixLift 5066700
  have htrace : WordTrace (prefixWord ++ tailWord_5066700) baseStart_5066700 baseEnd_5066700 := by
    simpa [prefixWord, tailWord_5066700, baseEnd_5066700] using wordTrace_append hprefix tailTrace_5066700
  have hstable : (prefixWord ++ tailWord_5066700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066700).length < 2 ^ (prefixWord ++ tailWord_5066700).sum := by decide
  have hdescent : baseEnd_5066700 < baseStart_5066700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066723 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 1, 6]
def baseStart_5066723 : Nat := 118140960795 + 5066723 * 2 ^ 59
def prefixEnd_5066723 : Nat := 4983230072969 + 3 ^ 40 * 5066723 * 2
def baseEnd_5066723 : Nat := 867221414063495052220357

theorem tailTrace_5066723 : CollatzResearch.WordTrace tailWord_5066723 prefixEnd_5066723 867221414063495052220357 := by
  unfold tailWord_5066723
  simp only [CollatzResearch.WordTrace]
  refine ⟨184798569623135373241276823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123199046415423582160851215 184798569623135373241276823)
  ·
    refine ⟨277197854434703059861915235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184798569623135373241276823 277197854434703059861915235)
    ·
      refine ⟨415796781652054589792872853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277197854434703059861915235 415796781652054589792872853)
      ·
        refine ⟨19490474139940058896540915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 415796781652054589792872853 19490474139940058896540915)
        ·
          refine ⟨29235711209910088344811373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19490474139940058896540915 29235711209910088344811373)
          ·
            refine ⟨10963391703716283129304265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29235711209910088344811373 10963391703716283129304265)
            ·
              refine ⟨8222543777787212346978199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10963391703716283129304265 8222543777787212346978199)
              ·
                refine ⟨12333815666680818520467299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222543777787212346978199 12333815666680818520467299)
                ·
                  refine ⟨18500723500021227780700949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12333815666680818520467299 18500723500021227780700949)
                  ·
                    refine ⟨867221414063495052220357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18500723500021227780700949 867221414063495052220357)
                    ·
                      rfl

theorem cell23_5066723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 6].length) (baseStart_5066723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066723 prefixEnd_5066723 := by exact prefixLift 5066723
  have htrace : WordTrace (prefixWord ++ tailWord_5066723) baseStart_5066723 baseEnd_5066723 := by
    simpa [prefixWord, tailWord_5066723, baseEnd_5066723] using wordTrace_append hprefix tailTrace_5066723
  have hstable : (prefixWord ++ tailWord_5066723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066723).length < 2 ^ (prefixWord ++ tailWord_5066723).sum := by decide
  have hdescent : baseEnd_5066723 < baseStart_5066723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066747 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 1, 2, 2]
def baseStart_5066747 : Nat := 118140960795 + 5066747 * 2 ^ 59
def prefixEnd_5066747 : Nat := 4983230072969 + 3 ^ 40 * 5066747 * 2
def baseEnd_5066747 : Nat := 2601676565726193062760961

theorem tailTrace_5066747 : CollatzResearch.WordTrace tailWord_5066747 prefixEnd_5066747 2601676565726193062760961 := by
  unfold tailWord_5066747
  simp only [CollatzResearch.WordTrace]
  refine ⟨184799444975048425340150495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123199629983365616893433663 184799444975048425340150495)
  ·
    refine ⟨277199167462572638010225743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184799444975048425340150495 277199167462572638010225743)
    ·
      refine ⟨415798751193858957015338615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277199167462572638010225743 415798751193858957015338615)
      ·
        refine ⟨623698126790788435523007923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415798751193858957015338615 623698126790788435523007923)
        ·
          refine ⟨935547190186182653284511885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623698126790788435523007923 935547190186182653284511885)
          ·
            refine ⟨350830196319818494981691957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 935547190186182653284511885 350830196319818494981691957)
            ·
              refine ⟨32890330904982983904533621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350830196319818494981691957 32890330904982983904533621)
              ·
                refine ⟨3083468522342154741050027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32890330904982983904533621 3083468522342154741050027)
                ·
                  refine ⟨4625202783513232111575041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083468522342154741050027 4625202783513232111575041)
                  ·
                    refine ⟨3468902087634924083681281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625202783513232111575041 3468902087634924083681281)
                    ·
                      refine ⟨2601676565726193062760961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3468902087634924083681281 2601676565726193062760961)
                      ·
                        rfl

theorem cell23_5066747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 2, 2].length) (baseStart_5066747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066747 prefixEnd_5066747 := by exact prefixLift 5066747
  have htrace : WordTrace (prefixWord ++ tailWord_5066747) baseStart_5066747 baseEnd_5066747 := by
    simpa [prefixWord, tailWord_5066747, baseEnd_5066747] using wordTrace_append hprefix tailTrace_5066747
  have hstable : (prefixWord ++ tailWord_5066747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066747).length < 2 ^ (prefixWord ++ tailWord_5066747).sum := by decide
  have hdescent : baseEnd_5066747 < baseStart_5066747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066758 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5066758 : Nat := 118140960795 + 5066758 * 2 ^ 59
def prefixEnd_5066758 : Nat := 4983230072969 + 3 ^ 40 * 5066758 * 2
def baseEnd_5066758 : Nat := 2601682214013392519723411

theorem tailTrace_5066758 : CollatzResearch.WordTrace tailWord_5066758 prefixEnd_5066758 2601682214013392519723411 := by
  unfold tailWord_5066758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774995193062767944337529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123199897452005716145867285 5774995193062767944337529)
  ·
    refine ⟨4331246394797075958253147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5774995193062767944337529 4331246394797075958253147)
    ·
      refine ⟨6496869592195613937379721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4331246394797075958253147 6496869592195613937379721)
      ·
        refine ⟨4872652194146710453034791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6496869592195613937379721 4872652194146710453034791)
        ·
          refine ⟨7308978291220065679552187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872652194146710453034791 7308978291220065679552187)
          ·
            refine ⟨10963467436830098519328281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308978291220065679552187 10963467436830098519328281)
            ·
              refine ⟨8222600577622573889496211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10963467436830098519328281 8222600577622573889496211)
              ·
                refine ⟨12333900866433860834244317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222600577622573889496211 12333900866433860834244317)
                ·
                  refine ⟨4625212824912697812841619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12333900866433860834244317 4625212824912697812841619)
                  ·
                    refine ⟨6937819237369046719262429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4625212824912697812841619 6937819237369046719262429)
                    ·
                      refine ⟨2601682214013392519723411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937819237369046719262429 2601682214013392519723411)
                      ·
                        rfl

theorem cell23_5066758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5066758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066758 prefixEnd_5066758 := by exact prefixLift 5066758
  have htrace : WordTrace (prefixWord ++ tailWord_5066758) baseStart_5066758 baseEnd_5066758 := by
    simpa [prefixWord, tailWord_5066758, baseEnd_5066758] using wordTrace_append hprefix tailTrace_5066758
  have hstable : (prefixWord ++ tailWord_5066758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066758).length < 2 ^ (prefixWord ++ tailWord_5066758).sum := by decide
  have hdescent : baseEnd_5066758 < baseStart_5066758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066780 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_5066780 : Nat := 118140960795 + 5066780 * 2 ^ 59
def prefixEnd_5066780 : Nat := 4983230072969 + 3 ^ 40 * 5066780 * 2
def baseEnd_5066780 : Nat := 2601693510587791433648309

theorem tailTrace_5066780 : CollatzResearch.WordTrace tailWord_5066780 prefixEnd_5066780 2601693510587791433648309 := by
  unfold tailWord_5066780
  simp only [CollatzResearch.WordTrace]
  refine ⟨92400324291964435988050897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123200432389285914650734529 92400324291964435988050897)
  ·
    refine ⟨69300243218973326991038173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92400324291964435988050897 69300243218973326991038173)
    ·
      refine ⟨25987591207114997621639315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69300243218973326991038173 25987591207114997621639315)
      ·
        refine ⟨38981386810672496432458973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25987591207114997621639315 38981386810672496432458973)
        ·
          refine ⟨14618020054002186162172115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38981386810672496432458973 14618020054002186162172115)
          ·
            refine ⟨21927030081003279243258173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14618020054002186162172115 21927030081003279243258173)
            ·
              refine ⟨8222636280376229716221815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21927030081003279243258173 8222636280376229716221815)
              ·
                refine ⟨12333954420564344574332723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222636280376229716221815 12333954420564344574332723)
                ·
                  refine ⟨18500931630846516861499085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12333954420564344574332723 18500931630846516861499085)
                  ·
                    refine ⟨6937849361567443823062157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18500931630846516861499085 6937849361567443823062157)
                    ·
                      refine ⟨2601693510587791433648309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937849361567443823062157 2601693510587791433648309)
                      ·
                        rfl

theorem cell23_5066780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_5066780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066780 prefixEnd_5066780 := by exact prefixLift 5066780
  have htrace : WordTrace (prefixWord ++ tailWord_5066780) baseStart_5066780 baseEnd_5066780 := by
    simpa [prefixWord, tailWord_5066780, baseEnd_5066780] using wordTrace_append hprefix tailTrace_5066780
  have hstable : (prefixWord ++ tailWord_5066780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066780).length < 2 ^ (prefixWord ++ tailWord_5066780).sum := by decide
  have hdescent : baseEnd_5066780 < baseStart_5066780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066796 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_5066796 : Nat := 118140960795 + 5066796 * 2 ^ 59
def prefixEnd_5066796 : Nat := 4983230072969 + 3 ^ 40 * 5066796 * 2
def baseEnd_5066796 : Nat := 867233908759421123682745

theorem tailTrace_5066796 : CollatzResearch.WordTrace tailWord_5066796 prefixEnd_5066796 867233908759421123682745 := by
  unfold tailWord_5066796
  simp only [CollatzResearch.WordTrace]
  refine ⟨92400616075935453354342121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123200821434580604472456161 92400616075935453354342121)
  ·
    refine ⟨69300462056951590015756591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92400616075935453354342121 69300462056951590015756591)
    ·
      refine ⟨103950693085427385023634887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69300462056951590015756591 103950693085427385023634887)
      ·
        refine ⟨155926039628141077535452331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103950693085427385023634887 155926039628141077535452331)
        ·
          refine ⟨233889059442211616303178497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155926039628141077535452331 233889059442211616303178497)
          ·
            refine ⟨175416794581658712227383873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233889059442211616303178497 175416794581658712227383873)
            ·
              refine ⟨131562595936244034170537905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175416794581658712227383873 131562595936244034170537905)
              ·
                refine ⟨98671946952183025627903429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131562595936244034170537905 98671946952183025627903429)
                ·
                  refine ⟨18500990053534317305231893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98671946952183025627903429 18500990053534317305231893)
                  ·
                    refine ⟨867233908759421123682745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18500990053534317305231893 867233908759421123682745)
                    ·
                      rfl

theorem cell23_5066796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_5066796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066796 prefixEnd_5066796 := by exact prefixLift 5066796
  have htrace : WordTrace (prefixWord ++ tailWord_5066796) baseStart_5066796 baseEnd_5066796 := by
    simpa [prefixWord, tailWord_5066796, baseEnd_5066796] using wordTrace_append hprefix tailTrace_5066796
  have hstable : (prefixWord ++ tailWord_5066796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066796).length < 2 ^ (prefixWord ++ tailWord_5066796).sum := by decide
  have hdescent : baseEnd_5066796 < baseStart_5066796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066823 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_5066823 : Nat := 118140960795 + 5066823 * 2 ^ 59
def prefixEnd_5066823 : Nat := 4983230072969 + 3 ^ 40 * 5066823 * 2
def baseEnd_5066823 : Nat := 2601715590255934765410611

theorem tailTrace_5066823 : CollatzResearch.WordTrace tailWord_5066823 prefixEnd_5066823 2601715590255934765410611 := by
  unfold tailWord_5066823
  simp only [CollatzResearch.WordTrace]
  refine ⟨184802216922773090319917123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123201477948515393546611415 184802216922773090319917123)
  ·
    refine ⟨277203325384159635479875685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184802216922773090319917123 277203325384159635479875685)
    ·
      refine ⟨51975623509529931652476691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277203325384159635479875685 51975623509529931652476691)
      ·
        refine ⟨77963435264294897478715037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51975623509529931652476691 77963435264294897478715037)
        ·
          refine ⟨29236288224110586554518139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77963435264294897478715037 29236288224110586554518139)
          ·
            refine ⟨43854432336165879831777209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29236288224110586554518139 43854432336165879831777209)
            ·
              refine ⟨32890824252124409873832907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43854432336165879831777209 32890824252124409873832907)
              ·
                refine ⟨49336236378186614810749361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32890824252124409873832907 49336236378186614810749361)
                ·
                  refine ⟨37002177283639961108062021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49336236378186614810749361 37002177283639961108062021)
                  ·
                    refine ⟨6937908240682492707761629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37002177283639961108062021 6937908240682492707761629)
                    ·
                      refine ⟨2601715590255934765410611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6937908240682492707761629 2601715590255934765410611)
                      ·
                        rfl

theorem cell23_5066823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_5066823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066823 prefixEnd_5066823 := by exact prefixLift 5066823
  have htrace : WordTrace (prefixWord ++ tailWord_5066823) baseStart_5066823 baseEnd_5066823 := by
    simpa [prefixWord, tailWord_5066823, baseEnd_5066823] using wordTrace_append hprefix tailTrace_5066823
  have hstable : (prefixWord ++ tailWord_5066823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066823).length < 2 ^ (prefixWord ++ tailWord_5066823).sum := by decide
  have hdescent : baseEnd_5066823 < baseStart_5066823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066877 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 5]
def baseStart_5066877 : Nat := 118140960795 + 5066877 * 2 ^ 59
def prefixEnd_5066877 : Nat := 4983230072969 + 3 ^ 40 * 5066877 * 2
def baseEnd_5066877 : Nat := 289082590912364172681707

theorem tailTrace_5066877 : CollatzResearch.WordTrace tailWord_5066877 prefixEnd_5066877 289082590912364172681707 := by
  unfold tailWord_5066877
  simp only [CollatzResearch.WordTrace]
  refine ⟨184804186464577457542382885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123202790976384971694921923 184804186464577457542382885)
  ·
    refine ⟨34650784962108273289196791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184804186464577457542382885 34650784962108273289196791)
    ·
      refine ⟨51976177443162409933795187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34650784962108273289196791 51976177443162409933795187)
      ·
        refine ⟨77964266164743614900692781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51976177443162409933795187 77964266164743614900692781)
        ·
          refine ⟨29236599811778855587759793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77964266164743614900692781 29236599811778855587759793)
          ·
            refine ⟨21927449858834141690819845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29236599811778855587759793 21927449858834141690819845)
            ·
              refine ⟨4111396848531401567028721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21927449858834141690819845 4111396848531401567028721)
              ·
                refine ⟨3083547636398551175271541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4111396848531401567028721 3083547636398551175271541)
                ·
                  refine ⟨289082590912364172681707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083547636398551175271541 289082590912364172681707)
                  ·
                    rfl

theorem cell23_5066877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_5066877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066877 prefixEnd_5066877 := by exact prefixLift 5066877
  have htrace : WordTrace (prefixWord ++ tailWord_5066877) baseStart_5066877 baseEnd_5066877 := by
    simpa [prefixWord, tailWord_5066877, baseEnd_5066877] using wordTrace_append hprefix tailTrace_5066877
  have hstable : (prefixWord ++ tailWord_5066877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066877).length < 2 ^ (prefixWord ++ tailWord_5066877).sum := by decide
  have hdescent : baseEnd_5066877 < baseStart_5066877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066883 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_5066883 : Nat := 118140960795 + 5066883 * 2 ^ 59
def prefixEnd_5066883 : Nat := 4983230072969 + 3 ^ 40 * 5066883 * 2
def baseEnd_5066883 : Nat := 2601746399095204530660335

theorem tailTrace_5066883 : CollatzResearch.WordTrace tailWord_5066883 prefixEnd_5066883 2601746399095204530660335 := by
  unfold tailWord_5066883
  simp only [CollatzResearch.WordTrace]
  refine ⟨184804405302555720567101303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123202936868370480378067535 184804405302555720567101303)
  ·
    refine ⟨277206607953833580850651955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184804405302555720567101303 277206607953833580850651955)
    ·
      refine ⟨415809911930750371275977933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277206607953833580850651955 415809911930750371275977933)
      ·
        refine ⟨155928716974031389228491725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415809911930750371275977933 155928716974031389228491725)
        ·
          refine ⟨58473268865261770960684397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155928716974031389228491725 58473268865261770960684397)
          ·
            refine ⟨21927475824473164110256649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58473268865261770960684397 21927475824473164110256649)
            ·
              refine ⟨16445606868354873082692487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21927475824473164110256649 16445606868354873082692487)
              ·
                refine ⟨24668410302532309624038731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16445606868354873082692487 24668410302532309624038731)
                ·
                  refine ⟨37002615453798464436058097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24668410302532309624038731 37002615453798464436058097)
                  ·
                    refine ⟨27751961590348848327043573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37002615453798464436058097 27751961590348848327043573)
                    ·
                      refine ⟨2601746399095204530660335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27751961590348848327043573 2601746399095204530660335)
                      ·
                        rfl

theorem cell23_5066883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_5066883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066883 prefixEnd_5066883 := by exact prefixLift 5066883
  have htrace : WordTrace (prefixWord ++ tailWord_5066883) baseStart_5066883 baseEnd_5066883 := by
    simpa [prefixWord, tailWord_5066883, baseEnd_5066883] using wordTrace_append hprefix tailTrace_5066883
  have hstable : (prefixWord ++ tailWord_5066883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066883).length < 2 ^ (prefixWord ++ tailWord_5066883).sum := by decide
  have hdescent : baseEnd_5066883 < baseStart_5066883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066930 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_5066930 : Nat := 118140960795 + 5066930 * 2 ^ 59
def prefixEnd_5066930 : Nat := 4983230072969 + 3 ^ 40 * 5066930 * 2
def baseEnd_5066930 : Nat := 2601770532685965846772619

theorem tailTrace_5066930 : CollatzResearch.WordTrace tailWord_5066930 prefixEnd_5066930 2601770532685965846772619 := by
  unfold tailWord_5066930
  simp only [CollatzResearch.WordTrace]
  refine ⟨46201529883346361898515561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123204079688923631729374829 46201529883346361898515561)
  ·
    refine ⟨34651147412509771423886671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46201529883346361898515561 34651147412509771423886671)
    ·
      refine ⟨51976721118764657135830007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34651147412509771423886671 51976721118764657135830007)
      ·
        refine ⟨77965081678146985703745011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51976721118764657135830007 77965081678146985703745011)
        ·
          refine ⟨116947622517220478555617517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77965081678146985703745011 116947622517220478555617517)
          ·
            refine ⟨43855358443957679458356569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116947622517220478555617517 43855358443957679458356569)
            ·
              refine ⟨32891518832968259593767427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43855358443957679458356569 32891518832968259593767427)
              ·
                refine ⟨49337278249452389390651141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32891518832968259593767427 49337278249452389390651141)
                ·
                  refine ⟨9250739671772323010747089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49337278249452389390651141 9250739671772323010747089)
                  ·
                    refine ⟨6938054753829242258060317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9250739671772323010747089 6938054753829242258060317)
                    ·
                      refine ⟨2601770532685965846772619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6938054753829242258060317 2601770532685965846772619)
                      ·
                        rfl

theorem cell23_5066930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_5066930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066930 prefixEnd_5066930 := by exact prefixLift 5066930
  have htrace : WordTrace (prefixWord ++ tailWord_5066930) baseStart_5066930 baseEnd_5066930 := by
    simpa [prefixWord, tailWord_5066930, baseEnd_5066930] using wordTrace_append hprefix tailTrace_5066930
  have hstable : (prefixWord ++ tailWord_5066930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066930).length < 2 ^ (prefixWord ++ tailWord_5066930).sum := by decide
  have hdescent : baseEnd_5066930 < baseStart_5066930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066937 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 1, 4]
def baseStart_5066937 : Nat := 118140960795 + 5066937 * 2 ^ 59
def prefixEnd_5066937 : Nat := 4983230072969 + 3 ^ 40 * 5066937 * 2
def baseEnd_5066937 : Nat := 867258042350182439795029

theorem tailTrace_5066937 : CollatzResearch.WordTrace tailWord_5066937 prefixEnd_5066937 867258042350182439795029 := by
  unfold tailWord_5066937
  simp only [CollatzResearch.WordTrace]
  refine ⟨184806374844360087789567065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123204249896240058526378043 184806374844360087789567065)
  ·
    refine ⟨138604781133270065842175299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184806374844360087789567065 138604781133270065842175299)
    ·
      refine ⟨207907171699905098763262949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138604781133270065842175299 207907171699905098763262949)
      ·
        refine ⟨38982594693732206018111803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207907171699905098763262949 38982594693732206018111803)
        ·
          refine ⟨58473892040598309027167705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38982594693732206018111803 58473892040598309027167705)
          ·
            refine ⟨43855419030448731770375779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58473892040598309027167705 43855419030448731770375779)
            ·
              refine ⟨65783128545673097655563669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43855419030448731770375779 65783128545673097655563669)
              ·
                refine ⟨3083584150578426452604547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65783128545673097655563669 3083584150578426452604547)
                ·
                  refine ⟨4625376225867639678906821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083584150578426452604547 4625376225867639678906821)
                  ·
                    refine ⟨867258042350182439795029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625376225867639678906821 867258042350182439795029)
                    ·
                      rfl

theorem cell23_5066937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 4].length) (baseStart_5066937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066937 prefixEnd_5066937 := by exact prefixLift 5066937
  have htrace : WordTrace (prefixWord ++ tailWord_5066937) baseStart_5066937 baseEnd_5066937 := by
    simpa [prefixWord, tailWord_5066937, baseEnd_5066937] using wordTrace_append hprefix tailTrace_5066937
  have hstable : (prefixWord ++ tailWord_5066937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066937).length < 2 ^ (prefixWord ++ tailWord_5066937).sum := by decide
  have hdescent : baseEnd_5066937 < baseStart_5066937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066987 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 2, 3, 2]
def baseStart_5066987 : Nat := 118140960795 + 5066987 * 2 ^ 59
def prefixEnd_5066987 : Nat := 4983230072969 + 3 ^ 40 * 5066987 * 2
def baseEnd_5066987 : Nat := 2601799801083272123759857

theorem tailTrace_5066987 : CollatzResearch.WordTrace tailWord_5066987 prefixEnd_5066987 2601799801083272123759857 := by
  unfold tailWord_5066987
  simp only [CollatzResearch.WordTrace]
  refine ⟨184808198494178946328887215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123205465662785964219258143 184808198494178946328887215)
  ·
    refine ⟨277212297741268419493330823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184808198494178946328887215 277212297741268419493330823)
    ·
      refine ⟨415818446611902629239996235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277212297741268419493330823 415818446611902629239996235)
      ·
        refine ⟨623727669917853943859994353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415818446611902629239996235 623727669917853943859994353)
        ·
          refine ⟨467795752438390457894995765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623727669917853943859994353 467795752438390457894995765)
          ·
            refine ⟨43855851791099105427655853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 467795752438390457894995765 43855851791099105427655853)
            ·
              refine ⟨16445944421662164535370945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43855851791099105427655853 16445944421662164535370945)
              ·
                refine ⟨12334458316246623401528209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16445944421662164535370945 12334458316246623401528209)
                ·
                  refine ⟨9250843737184967551146157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12334458316246623401528209 9250843737184967551146157)
                  ·
                    refine ⟨3469066401444362831679809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9250843737184967551146157 3469066401444362831679809)
                    ·
                      refine ⟨2601799801083272123759857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469066401444362831679809 2601799801083272123759857)
                      ·
                        rfl

theorem cell23_5066987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3, 2].length) (baseStart_5066987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066987 prefixEnd_5066987 := by exact prefixLift 5066987
  have htrace : WordTrace (prefixWord ++ tailWord_5066987) baseStart_5066987 baseEnd_5066987 := by
    simpa [prefixWord, tailWord_5066987, baseEnd_5066987] using wordTrace_append hprefix tailTrace_5066987
  have hstable : (prefixWord ++ tailWord_5066987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066987).length < 2 ^ (prefixWord ++ tailWord_5066987).sum := by decide
  have hdescent : baseEnd_5066987 < baseStart_5066987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5066994 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_5066994 : Nat := 118140960795 + 5066994 * 2 ^ 59
def prefixEnd_5066994 : Nat := 4983230072969 + 3 ^ 40 * 5066994 * 2
def baseEnd_5066994 : Nat := 2601803395447853596372325

theorem tailTrace_5066994 : CollatzResearch.WordTrace tailWord_5066994 prefixEnd_5066994 2601803395447853596372325 := by
  unfold tailWord_5066994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46202113451288396631098009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123205635870102391016261357 46202113451288396631098009)
  ·
    refine ⟨34651585088466297473323507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46202113451288396631098009 34651585088466297473323507)
    ·
      refine ⟨51977377632699446209985261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34651585088466297473323507 51977377632699446209985261)
      ·
        refine ⟨19491516612262292328744473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51977377632699446209985261 19491516612262292328744473)
        ·
          refine ⟨14618637459196719246558355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19491516612262292328744473 14618637459196719246558355)
          ·
            refine ⟨21927956188795078869837533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14618637459196719246558355 21927956188795078869837533)
            ·
              refine ⟨8222983570798154576189075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21927956188795078869837533 8222983570798154576189075)
              ·
                refine ⟨12334475356197231864283613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222983570798154576189075 12334475356197231864283613)
                ·
                  refine ⟨4625428258573961949106355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12334475356197231864283613 4625428258573961949106355)
                  ·
                    refine ⟨6938142387860942923659533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4625428258573961949106355 6938142387860942923659533)
                    ·
                      refine ⟨2601803395447853596372325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6938142387860942923659533 2601803395447853596372325)
                      ·
                        rfl

theorem cell23_5066994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_5066994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5066994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5066994 prefixEnd_5066994 := by exact prefixLift 5066994
  have htrace : WordTrace (prefixWord ++ tailWord_5066994) baseStart_5066994 baseEnd_5066994 := by
    simpa [prefixWord, tailWord_5066994, baseEnd_5066994] using wordTrace_append hprefix tailTrace_5066994
  have hstable : (prefixWord ++ tailWord_5066994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5066994).length < 2 ^ (prefixWord ++ tailWord_5066994).sum := by decide
  have hdescent : baseEnd_5066994 < baseStart_5066994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5066994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067017 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_5067017 : Nat := 118140960795 + 5067017 * 2 ^ 59
def prefixEnd_5067017 : Nat := 4983230072969 + 3 ^ 40 * 5067017 * 2
def baseEnd_5067017 : Nat := 2601815205502907006384719

theorem tailTrace_5067017 : CollatzResearch.WordTrace tailWord_5067017 prefixEnd_5067017 2601815205502907006384719 := by
  unfold tailWord_5067017
  simp only [CollatzResearch.WordTrace]
  refine ⟨184809292684070261452479305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123206195122713507634986203 184809292684070261452479305)
  ·
    refine ⟨138606969513052696089359479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184809292684070261452479305 138606969513052696089359479)
    ·
      refine ⟨207910454269579044134039219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138606969513052696089359479 207910454269579044134039219)
      ·
        refine ⟨311865681404368566201058829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207910454269579044134039219 311865681404368566201058829)
        ·
          refine ⟨116949630526638212325397061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311865681404368566201058829 116949630526638212325397061)
          ·
            refine ⟨21928055723744664811011949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116949630526638212325397061 21928055723744664811011949)
            ·
              refine ⟨8223020896404249304129481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21928055723744664811011949 8223020896404249304129481)
              ·
                refine ⟨6167265672303186978097111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8223020896404249304129481 6167265672303186978097111)
                ·
                  refine ⟨9250898508454780467145667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6167265672303186978097111 9250898508454780467145667)
                  ·
                    refine ⟨13876347762682170700718501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9250898508454780467145667 13876347762682170700718501)
                    ·
                      refine ⟨2601815205502907006384719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13876347762682170700718501 2601815205502907006384719)
                      ·
                        rfl

theorem cell23_5067017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_5067017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067017 prefixEnd_5067017 := by exact prefixLift 5067017
  have htrace : WordTrace (prefixWord ++ tailWord_5067017) baseStart_5067017 baseEnd_5067017 := by
    simpa [prefixWord, tailWord_5067017, baseEnd_5067017] using wordTrace_append hprefix tailTrace_5067017
  have hstable : (prefixWord ++ tailWord_5067017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067017).length < 2 ^ (prefixWord ++ tailWord_5067017).sum := by decide
  have hdescent : baseEnd_5067017 < baseStart_5067017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067044 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_5067044 : Nat := 118140960795 + 5067044 * 2 ^ 59
def prefixEnd_5067044 : Nat := 4983230072969 + 3 ^ 40 * 5067044 * 2
def baseEnd_5067044 : Nat := 867276356493526133582365

theorem tailTrace_5067044 : CollatzResearch.WordTrace tailWord_5067044 prefixEnd_5067044 867276356493526133582365 := by
  unfold tailWord_5067044
  simp only [CollatzResearch.WordTrace]
  refine ⟨92405138727486222531856093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123206851636648296709141457 92405138727486222531856093)
  ·
    refine ⟨34651927022807333449446035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92405138727486222531856093 34651927022807333449446035)
    ·
      refine ⟨51977890534211000174169053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34651927022807333449446035 51977890534211000174169053)
      ·
        refine ⟨19491708950329125065313395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51977890534211000174169053 19491708950329125065313395)
        ·
          refine ⟨29237563425493687597970093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19491708950329125065313395 29237563425493687597970093)
          ·
            refine ⟨10964086284560132849238785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29237563425493687597970093 10964086284560132849238785)
            ·
              refine ⟨8223064713420099636929089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10964086284560132849238785 8223064713420099636929089)
              ·
                refine ⟨6167298535065074727696817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8223064713420099636929089 6167298535065074727696817)
                ·
                  refine ⟨4625473901298806045772613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6167298535065074727696817 4625473901298806045772613)
                  ·
                    refine ⟨867276356493526133582365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625473901298806045772613 867276356493526133582365)
                    ·
                      rfl

theorem cell23_5067044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_5067044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067044 prefixEnd_5067044 := by exact prefixLift 5067044
  have htrace : WordTrace (prefixWord ++ tailWord_5067044) baseStart_5067044 baseEnd_5067044 := by
    simpa [prefixWord, tailWord_5067044, baseEnd_5067044] using wordTrace_append hprefix tailTrace_5067044
  have hstable : (prefixWord ++ tailWord_5067044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067044).length < 2 ^ (prefixWord ++ tailWord_5067044).sum := by decide
  have hdescent : baseEnd_5067044 < baseStart_5067044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067045 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 1, 1, 3]
def baseStart_5067045 : Nat := 118140960795 + 5067045 * 2 ^ 59
def prefixEnd_5067045 : Nat := 4983230072969 + 3 ^ 40 * 5067045 * 2
def baseEnd_5067045 : Nat := 2601829582961232896834591

theorem tailTrace_5067045 : CollatzResearch.WordTrace tailWord_5067045 prefixEnd_5067045 2601829582961232896834591 := by
  unfold tailWord_5067045
  simp only [CollatzResearch.WordTrace]
  refine ⟨184810313927968822234498589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123206875951979214822999059 184810313927968822234498589)
  ·
    refine ⟨69303867722988308337936971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184810313927968822234498589 69303867722988308337936971)
    ·
      refine ⟨103955801584482462506905457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69303867722988308337936971 103955801584482462506905457)
      ·
        refine ⟨77966851188361846880179093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103955801584482462506905457 77966851188361846880179093)
        ·
          refine ⟨3654696149454461572508395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77966851188361846880179093 3654696149454461572508395)
          ·
            refine ⟨5482044224181692358762593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654696149454461572508395 5482044224181692358762593)
            ·
              refine ⟨4111533168136269269071945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482044224181692358762593 4111533168136269269071945)
              ·
                refine ⟨3083649876102201951803959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4111533168136269269071945 3083649876102201951803959)
                ·
                  refine ⟨4625474814153302927705939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083649876102201951803959 4625474814153302927705939)
                  ·
                    refine ⟨6938212221229954391558909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4625474814153302927705939 6938212221229954391558909)
                    ·
                      refine ⟨2601829582961232896834591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6938212221229954391558909 2601829582961232896834591)
                      ·
                        rfl

theorem cell23_5067045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_5067045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067045 prefixEnd_5067045 := by exact prefixLift 5067045
  have htrace : WordTrace (prefixWord ++ tailWord_5067045) baseStart_5067045 baseEnd_5067045 := by
    simpa [prefixWord, tailWord_5067045, baseEnd_5067045] using wordTrace_append hprefix tailTrace_5067045
  have hstable : (prefixWord ++ tailWord_5067045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067045).length < 2 ^ (prefixWord ++ tailWord_5067045).sum := by decide
  have hdescent : baseEnd_5067045 < baseStart_5067045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067057 : List Nat := [1, 2, 2, 3, 4, 2, 1, 8]
def baseStart_5067057 : Nat := 118140960795 + 5067057 * 2 ^ 59
def prefixEnd_5067057 : Nat := 4983230072969 + 3 ^ 40 * 5067057 * 2
def baseEnd_5067057 : Nat := 96364286841818031477205

theorem tailTrace_5067057 : CollatzResearch.WordTrace tailWord_5067057 prefixEnd_5067057 96364286841818031477205 := by
  unfold tailWord_5067057
  simp only [CollatzResearch.WordTrace]
  refine ⟨184810751603925348283935425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123207167735950232189290283 184810751603925348283935425)
  ·
    refine ⟨138608063702944011212951569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184810751603925348283935425 138608063702944011212951569)
    ·
      refine ⟨103956047777208008409713677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138608063702944011212951569 103956047777208008409713677)
      ·
        refine ⟨38983517916453003153642629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103956047777208008409713677 38983517916453003153642629)
        ·
          refine ⟨7309409609334938091307993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38983517916453003153642629 7309409609334938091307993)
          ·
            refine ⟨5482057207001203568480995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309409609334938091307993 5482057207001203568480995)
            ·
              refine ⟨8223085810501805352721493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482057207001203568480995 8223085810501805352721493)
              ·
                refine ⟨96364286841818031477205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8223085810501805352721493 96364286841818031477205)
                ·
                  rfl

theorem cell23_5067057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 8].length) (baseStart_5067057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067057 prefixEnd_5067057 := by exact prefixLift 5067057
  have htrace : WordTrace (prefixWord ++ tailWord_5067057) baseStart_5067057 baseEnd_5067057 := by
    simpa [prefixWord, tailWord_5067057, baseEnd_5067057] using wordTrace_append hprefix tailTrace_5067057
  have hstable : (prefixWord ++ tailWord_5067057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067057).length < 2 ^ (prefixWord ++ tailWord_5067057).sum := by decide
  have hdescent : baseEnd_5067057 < baseStart_5067057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067175 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_5067175 : Nat := 118140960795 + 5067175 * 2 ^ 59
def prefixEnd_5067175 : Nat := 4983230072969 + 3 ^ 40 * 5067175 * 2
def baseEnd_5067175 : Nat := 2601896335446317388208993

theorem tailTrace_5067175 : CollatzResearch.WordTrace tailWord_5067175 prefixEnd_5067175 2601896335446317388208993 := by
  unfold tailWord_5067175
  simp only [CollatzResearch.WordTrace]
  refine ⟨184815055417497854436730979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123210036944998569624487319 184815055417497854436730979)
  ·
    refine ⟨277222583126246781655096469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184815055417497854436730979 277222583126246781655096469)
    ·
      refine ⟨12994808584042817890082647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 277222583126246781655096469 12994808584042817890082647)
      ·
        refine ⟨19492212876064226835123971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12994808584042817890082647 19492212876064226835123971)
        ·
          refine ⟨29238319314096340252685957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19492212876064226835123971 29238319314096340252685957)
          ·
            refine ⟨5482184871393063797378617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29238319314096340252685957 5482184871393063797378617)
            ·
              refine ⟨4111638653544797848033963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482184871393063797378617 4111638653544797848033963)
              ·
                refine ⟨6167457980317196772050945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111638653544797848033963 6167457980317196772050945)
                ·
                  refine ⟨4625593485237897579038209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6167457980317196772050945 4625593485237897579038209)
                  ·
                    refine ⟨3469195113928423184278657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625593485237897579038209 3469195113928423184278657)
                    ·
                      refine ⟨2601896335446317388208993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469195113928423184278657 2601896335446317388208993)
                      ·
                        rfl

theorem cell23_5067175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_5067175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067175 prefixEnd_5067175 := by exact prefixLift 5067175
  have htrace : WordTrace (prefixWord ++ tailWord_5067175) baseStart_5067175 baseEnd_5067175 := by
    simpa [prefixWord, tailWord_5067175, baseEnd_5067175] using wordTrace_append hprefix tailTrace_5067175
  have hstable : (prefixWord ++ tailWord_5067175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067175).length < 2 ^ (prefixWord ++ tailWord_5067175).sum := by decide
  have hdescent : baseEnd_5067175 < baseStart_5067175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067214 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_5067214 : Nat := 118140960795 + 5067214 * 2 ^ 59
def prefixEnd_5067214 : Nat := 4983230072969 + 3 ^ 40 * 5067214 * 2
def baseEnd_5067214 : Nat := 2601916361191842735621313

theorem tailTrace_5067214 : CollatzResearch.WordTrace tailWord_5067214 prefixEnd_5067214 2601916361191842735621313 := by
  unfold tailWord_5067214
  simp only [CollatzResearch.WordTrace]
  refine ⟨23102059733044570512175087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123210985242904376064933797 23102059733044570512175087)
  ·
    refine ⟨34653089599566855768262631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23102059733044570512175087 34653089599566855768262631)
    ·
      refine ⟨51979634399350283652393947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34653089599566855768262631 51979634399350283652393947)
      ·
        refine ⟨77969451599025425478590921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51979634399350283652393947 77969451599025425478590921)
        ·
          refine ⟨58477088699269069108943191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77969451599025425478590921 58477088699269069108943191)
          ·
            refine ⟨87715633048903603663414787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58477088699269069108943191 87715633048903603663414787)
            ·
              refine ⟨131573449573355405495122181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87715633048903603663414787 131573449573355405495122181)
              ·
                refine ⟨24670021795004138530335409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131573449573355405495122181 24670021795004138530335409)
                ·
                  refine ⟨18502516346253103897751557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24670021795004138530335409 18502516346253103897751557)
                  ·
                    refine ⟨3469221814922456980828417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18502516346253103897751557 3469221814922456980828417)
                    ·
                      refine ⟨2601916361191842735621313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469221814922456980828417 2601916361191842735621313)
                      ·
                        rfl

theorem cell23_5067214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_5067214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067214 prefixEnd_5067214 := by exact prefixLift 5067214
  have htrace : WordTrace (prefixWord ++ tailWord_5067214) baseStart_5067214 baseEnd_5067214 := by
    simpa [prefixWord, tailWord_5067214, baseEnd_5067214] using wordTrace_append hprefix tailTrace_5067214
  have hstable : (prefixWord ++ tailWord_5067214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067214).length < 2 ^ (prefixWord ++ tailWord_5067214).sum := by decide
  have hdescent : baseEnd_5067214 < baseStart_5067214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067271 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 6]
def baseStart_5067271 : Nat := 118140960795 + 5067271 * 2 ^ 59
def prefixEnd_5067271 : Nat := 4983230072969 + 3 ^ 40 * 5067271 * 2
def baseEnd_5067271 : Nat := 289105069954349890289839

theorem tailTrace_5067271 : CollatzResearch.WordTrace tailWord_5067271 prefixEnd_5067271 289105069954349890289839 := by
  unfold tailWord_5067271
  simp only [CollatzResearch.WordTrace]
  refine ⟨184818556825150062832225667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123212371216766708554817111 184818556825150062832225667)
  ·
    refine ⟨277227835237725094248338501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184818556825150062832225667 277227835237725094248338501)
    ·
      refine ⟨51980219107073455171563469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277227835237725094248338501 51980219107073455171563469)
      ·
        refine ⟨19492582165152545689336301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51980219107073455171563469 19492582165152545689336301)
        ·
          refine ⟨7309718311932204633501113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19492582165152545689336301 7309718311932204633501113)
          ·
            refine ⟨5482288733949153475125835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309718311932204633501113 5482288733949153475125835)
            ·
              refine ⟨8223433100923730212688753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482288733949153475125835 8223433100923730212688753)
              ·
                refine ⟨6167574825692797659516565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8223433100923730212688753 6167574825692797659516565)
                ·
                  refine ⟨289105069954349890289839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6167574825692797659516565 289105069954349890289839)
                  ·
                    rfl

theorem cell23_5067271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 6].length) (baseStart_5067271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067271 prefixEnd_5067271 := by exact prefixLift 5067271
  have htrace : WordTrace (prefixWord ++ tailWord_5067271) baseStart_5067271 baseEnd_5067271 := by
    simpa [prefixWord, tailWord_5067271, baseEnd_5067271] using wordTrace_append hprefix tailTrace_5067271
  have hstable : (prefixWord ++ tailWord_5067271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067271).length < 2 ^ (prefixWord ++ tailWord_5067271).sum := by decide
  have hdescent : baseEnd_5067271 < baseStart_5067271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067307 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3]
def baseStart_5067307 : Nat := 118140960795 + 5067307 * 2 ^ 59
def prefixEnd_5067307 : Nat := 4983230072969 + 3 ^ 40 * 5067307 * 2
def baseEnd_5067307 : Nat := 2601964114892710871758385

theorem tailTrace_5067307 : CollatzResearch.WordTrace tailWord_5067307 prefixEnd_5067307 2601964114892710871758385 := by
  unfold tailWord_5067307
  simp only [CollatzResearch.WordTrace]
  refine ⟨184819869853019640980536175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123213246568679760653690783 184819869853019640980536175)
  ·
    refine ⟨277229804779529461470804263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184819869853019640980536175 277229804779529461470804263)
    ·
      refine ⟨415844707169294192206206395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277229804779529461470804263 415844707169294192206206395)
      ·
        refine ⟨623767060753941288309309593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415844707169294192206206395 623767060753941288309309593)
        ·
          refine ⟨467825295565455966231982195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623767060753941288309309593 467825295565455966231982195)
          ·
            refine ⟨701737943348183949347973293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467825295565455966231982195 701737943348183949347973293)
            ·
              refine ⟨263151728755568981005489985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701737943348183949347973293 263151728755568981005489985)
              ·
                refine ⟨197363796566676735754117489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263151728755568981005489985 197363796566676735754117489)
                ·
                  refine ⟨148022847425007551815588117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197363796566676735754117489 148022847425007551815588117)
                  ·
                    refine ⟨6938570973047228991355693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148022847425007551815588117 6938570973047228991355693)
                    ·
                      refine ⟨2601964114892710871758385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6938570973047228991355693 2601964114892710871758385)
                      ·
                        rfl

theorem cell23_5067307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3].length) (baseStart_5067307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067307 prefixEnd_5067307 := by exact prefixLift 5067307
  have htrace : WordTrace (prefixWord ++ tailWord_5067307) baseStart_5067307 baseEnd_5067307 := by
    simpa [prefixWord, tailWord_5067307, baseEnd_5067307] using wordTrace_append hprefix tailTrace_5067307
  have hstable : (prefixWord ++ tailWord_5067307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067307).length < 2 ^ (prefixWord ++ tailWord_5067307).sum := by decide
  have hdescent : baseEnd_5067307 < baseStart_5067307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067309 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5067309 : Nat := 118140960795 + 5067309 * 2 ^ 59
def prefixEnd_5067309 : Nat := 4983230072969 + 3 ^ 40 * 5067309 * 2
def baseEnd_5067309 : Nat := 867321713951339954644459

theorem tailTrace_5067309 : CollatzResearch.WordTrace tailWord_5067309 prefixEnd_5067309 867321713951339954644459 := by
  unfold tailWord_5067309
  simp only [CollatzResearch.WordTrace]
  refine ⟨184819942799012395322108981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123213295199341596881405987 184819942799012395322108981)
  ·
    refine ⟨17326869637407412061447717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184819942799012395322108981 17326869637407412061447717)
    ·
      refine ⟨3248788057013889761521447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17326869637407412061447717 3248788057013889761521447)
      ·
        refine ⟨4873182085520834642282171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248788057013889761521447 4873182085520834642282171)
        ·
          refine ⟨7309773128281251963423257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873182085520834642282171 7309773128281251963423257)
          ·
            refine ⟨5482329846210938972567443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309773128281251963423257 5482329846210938972567443)
            ·
              refine ⟨8223494769316408458851165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482329846210938972567443 8223494769316408458851165)
              ·
                refine ⟨3083810538493653172069187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8223494769316408458851165 3083810538493653172069187)
                ·
                  refine ⟨4625715807740479758103781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083810538493653172069187 4625715807740479758103781)
                  ·
                    refine ⟨867321713951339954644459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625715807740479758103781 867321713951339954644459)
                    ·
                      rfl

theorem cell23_5067309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5067309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067309 prefixEnd_5067309 := by exact prefixLift 5067309
  have htrace : WordTrace (prefixWord ++ tailWord_5067309) baseStart_5067309 baseEnd_5067309 := by
    simpa [prefixWord, tailWord_5067309, baseEnd_5067309] using wordTrace_append hprefix tailTrace_5067309
  have hstable : (prefixWord ++ tailWord_5067309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067309).length < 2 ^ (prefixWord ++ tailWord_5067309).sum := by decide
  have hdescent : baseEnd_5067309 < baseStart_5067309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067314 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_5067314 : Nat := 118140960795 + 5067314 * 2 ^ 59
def prefixEnd_5067314 : Nat := 4983230072969 + 3 ^ 40 * 5067314 * 2
def baseEnd_5067314 : Nat := 867322569752430781456951

theorem tailTrace_5067314 : CollatzResearch.WordTrace tailWord_5067314 prefixEnd_5067314 867322569752430781456951 := by
  unfold tailWord_5067314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46205031290998570294010249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123213416775996187450693997 46205031290998570294010249)
  ·
    refine ⟨34653773468248927720507687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46205031290998570294010249 34653773468248927720507687)
    ·
      refine ⟨51980660202373391580761531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34653773468248927720507687 51980660202373391580761531)
      ·
        refine ⟨77970990303560087371142297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51980660202373391580761531 77970990303560087371142297)
        ·
          refine ⟨58478242727670065528356723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77970990303560087371142297 58478242727670065528356723)
          ·
            refine ⟨87717364091505098292535085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58478242727670065528356723 87717364091505098292535085)
            ·
              refine ⟨32894011534314411859700657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87717364091505098292535085 32894011534314411859700657)
              ·
                refine ⟨24670508650735808894775493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32894011534314411859700657 24670508650735808894775493)
                ·
                  refine ⟨4625720372012964167770405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24670508650735808894775493 4625720372012964167770405)
                  ·
                    refine ⟨867322569752430781456951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625720372012964167770405 867322569752430781456951)
                    ·
                      rfl

theorem cell23_5067314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_5067314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067314 prefixEnd_5067314 := by exact prefixLift 5067314
  have htrace : WordTrace (prefixWord ++ tailWord_5067314) baseStart_5067314 baseEnd_5067314 := by
    simpa [prefixWord, tailWord_5067314, baseEnd_5067314] using wordTrace_append hprefix tailTrace_5067314
  have hstable : (prefixWord ++ tailWord_5067314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067314).length < 2 ^ (prefixWord ++ tailWord_5067314).sum := by decide
  have hdescent : baseEnd_5067314 < baseStart_5067314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067324 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_5067324 : Nat := 118140960795 + 5067324 * 2 ^ 59
def prefixEnd_5067324 : Nat := 4983230072969 + 3 ^ 40 * 5067324 * 2
def baseEnd_5067324 : Nat := 2601972844063837305245807

theorem tailTrace_5067324 : CollatzResearch.WordTrace tailWord_5067324 prefixEnd_5067324 2601972844063837305245807 := by
  unfold tailWord_5067324
  simp only [CollatzResearch.WordTrace]
  refine ⟨92410244946979026441952513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123213659929305368589270017 92410244946979026441952513)
  ·
    refine ⟨69307683710234269831464385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92410244946979026441952513 69307683710234269831464385)
    ·
      refine ⟨51980762782675702373598289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69307683710234269831464385 51980762782675702373598289)
      ·
        refine ⟨38985572087006776780198717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51980762782675702373598289 38985572087006776780198717)
        ·
          refine ⟨14619589532627541292574519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38985572087006776780198717 14619589532627541292574519)
          ·
            refine ⟨21929384298941311938861779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14619589532627541292574519 21929384298941311938861779)
            ·
              refine ⟨32894076448411967908292669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21929384298941311938861779 32894076448411967908292669)
              ·
                refine ⟨12335278668154487965609751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32894076448411967908292669 12335278668154487965609751)
                ·
                  refine ⟨18502918002231731948414627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12335278668154487965609751 18502918002231731948414627)
                  ·
                    refine ⟨27754377003347597922621941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18502918002231731948414627 27754377003347597922621941)
                    ·
                      refine ⟨2601972844063837305245807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27754377003347597922621941 2601972844063837305245807)
                      ·
                        rfl

theorem cell23_5067324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_5067324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067324 prefixEnd_5067324 := by exact prefixLift 5067324
  have htrace : WordTrace (prefixWord ++ tailWord_5067324) baseStart_5067324 baseEnd_5067324 := by
    simpa [prefixWord, tailWord_5067324, baseEnd_5067324] using wordTrace_append hprefix tailTrace_5067324
  have hstable : (prefixWord ++ tailWord_5067324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067324).length < 2 ^ (prefixWord ++ tailWord_5067324).sum := by decide
  have hdescent : baseEnd_5067324 < baseStart_5067324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067338 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_5067338 : Nat := 118140960795 + 5067338 * 2 ^ 59
def prefixEnd_5067338 : Nat := 4983230072969 + 3 ^ 40 * 5067338 * 2
def baseEnd_5067338 : Nat := 2601980032793000250470743

theorem tailTrace_5067338 : CollatzResearch.WordTrace tailWord_5067338 prefixEnd_5067338 2601980032793000250470743 := by
  unfold tailWord_5067338
  simp only [CollatzResearch.WordTrace]
  refine ⟨46205250128976833318728667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123214000343938222183276445 46205250128976833318728667)
  ·
    refine ⟨69307875193465249978093001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46205250128976833318728667 69307875193465249978093001)
    ·
      refine ⟨51980906395098937483569751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69307875193465249978093001 51980906395098937483569751)
      ·
        refine ⟨77971359592648406225354627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51980906395098937483569751 77971359592648406225354627)
        ·
          refine ⟨116957039388972609338031941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77971359592648406225354627 116957039388972609338031941)
          ·
            refine ⟨21929444885432364250880989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116957039388972609338031941 21929444885432364250880989)
            ·
              refine ⟨8223541832037136594080371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21929444885432364250880989 8223541832037136594080371)
              ·
                refine ⟨12335312748055704891120557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8223541832037136594080371 12335312748055704891120557)
                ·
                  refine ⟨4625742280520889334170209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12335312748055704891120557 4625742280520889334170209)
                  ·
                    refine ⟨3469306710390667000627657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625742280520889334170209 3469306710390667000627657)
                    ·
                      refine ⟨2601980032793000250470743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469306710390667000627657 2601980032793000250470743)
                      ·
                        rfl

theorem cell23_5067338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_5067338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067338 prefixEnd_5067338 := by exact prefixLift 5067338
  have htrace : WordTrace (prefixWord ++ tailWord_5067338) baseStart_5067338 baseEnd_5067338 := by
    simpa [prefixWord, tailWord_5067338, baseEnd_5067338] using wordTrace_append hprefix tailTrace_5067338
  have hstable : (prefixWord ++ tailWord_5067338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067338).length < 2 ^ (prefixWord ++ tailWord_5067338).sum := by decide
  have hdescent : baseEnd_5067338 < baseStart_5067338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067341 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5067341 : Nat := 118140960795 + 5067341 * 2 ^ 59
def prefixEnd_5067341 : Nat := 4983230072969 + 3 ^ 40 * 5067341 * 2
def baseEnd_5067341 : Nat := 2601981573234963738733229

theorem tailTrace_5067341 : CollatzResearch.WordTrace tailWord_5067341 prefixEnd_5067341 2601981573234963738733229 := by
  unfold tailWord_5067341
  simp only [CollatzResearch.WordTrace]
  refine ⟨184821109934896464787273877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123214073289930976524849251 184821109934896464787273877)
  ·
    refine ⟨8663489528198271786903463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184821109934896464787273877 8663489528198271786903463)
    ·
      refine ⟨12995234292297407680355195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663489528198271786903463 12995234292297407680355195)
      ·
        refine ⟨19492851438446111520532793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12995234292297407680355195 19492851438446111520532793)
        ·
          refine ⟨14619638578834583640399595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19492851438446111520532793 14619638578834583640399595)
          ·
            refine ⟨21929457868251875460599393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14619638578834583640399595 21929457868251875460599393)
            ·
              refine ⟨16447093401188906595449545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21929457868251875460599393 16447093401188906595449545)
              ·
                refine ⟨12335320050891679946587159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16447093401188906595449545 12335320050891679946587159)
                ·
                  refine ⟨18502980076337519919880739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12335320050891679946587159 18502980076337519919880739)
                  ·
                    refine ⟨27754470114506279879821109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18502980076337519919880739 27754470114506279879821109)
                    ·
                      refine ⟨2601981573234963738733229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27754470114506279879821109 2601981573234963738733229)
                      ·
                        rfl

theorem cell23_5067341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5067341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067341 prefixEnd_5067341 := by exact prefixLift 5067341
  have htrace : WordTrace (prefixWord ++ tailWord_5067341) baseStart_5067341 baseEnd_5067341 := by
    simpa [prefixWord, tailWord_5067341, baseEnd_5067341] using wordTrace_append hprefix tailTrace_5067341
  have hstable : (prefixWord ++ tailWord_5067341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067341).length < 2 ^ (prefixWord ++ tailWord_5067341).sum := by decide
  have hdescent : baseEnd_5067341 < baseStart_5067341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067348 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5067348 : Nat := 118140960795 + 5067348 * 2 ^ 59
def prefixEnd_5067348 : Nat := 4983230072969 + 3 ^ 40 * 5067348 * 2
def baseEnd_5067348 : Nat := 867328389199848403781899

theorem tailTrace_5067348 : CollatzResearch.WordTrace tailWord_5067348 prefixEnd_5067348 867328389199848403781899 := by
  unfold tailWord_5067348
  simp only [CollatzResearch.WordTrace]
  refine ⟨92410682622935552491389349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123214243497247403321852465 92410682622935552491389349)
  ·
    refine ⟨17327002991800416092135503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92410682622935552491389349 17327002991800416092135503)
    ·
      refine ⟨25990504487700624138203255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17327002991800416092135503 25990504487700624138203255)
      ·
        refine ⟨38985756731550936207304883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25990504487700624138203255 38985756731550936207304883)
        ·
          refine ⟨58478635097326404310957325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38985756731550936207304883 58478635097326404310957325)
          ·
            refine ⟨21929488161497401616608997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58478635097326404310957325 21929488161497401616608997)
            ·
              refine ⟨4111779030280762803114187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21929488161497401616608997 4111779030280762803114187)
              ·
                refine ⟨6167668545421144204671281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111779030280762803114187 6167668545421144204671281)
                ·
                  refine ⟨4625751409065858153503461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6167668545421144204671281 4625751409065858153503461)
                  ·
                    refine ⟨867328389199848403781899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625751409065858153503461 867328389199848403781899)
                    ·
                      rfl

theorem cell23_5067348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5067348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067348 prefixEnd_5067348 := by exact prefixLift 5067348
  have htrace : WordTrace (prefixWord ++ tailWord_5067348) baseStart_5067348 baseEnd_5067348 := by
    simpa [prefixWord, tailWord_5067348, baseEnd_5067348] using wordTrace_append hprefix tailTrace_5067348
  have hstable : (prefixWord ++ tailWord_5067348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067348).length < 2 ^ (prefixWord ++ tailWord_5067348).sum := by decide
  have hdescent : baseEnd_5067348 < baseStart_5067348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067389 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_5067389 : Nat := 118140960795 + 5067389 * 2 ^ 59
def prefixEnd_5067389 : Nat := 4983230072969 + 3 ^ 40 * 5067389 * 2
def baseEnd_5067389 : Nat := 2602006220306379550933009

theorem tailTrace_5067389 : CollatzResearch.WordTrace tailWord_5067389 prefixEnd_5067389 2602006220306379550933009 := by
  unfold tailWord_5067389
  simp only [CollatzResearch.WordTrace]
  refine ⟨184822860638722568985021221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123215240425815045990014147 184822860638722568985021221)
  ·
    refine ⟨34654286369760481684691479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184822860638722568985021221 34654286369760481684691479)
    ·
      refine ⟨51981429554640722527037219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34654286369760481684691479 51981429554640722527037219)
      ·
        refine ⟨77972144331961083790555829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51981429554640722527037219 77972144331961083790555829)
        ·
          refine ⟨7309888531121351605364609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77972144331961083790555829 7309888531121351605364609)
          ·
            refine ⟨5482416398341013704023457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309888531121351605364609 5482416398341013704023457)
            ·
              refine ⟨4111812298755760278017593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482416398341013704023457 4111812298755760278017593)
              ·
                refine ⟨3083859224066820208513195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4111812298755760278017593 3083859224066820208513195)
                ·
                  refine ⟨4625788836100230312769793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083859224066820208513195 4625788836100230312769793)
                  ·
                    refine ⟨3469341627075172734577345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625788836100230312769793 3469341627075172734577345)
                    ·
                      refine ⟨2602006220306379550933009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469341627075172734577345 2602006220306379550933009)
                      ·
                        rfl

theorem cell23_5067389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_5067389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067389 prefixEnd_5067389 := by exact prefixLift 5067389
  have htrace : WordTrace (prefixWord ++ tailWord_5067389) baseStart_5067389 baseEnd_5067389 := by
    simpa [prefixWord, tailWord_5067389, baseEnd_5067389] using wordTrace_append hprefix tailTrace_5067389
  have hstable : (prefixWord ++ tailWord_5067389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067389).length < 2 ^ (prefixWord ++ tailWord_5067389).sum := by decide
  have hdescent : baseEnd_5067389 < baseStart_5067389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067407 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_5067407 : Nat := 118140960795 + 5067407 * 2 ^ 59
def prefixEnd_5067407 : Nat := 4983230072969 + 3 ^ 40 * 5067407 * 2
def baseEnd_5067407 : Nat := 2602015462958160480507925

theorem tailTrace_5067407 : CollatzResearch.WordTrace tailWord_5067407 prefixEnd_5067407 2602015462958160480507925 := by
  unfold tailWord_5067407
  simp only [CollatzResearch.WordTrace]
  refine ⟨184823517152657358059176475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123215678101771572039450983 184823517152657358059176475)
  ·
    refine ⟨277235275728986037088764713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184823517152657358059176475 277235275728986037088764713)
    ·
      refine ⟨207926456796739527816573535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277235275728986037088764713 207926456796739527816573535)
      ·
        refine ⟨311889685195109291724860303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207926456796739527816573535 311889685195109291724860303)
        ·
          refine ⟨467834527792663937587290455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311889685195109291724860303 467834527792663937587290455)
          ·
            refine ⟨701751791688995906380935683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467834527792663937587290455 701751791688995906380935683)
            ·
              refine ⟨1052627687533493859571403525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701751791688995906380935683 1052627687533493859571403525)
              ·
                refine ⟨197367691412530098669638161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1052627687533493859571403525 197367691412530098669638161)
                ·
                  refine ⟨148025768559397574002228621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197367691412530098669638161 148025768559397574002228621)
                  ·
                    refine ⟨55509663209774090250835733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148025768559397574002228621 55509663209774090250835733)
                    ·
                      refine ⟨2602015462958160480507925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55509663209774090250835733 2602015462958160480507925)
                      ·
                        rfl

theorem cell23_5067407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_5067407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067407 prefixEnd_5067407 := by exact prefixLift 5067407
  have htrace : WordTrace (prefixWord ++ tailWord_5067407) baseStart_5067407 baseEnd_5067407 := by
    simpa [prefixWord, tailWord_5067407, baseEnd_5067407] using wordTrace_append hprefix tailTrace_5067407
  have hstable : (prefixWord ++ tailWord_5067407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067407).length < 2 ^ (prefixWord ++ tailWord_5067407).sum := by decide
  have hdescent : baseEnd_5067407 < baseStart_5067407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067428 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_5067428 : Nat := 118140960795 + 5067428 * 2 ^ 59
def prefixEnd_5067428 : Nat := 4983230072969 + 3 ^ 40 * 5067428 * 2
def baseEnd_5067428 : Nat := 2602026246051904898345329

theorem tailTrace_5067428 : CollatzResearch.WordTrace tailWord_5067428 prefixEnd_5067428 2602026246051904898345329 := by
  unfold tailWord_5067428
  simp only [CollatzResearch.WordTrace]
  refine ⟨92412141542790639322845469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123216188723720852430460625 92412141542790639322845469)
  ·
    refine ⟨34654553078546489746067051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92412141542790639322845469 34654553078546489746067051)
    ·
      refine ⟨51981829617819734619100577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34654553078546489746067051 51981829617819734619100577)
      ·
        refine ⟨38986372213364800964325433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51981829617819734619100577 38986372213364800964325433)
        ·
          refine ⟨29239779160023600723244075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38986372213364800964325433 29239779160023600723244075)
          ·
            refine ⟨43859668740035401084866113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29239779160023600723244075 43859668740035401084866113)
            ·
              refine ⟨32894751555026550813649585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43859668740035401084866113 32894751555026550813649585)
              ·
                refine ⟨24671063666269913110237189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32894751555026550813649585 24671063666269913110237189)
                ·
                  refine ⟨4625824437425608708169473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24671063666269913110237189 4625824437425608708169473)
                  ·
                    refine ⟨3469368328069206531127105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625824437425608708169473 3469368328069206531127105)
                    ·
                      refine ⟨2602026246051904898345329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469368328069206531127105 2602026246051904898345329)
                      ·
                        rfl

theorem cell23_5067428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_5067428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067428 prefixEnd_5067428 := by exact prefixLift 5067428
  have htrace : WordTrace (prefixWord ++ tailWord_5067428) baseStart_5067428 baseEnd_5067428 := by
    simpa [prefixWord, tailWord_5067428, baseEnd_5067428] using wordTrace_append hprefix tailTrace_5067428
  have hstable : (prefixWord ++ tailWord_5067428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067428).length < 2 ^ (prefixWord ++ tailWord_5067428).sum := by decide
  have hdescent : baseEnd_5067428 < baseStart_5067428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067445 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5067445 : Nat := 118140960795 + 5067445 * 2 ^ 59
def prefixEnd_5067445 : Nat := 4983230072969 + 3 ^ 40 * 5067445 * 2
def baseEnd_5067445 : Nat := 2602034975223031331832751

theorem tailTrace_5067445 : CollatzResearch.WordTrace tailWord_5067445 prefixEnd_5067445 2602034975223031331832751 := by
  unfold tailWord_5067445
  simp only [CollatzResearch.WordTrace]
  refine ⟨184824903126519690549059789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123216602084346460366039859 184824903126519690549059789)
  ·
    refine ⟨69309338672444883955897421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184824903126519690549059789 69309338672444883955897421)
    ·
      refine ⟨25991002002166831483461533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69309338672444883955897421 25991002002166831483461533)
      ·
        refine ⟨9746625750812561806298075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25991002002166831483461533 9746625750812561806298075)
        ·
          refine ⟨14619938626218842709447113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9746625750812561806298075 14619938626218842709447113)
          ·
            refine ⟨10964953969664132032085335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14619938626218842709447113 10964953969664132032085335)
            ·
              refine ⟨16447430954496198048128003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10964953969664132032085335 16447430954496198048128003)
              ·
                refine ⟨24671146431744297072192005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16447430954496198048128003 24671146431744297072192005)
                ·
                  refine ⟨4625839955952055701036001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24671146431744297072192005 4625839955952055701036001)
                  ·
                    refine ⟨3469379966964041775777001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4625839955952055701036001 3469379966964041775777001)
                    ·
                      refine ⟨2602034975223031331832751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469379966964041775777001 2602034975223031331832751)
                      ·
                        rfl

theorem cell23_5067445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5067445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067445 prefixEnd_5067445 := by exact prefixLift 5067445
  have htrace : WordTrace (prefixWord ++ tailWord_5067445) baseStart_5067445 baseEnd_5067445 := by
    simpa [prefixWord, tailWord_5067445, baseEnd_5067445] using wordTrace_append hprefix tailTrace_5067445
  have hstable : (prefixWord ++ tailWord_5067445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067445).length < 2 ^ (prefixWord ++ tailWord_5067445).sum := by decide
  have hdescent : baseEnd_5067445 < baseStart_5067445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067464 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_5067464 : Nat := 118140960795 + 5067464 * 2 ^ 59
def prefixEnd_5067464 : Nat := 4983230072969 + 3 ^ 40 * 5067464 * 2
def baseEnd_5067464 : Nat := 867348243785155585831721

theorem tailTrace_5067464 : CollatzResearch.WordTrace tailWord_5067464 prefixEnd_5067464 867348243785155585831721 := by
  unfold tailWord_5067464
  simp only [CollatzResearch.WordTrace]
  refine ⟨92412798056725428397000723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123217064075633904529334297 92412798056725428397000723)
  ·
    refine ⟨138619197085088142595501085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92412798056725428397000723 138619197085088142595501085)
    ·
      refine ⟨51982198906908053473312907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138619197085088142595501085 51982198906908053473312907)
      ·
        refine ⟨77973298360362080209969361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51982198906908053473312907 77973298360362080209969361)
        ·
          refine ⟨58479973770271560157477021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77973298360362080209969361 58479973770271560157477021)
          ·
            refine ⟨21929990163851835059053883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58479973770271560157477021 21929990163851835059053883)
            ·
              refine ⟨32894985245777752588580825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21929990163851835059053883 32894985245777752588580825)
              ·
                refine ⟨24671238934333314441435619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32894985245777752588580825 24671238934333314441435619)
                ·
                  refine ⟨37006858401499971662153429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24671238934333314441435619 37006858401499971662153429)
                  ·
                    refine ⟨867348243785155585831721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37006858401499971662153429 867348243785155585831721)
                    ·
                      rfl

theorem cell23_5067464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_5067464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067464 prefixEnd_5067464 := by exact prefixLift 5067464
  have htrace : WordTrace (prefixWord ++ tailWord_5067464) baseStart_5067464 baseEnd_5067464 := by
    simpa [prefixWord, tailWord_5067464, baseEnd_5067464] using wordTrace_append hprefix tailTrace_5067464
  have hstable : (prefixWord ++ tailWord_5067464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067464).length < 2 ^ (prefixWord ++ tailWord_5067464).sum := by decide
  have hdescent : baseEnd_5067464 < baseStart_5067464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067514 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_5067514 : Nat := 118140960795 + 5067514 * 2 ^ 59
def prefixEnd_5067514 : Nat := 4983230072969 + 3 ^ 40 * 5067514 * 2
def baseEnd_5067514 : Nat := 2602070405388191561869933

theorem tailTrace_5067514 : CollatzResearch.WordTrace tailWord_5067514 prefixEnd_5067514 2602070405388191561869933 := by
  unfold tailWord_5067514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46206854940817428833330399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123218279842179810222214397 46206854940817428833330399)
  ·
    refine ⟨69310282411226143249995599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46206854940817428833330399 69310282411226143249995599)
    ·
      refine ⟨103965423616839214874993399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69310282411226143249995599 103965423616839214874993399)
      ·
        refine ⟨155948135425258822312490099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103965423616839214874993399 155948135425258822312490099)
        ·
          refine ⟨233922203137888233468735149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155948135425258822312490099 233922203137888233468735149)
          ·
            refine ⟨87720826176708087550775681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233922203137888233468735149 87720826176708087550775681)
            ·
              refine ⟨65790619632531065663081761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87720826176708087550775681 65790619632531065663081761)
              ·
                refine ⟨49342964724398299247311321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65790619632531065663081761 49342964724398299247311321)
                ·
                  refine ⟨37007223543298724435483491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49342964724398299247311321 37007223543298724435483491)
                  ·
                    refine ⟨55510835314948086653225237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37007223543298724435483491 55510835314948086653225237)
                    ·
                      refine ⟨2602070405388191561869933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55510835314948086653225237 2602070405388191561869933)
                      ·
                        rfl

theorem cell23_5067514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_5067514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067514 prefixEnd_5067514 := by exact prefixLift 5067514
  have htrace : WordTrace (prefixWord ++ tailWord_5067514) baseStart_5067514 baseEnd_5067514 := by
    simpa [prefixWord, tailWord_5067514, baseEnd_5067514] using wordTrace_append hprefix tailTrace_5067514
  have hstable : (prefixWord ++ tailWord_5067514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067514).length < 2 ^ (prefixWord ++ tailWord_5067514).sum := by decide
  have hdescent : baseEnd_5067514 < baseStart_5067514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067521 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_5067521 : Nat := 118140960795 + 5067521 * 2 ^ 59
def prefixEnd_5067521 : Nat := 4983230072969 + 3 ^ 40 * 5067521 * 2
def baseEnd_5067521 : Nat := 2602073999752773034482401

theorem tailTrace_5067521 : CollatzResearch.WordTrace tailWord_5067521 prefixEnd_5067521 2602073999752773034482401 := by
  unfold tailWord_5067521
  simp only [CollatzResearch.WordTrace]
  refine ⟨184827675074244355528826417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123218450049496237019217611 184827675074244355528826417)
  ·
    refine ⟨138620756305683266646619813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184827675074244355528826417 138620756305683266646619813)
    ·
      refine ⟨25991391807315612496241215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138620756305683266646619813 25991391807315612496241215)
      ·
        refine ⟨38987087710973418744361823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25991391807315612496241215 38987087710973418744361823)
        ·
          refine ⟨58480631566460128116542735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38987087710973418744361823 58480631566460128116542735)
          ·
            refine ⟨87720947349690192174814103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58480631566460128116542735 87720947349690192174814103)
            ·
              refine ⟨131581421024535288262221155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87720947349690192174814103 131581421024535288262221155)
              ·
                refine ⟨197372131536802932393331733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131581421024535288262221155 197372131536802932393331733)
                ·
                  refine ⟨9251818665787637455937425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197372131536802932393331733 9251818665787637455937425)
                  ·
                    refine ⟨6938863999340728091953069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9251818665787637455937425 6938863999340728091953069)
                    ·
                      refine ⟨2602073999752773034482401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6938863999340728091953069 2602073999752773034482401)
                      ·
                        rfl

theorem cell23_5067521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_5067521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067521 prefixEnd_5067521 := by exact prefixLift 5067521
  have htrace : WordTrace (prefixWord ++ tailWord_5067521) baseStart_5067521 baseEnd_5067521 := by
    simpa [prefixWord, tailWord_5067521, baseEnd_5067521] using wordTrace_append hprefix tailTrace_5067521
  have hstable : (prefixWord ++ tailWord_5067521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067521).length < 2 ^ (prefixWord ++ tailWord_5067521).sum := by decide
  have hdescent : baseEnd_5067521 < baseStart_5067521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067544 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5067544 : Nat := 118140960795 + 5067544 * 2 ^ 59
def prefixEnd_5067544 : Nat := 4983230072969 + 3 ^ 40 * 5067544 * 2
def baseEnd_5067544 : Nat := 2602085809807826444494795

theorem tailTrace_5067544 : CollatzResearch.WordTrace tailWord_5067544 prefixEnd_5067544 2602085809807826444494795 := by
  unfold tailWord_5067544
  simp only [CollatzResearch.WordTrace]
  refine ⟨92414256976580515228456843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123219009302107353637942457 92414256976580515228456843)
  ·
    refine ⟨138621385464870772842685265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92414256976580515228456843 138621385464870772842685265)
    ·
      refine ⟨103966039098653079632013949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138621385464870772842685265 103966039098653079632013949)
      ·
        refine ⟨38987264661994904862005231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103966039098653079632013949 38987264661994904862005231)
        ·
          refine ⟨58480896992992357293007847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38987264661994904862005231 58480896992992357293007847)
          ·
            refine ⟨87721345489488535939511771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58480896992992357293007847 87721345489488535939511771)
            ·
              refine ⟨131582018234232803909267657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87721345489488535939511771 131582018234232803909267657)
              ·
                refine ⟨98686513675674602931950743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131582018234232803909267657 98686513675674602931950743)
                ·
                  refine ⟨148029770513511904397926115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98686513675674602931950743 148029770513511904397926115)
                  ·
                    refine ⟨222044655770267856596889173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148029770513511904397926115 222044655770267856596889173)
                    ·
                      refine ⟨2602085809807826444494795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 222044655770267856596889173 2602085809807826444494795)
                      ·
                        rfl

theorem cell23_5067544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5067544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067544 prefixEnd_5067544 := by exact prefixLift 5067544
  have htrace : WordTrace (prefixWord ++ tailWord_5067544) baseStart_5067544 baseEnd_5067544 := by
    simpa [prefixWord, tailWord_5067544, baseEnd_5067544] using wordTrace_append hprefix tailTrace_5067544
  have hstable : (prefixWord ++ tailWord_5067544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067544).length < 2 ^ (prefixWord ++ tailWord_5067544).sum := by decide
  have hdescent : baseEnd_5067544 < baseStart_5067544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067571 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 3, 5]
def baseStart_5067571 : Nat := 118140960795 + 5067571 * 2 ^ 59
def prefixEnd_5067571 : Nat := 4983230072969 + 3 ^ 40 * 5067571 * 2
def baseEnd_5067571 : Nat := 867366557928499279619057

theorem tailTrace_5067571 : CollatzResearch.WordTrace tailWord_5067571 prefixEnd_5067571 867366557928499279619057 := by
  unfold tailWord_5067571
  simp only [CollatzResearch.WordTrace]
  refine ⟨184829498724063214068146567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123219665816042142712097711 184829498724063214068146567)
  ·
    refine ⟨277244248086094821102219851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184829498724063214068146567 277244248086094821102219851)
    ·
      refine ⟨415866372129142231653329777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277244248086094821102219851 415866372129142231653329777)
      ·
        refine ⟨311899779096856673739997333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415866372129142231653329777 311899779096856673739997333)
        ·
          refine ⟨14620302145165156581562375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 311899779096856673739997333 14620302145165156581562375)
          ·
            refine ⟨21930453217747734872343563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14620302145165156581562375 21930453217747734872343563)
            ·
              refine ⟨32895679826621602308515345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21930453217747734872343563 32895679826621602308515345)
              ·
                refine ⟨24671759869966201731386509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32895679826621602308515345 24671759869966201731386509)
                ·
                  refine ⟨9251909951237325649269941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24671759869966201731386509 9251909951237325649269941)
                  ·
                    refine ⟨867366557928499279619057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9251909951237325649269941 867366557928499279619057)
                    ·
                      rfl

theorem cell23_5067571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 5].length) (baseStart_5067571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067571 prefixEnd_5067571 := by exact prefixLift 5067571
  have htrace : WordTrace (prefixWord ++ tailWord_5067571) baseStart_5067571 baseEnd_5067571 := by
    simpa [prefixWord, tailWord_5067571, baseEnd_5067571] using wordTrace_append hprefix tailTrace_5067571
  have hstable : (prefixWord ++ tailWord_5067571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067571).length < 2 ^ (prefixWord ++ tailWord_5067571).sum := by decide
  have hdescent : baseEnd_5067571 < baseStart_5067571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067602 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_5067602 : Nat := 118140960795 + 5067602 * 2 ^ 59
def prefixEnd_5067602 : Nat := 4983230072969 + 3 ^ 40 * 5067602 * 2
def baseEnd_5067602 : Nat := 2602115591685787217569529

theorem tailTrace_5067602 : CollatzResearch.WordTrace tailWord_5067602 prefixEnd_5067602 2602115591685787217569529 := by
  unfold tailWord_5067602
  simp only [CollatzResearch.WordTrace]
  refine ⟨46207657346737726590631265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123220419591300604241683373 46207657346737726590631265)
  ·
    refine ⟨34655743010053294942973449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46207657346737726590631265 34655743010053294942973449)
    ·
      refine ⟨25991807257539971207230087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34655743010053294942973449 25991807257539971207230087)
      ·
        refine ⟨38987710886309956810845131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25991807257539971207230087 38987710886309956810845131)
        ·
          refine ⟨58481566329464935216267697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38987710886309956810845131 58481566329464935216267697)
          ·
            refine ⟨43861174747098701412200773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58481566329464935216267697 43861174747098701412200773)
            ·
              refine ⟨8223970265081006514787645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43861174747098701412200773 8223970265081006514787645)
              ·
                refine ⟨3083988849405377443045367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8223970265081006514787645 3083988849405377443045367)
                ·
                  refine ⟨4625983274108066164568051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083988849405377443045367 4625983274108066164568051)
                  ·
                    refine ⟨6938974911162099246852077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4625983274108066164568051 6938974911162099246852077)
                    ·
                      refine ⟨2602115591685787217569529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6938974911162099246852077 2602115591685787217569529)
                      ·
                        rfl

theorem cell23_5067602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_5067602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067602 prefixEnd_5067602 := by exact prefixLift 5067602
  have htrace : WordTrace (prefixWord ++ tailWord_5067602) baseStart_5067602 baseEnd_5067602 := by
    simpa [prefixWord, tailWord_5067602, baseEnd_5067602] using wordTrace_append hprefix tailTrace_5067602
  have hstable : (prefixWord ++ tailWord_5067602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067602).length < 2 ^ (prefixWord ++ tailWord_5067602).sum := by decide
  have hdescent : baseEnd_5067602 < baseStart_5067602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067621 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5067621 : Nat := 118140960795 + 5067621 * 2 ^ 59
def prefixEnd_5067621 : Nat := 4983230072969 + 3 ^ 40 * 5067621 * 2
def baseEnd_5067621 : Nat := 2602125347818222643231941

theorem tailTrace_5067621 : CollatzResearch.WordTrace tailWord_5067621 prefixEnd_5067621 2602125347818222643231941 := by
  unfold tailWord_5067621
  simp only [CollatzResearch.WordTrace]
  refine ⟨184831322373882072607466717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123220881582588048404977811 184831322373882072607466717)
  ·
    refine ⟨69311745890205777227800019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184831322373882072607466717 69311745890205777227800019)
    ·
      refine ⟨103967618835308665841700029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69311745890205777227800019 103967618835308665841700029)
      ·
        refine ⟨38987857063240749690637511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103967618835308665841700029 38987857063240749690637511)
        ·
          refine ⟨58481785594861124535956267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38987857063240749690637511 58481785594861124535956267)
          ·
            refine ⟨87722678392291686803934401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58481785594861124535956267 87722678392291686803934401)
            ·
              refine ⟨65792008794218765102950801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87722678392291686803934401 65792008794218765102950801)
              ·
                refine ⟨49344006595664073827213101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65792008794218765102950801 49344006595664073827213101)
                ·
                  refine ⟨18504002473374027685204913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49344006595664073827213101 18504002473374027685204913)
                  ·
                    refine ⟨13878001855030520763903685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18504002473374027685204913 13878001855030520763903685)
                    ·
                      refine ⟨2602125347818222643231941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13878001855030520763903685 2602125347818222643231941)
                      ·
                        rfl

theorem cell23_5067621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5067621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067621 prefixEnd_5067621 := by exact prefixLift 5067621
  have htrace : WordTrace (prefixWord ++ tailWord_5067621) baseStart_5067621 baseEnd_5067621 := by
    simpa [prefixWord, tailWord_5067621, baseEnd_5067621] using wordTrace_append hprefix tailTrace_5067621
  have hstable : (prefixWord ++ tailWord_5067621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067621).length < 2 ^ (prefixWord ++ tailWord_5067621).sum := by decide
  have hdescent : baseEnd_5067621 < baseStart_5067621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067671 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_5067671 : Nat := 118140960795 + 5067671 * 2 ^ 59
def prefixEnd_5067671 : Nat := 4983230072969 + 3 ^ 40 * 5067671 * 2
def baseEnd_5067671 : Nat := 2602151021850947447606711

theorem tailTrace_5067671 : CollatzResearch.WordTrace tailWord_5067671 prefixEnd_5067671 2602151021850947447606711 := by
  unfold tailWord_5067671
  simp only [CollatzResearch.WordTrace]
  refine ⟨184833146023700931146786867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123222097349133954097857911 184833146023700931146786867)
  ·
    refine ⟨277249719035551396720180301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184833146023700931146786867 277249719035551396720180301)
    ·
      refine ⟨103968644638331773770067613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277249719035551396720180301 103968644638331773770067613)
      ·
        refine ⟨38988241739374415163775355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103968644638331773770067613 38988241739374415163775355)
        ·
          refine ⟨58482362609061622745663033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38988241739374415163775355 58482362609061622745663033)
          ·
            refine ⟨43861771956796217059247275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58482362609061622745663033 43861771956796217059247275)
            ·
              refine ⟨65792657935194325588870913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43861771956796217059247275 65792657935194325588870913)
              ·
                refine ⟨49344493451395744191653185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65792657935194325588870913 49344493451395744191653185)
                ·
                  refine ⟨37008370088546808143739889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49344493451395744191653185 37008370088546808143739889)
                  ·
                    refine ⟨27756277566410106107804917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37008370088546808143739889 27756277566410106107804917)
                    ·
                      refine ⟨2602151021850947447606711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27756277566410106107804917 2602151021850947447606711)
                      ·
                        rfl

theorem cell23_5067671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_5067671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067671 prefixEnd_5067671 := by exact prefixLift 5067671
  have htrace : WordTrace (prefixWord ++ tailWord_5067671) baseStart_5067671 baseEnd_5067671 := by
    simpa [prefixWord, tailWord_5067671, baseEnd_5067671] using wordTrace_append hprefix tailTrace_5067671
  have hstable : (prefixWord ++ tailWord_5067671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067671).length < 2 ^ (prefixWord ++ tailWord_5067671).sum := by decide
  have hdescent : baseEnd_5067671 < baseStart_5067671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067676 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5067676 : Nat := 118140960795 + 5067676 * 2 ^ 59
def prefixEnd_5067676 : Nat := 4983230072969 + 3 ^ 40 * 5067676 * 2
def baseEnd_5067676 : Nat := 2602153589254219928044189

theorem tailTrace_5067676 : CollatzResearch.WordTrace tailWord_5067676 prefixEnd_5067676 2602153589254219928044189 := by
  unfold tailWord_5067676
  simp only [CollatzResearch.WordTrace]
  refine ⟨92416664194341408500359441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123222218925788544667145921 92416664194341408500359441)
  ·
    refine ⟨69312498145756056375269581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92416664194341408500359441 69312498145756056375269581)
    ·
      refine ⟨25992186804658521140726093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69312498145756056375269581 25992186804658521140726093)
      ·
        refine ⟨9747070051746945427772285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25992186804658521140726093 9747070051746945427772285)
        ·
          refine ⟨3655151269405104535414607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9747070051746945427772285 3655151269405104535414607)
          ·
            refine ⟨5482726904107656803121911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655151269405104535414607 5482726904107656803121911)
            ·
              refine ⟨8224090356161485204682867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482726904107656803121911 8224090356161485204682867)
              ·
                refine ⟨12336135534242227807024301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224090356161485204682867 12336135534242227807024301)
                ·
                  refine ⟨4626050825340835427634113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12336135534242227807024301 4626050825340835427634113)
                  ·
                    refine ⟨3469538119005626570725585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626050825340835427634113 3469538119005626570725585)
                    ·
                      refine ⟨2602153589254219928044189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469538119005626570725585 2602153589254219928044189)
                      ·
                        rfl

theorem cell23_5067676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5067676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067676 prefixEnd_5067676 := by exact prefixLift 5067676
  have htrace : WordTrace (prefixWord ++ tailWord_5067676) baseStart_5067676 baseEnd_5067676 := by
    simpa [prefixWord, tailWord_5067676, baseEnd_5067676] using wordTrace_append hprefix tailTrace_5067676
  have hstable : (prefixWord ++ tailWord_5067676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067676).length < 2 ^ (prefixWord ++ tailWord_5067676).sum := by decide
  have hdescent : baseEnd_5067676 < baseStart_5067676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067711 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_5067711 : Nat := 118140960795 + 5067711 * 2 ^ 59
def prefixEnd_5067711 : Nat := 4983230072969 + 3 ^ 40 * 5067711 * 2
def baseEnd_5067711 : Nat := 2602171561077127291106527

theorem tailTrace_5067711 : CollatzResearch.WordTrace tailWord_5067711 prefixEnd_5067711 2602171561077127291106527 := by
  unfold tailWord_5067711
  simp only [CollatzResearch.WordTrace]
  refine ⟨184834604943556017978242987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123223069962370678652161991 184834604943556017978242987)
  ·
    refine ⟨277251907415334026967364481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184834604943556017978242987 277251907415334026967364481)
    ·
      refine ⟨207938930561500520225523361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277251907415334026967364481 207938930561500520225523361)
      ·
        refine ⟨155954197921125390169142521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207938930561500520225523361 155954197921125390169142521)
        ·
          refine ⟨116965648440844042626856891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155954197921125390169142521 116965648440844042626856891)
          ·
            refine ⟨175448472661266063940285337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116965648440844042626856891 175448472661266063940285337)
            ·
              refine ⟨131586354495949547955214003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175448472661266063940285337 131586354495949547955214003)
              ·
                refine ⟨197379531743924321932821005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131586354495949547955214003 197379531743924321932821005)
                ·
                  refine ⟨74017324403971620724807877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197379531743924321932821005 74017324403971620724807877)
                  ·
                    refine ⟨13878248325744678885901477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74017324403971620724807877 13878248325744678885901477)
                    ·
                      refine ⟨2602171561077127291106527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13878248325744678885901477 2602171561077127291106527)
                      ·
                        rfl

theorem cell23_5067711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_5067711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067711 prefixEnd_5067711 := by exact prefixLift 5067711
  have htrace : WordTrace (prefixWord ++ tailWord_5067711) baseStart_5067711 baseEnd_5067711 := by
    simpa [prefixWord, tailWord_5067711, baseEnd_5067711] using wordTrace_append hprefix tailTrace_5067711
  have hstable : (prefixWord ++ tailWord_5067711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067711).length < 2 ^ (prefixWord ++ tailWord_5067711).sum := by decide
  have hdescent : baseEnd_5067711 < baseStart_5067711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067749 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5067749 : Nat := 118140960795 + 5067749 * 2 ^ 59
def prefixEnd_5067749 : Nat := 4983230072969 + 3 ^ 40 * 5067749 * 2
def baseEnd_5067749 : Nat := 2602191073341998142431353

theorem tailTrace_5067749 : CollatzResearch.WordTrace tailWord_5067749 prefixEnd_5067749 2602191073341998142431353 := by
  unfold tailWord_5067749
  simp only [CollatzResearch.WordTrace]
  refine ⟨184835990917418350468126301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123223993944945566978750867 184835990917418350468126301)
  ·
    refine ⟨69313496594031881425547363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184835990917418350468126301 69313496594031881425547363)
    ·
      refine ⟨103970244891047822138321045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69313496594031881425547363 103970244891047822138321045)
      ·
        refine ⟨4873605229267866662733799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103970244891047822138321045 4873605229267866662733799)
        ·
          refine ⟨7310407843901799994100699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873605229267866662733799 7310407843901799994100699)
          ·
            refine ⟨10965611765852699991151049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7310407843901799994100699 10965611765852699991151049)
            ·
              refine ⟨8224208824389524993363287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10965611765852699991151049 8224208824389524993363287)
              ·
                refine ⟨12336313236584287490044931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224208824389524993363287 12336313236584287490044931)
                ·
                  refine ⟨18504469854876431235067397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12336313236584287490044931 18504469854876431235067397)
                  ·
                    refine ⟨3469588097789330856575137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18504469854876431235067397 3469588097789330856575137)
                    ·
                      refine ⟨2602191073341998142431353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469588097789330856575137 2602191073341998142431353)
                      ·
                        rfl

theorem cell23_5067749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5067749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067749 prefixEnd_5067749 := by exact prefixLift 5067749
  have htrace : WordTrace (prefixWord ++ tailWord_5067749) baseStart_5067749 baseEnd_5067749 := by
    simpa [prefixWord, tailWord_5067749, baseEnd_5067749] using wordTrace_append hprefix tailTrace_5067749
  have hstable : (prefixWord ++ tailWord_5067749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067749).length < 2 ^ (prefixWord ++ tailWord_5067749).sum := by decide
  have hdescent : baseEnd_5067749 < baseStart_5067749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067825 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_5067825 : Nat := 118140960795 + 5067825 * 2 ^ 59
def prefixEnd_5067825 : Nat := 4983230072969 + 3 ^ 40 * 5067825 * 2
def baseEnd_5067825 : Nat := 2602230097871739845081003

theorem tailTrace_5067825 : CollatzResearch.WordTrace tailWord_5067825 prefixEnd_5067825 2602230097871739845081003 := by
  unfold tailWord_5067825
  simp only [CollatzResearch.WordTrace]
  refine ⟨184838762865143015447892929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123225841910095343631928619 184838762865143015447892929)
  ·
    refine ⟨138629072148857261585919697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184838762865143015447892929 138629072148857261585919697)
    ·
      refine ⟨103971804111642946189439773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138629072148857261585919697 103971804111642946189439773)
      ·
        refine ⟨38989426541866104821039915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103971804111642946189439773 38989426541866104821039915)
        ·
          refine ⟨58484139812799157231559873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38989426541866104821039915 58484139812799157231559873)
          ·
            refine ⟨43863104859599367923669905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58484139812799157231559873 43863104859599367923669905)
            ·
              refine ⟨32897328644699525942752429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43863104859599367923669905 32897328644699525942752429)
              ·
                refine ⟨12336498241762322228532161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32897328644699525942752429 12336498241762322228532161)
                ·
                  refine ⟨9252373681321741671399121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12336498241762322228532161 9252373681321741671399121)
                  ·
                    refine ⟨6939280260991306253549341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9252373681321741671399121 6939280260991306253549341)
                    ·
                      refine ⟨2602230097871739845081003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6939280260991306253549341 2602230097871739845081003)
                      ·
                        rfl

theorem cell23_5067825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_5067825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067825 prefixEnd_5067825 := by exact prefixLift 5067825
  have htrace : WordTrace (prefixWord ++ tailWord_5067825) baseStart_5067825 baseEnd_5067825 := by
    simpa [prefixWord, tailWord_5067825, baseEnd_5067825] using wordTrace_append hprefix tailTrace_5067825
  have hstable : (prefixWord ++ tailWord_5067825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067825).length < 2 ^ (prefixWord ++ tailWord_5067825).sum := by decide
  have hdescent : baseEnd_5067825 < baseStart_5067825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067865 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 5, 2]
def baseStart_5067865 : Nat := 118140960795 + 5067865 * 2 ^ 59
def prefixEnd_5067865 : Nat := 4983230072969 + 3 ^ 40 * 5067865 * 2
def baseEnd_5067865 : Nat := 2602250637097919688580819

theorem tailTrace_5067865 : CollatzResearch.WordTrace tailWord_5067865 prefixEnd_5067865 2602250637097919688580819 := by
  unfold tailWord_5067865
  simp only [CollatzResearch.WordTrace]
  refine ⟨184840221784998102279349049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123226814523332068186232699 184840221784998102279349049)
  ·
    refine ⟨138630166338748576709511787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184840221784998102279349049 138630166338748576709511787)
    ·
      refine ⟨207945249508122865064267681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138630166338748576709511787 207945249508122865064267681)
      ·
        refine ⟨155958937131092148798200761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207945249508122865064267681 155958937131092148798200761)
        ·
          refine ⟨116969202848319111598650571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155958937131092148798200761 116969202848319111598650571)
          ·
            refine ⟨175453804272478667397975857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116969202848319111598650571 175453804272478667397975857)
            ·
              refine ⟨131590353204359000548481893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175453804272478667397975857 131590353204359000548481893)
              ·
                refine ⟨24673191225817312602840355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131590353204359000548481893 24673191225817312602840355)
                ·
                  refine ⟨37009786838725968904260533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24673191225817312602840355 37009786838725968904260533)
                  ·
                    refine ⟨3469667516130559584774425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37009786838725968904260533 3469667516130559584774425)
                    ·
                      refine ⟨2602250637097919688580819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469667516130559584774425 2602250637097919688580819)
                      ·
                        rfl

theorem cell23_5067865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_5067865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067865 prefixEnd_5067865 := by exact prefixLift 5067865
  have htrace : WordTrace (prefixWord ++ tailWord_5067865) baseStart_5067865 baseEnd_5067865 := by
    simpa [prefixWord, tailWord_5067865, baseEnd_5067865] using wordTrace_append hprefix tailTrace_5067865
  have hstable : (prefixWord ++ tailWord_5067865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067865).length < 2 ^ (prefixWord ++ tailWord_5067865).sum := by decide
  have hdescent : baseEnd_5067865 < baseStart_5067865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067922 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5067922 : Nat := 118140960795 + 5067922 * 2 ^ 59
def prefixEnd_5067922 : Nat := 4983230072969 + 3 ^ 40 * 5067922 * 2
def baseEnd_5067922 : Nat := 867426635165075321856019

theorem tailTrace_5067922 : CollatzResearch.WordTrace tailWord_5067922 prefixEnd_5067922 867426635165075321856019 := by
  unfold tailWord_5067922
  simp only [CollatzResearch.WordTrace]
  refine ⟨46210575186447900253543505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123228200497194400676116013 46210575186447900253543505)
  ·
    refine ⟨34657931389835925190157629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46210575186447900253543505 34657931389835925190157629)
    ·
      refine ⟨12996724271188471946309111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34657931389835925190157629 12996724271188471946309111)
      ·
        refine ⟨19495086406782707919463667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12996724271188471946309111 19495086406782707919463667)
        ·
          refine ⟨29242629610174061879195501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19495086406782707919463667 29242629610174061879195501)
          ·
            refine ⟨10965986103815273204698313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29242629610174061879195501 10965986103815273204698313)
            ·
              refine ⟨8224489577861454903523735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10965986103815273204698313 8224489577861454903523735)
              ·
                refine ⟨12336734366792182355285603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224489577861454903523735 12336734366792182355285603)
                ·
                  refine ⟨18505101550188273532928405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12336734366792182355285603 18505101550188273532928405)
                  ·
                    refine ⟨867426635165075321856019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18505101550188273532928405 867426635165075321856019)
                    ·
                      rfl

theorem cell23_5067922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5067922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067922 prefixEnd_5067922 := by exact prefixLift 5067922
  have htrace : WordTrace (prefixWord ++ tailWord_5067922) baseStart_5067922 baseEnd_5067922 := by
    simpa [prefixWord, tailWord_5067922, baseEnd_5067922] using wordTrace_append hprefix tailTrace_5067922
  have hstable : (prefixWord ++ tailWord_5067922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067922).length < 2 ^ (prefixWord ++ tailWord_5067922).sum := by decide
  have hdescent : baseEnd_5067922 < baseStart_5067922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067932 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5067932 : Nat := 118140960795 + 5067932 * 2 ^ 59
def prefixEnd_5067932 : Nat := 4983230072969 + 3 ^ 40 * 5067932 * 2
def baseEnd_5067932 : Nat := 2602285040301770926443011

theorem tailTrace_5067932 : CollatzResearch.WordTrace tailWord_5067932 prefixEnd_5067932 2602285040301770926443011 := by
  unfold tailWord_5067932
  simp only [CollatzResearch.WordTrace]
  refine ⟨92421332737877686361019025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123228443650503581814692033 92421332737877686361019025)
  ·
    refine ⟨69315999553408264770764269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92421332737877686361019025 69315999553408264770764269)
    ·
      refine ⟨25993499832528099289036601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69315999553408264770764269 25993499832528099289036601)
      ·
        refine ⟨19495124874396074466777451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25993499832528099289036601 19495124874396074466777451)
        ·
          refine ⟨29242687311594111700166177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19495124874396074466777451 29242687311594111700166177)
          ·
            refine ⟨21932015483695583775124633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29242687311594111700166177 21932015483695583775124633)
            ·
              refine ⟨16449011612771687831343475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21932015483695583775124633 16449011612771687831343475)
              ·
                refine ⟨24673517419157531747015213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449011612771687831343475 24673517419157531747015213)
                ·
                  refine ⟨9252569032184074405130705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24673517419157531747015213 9252569032184074405130705)
                  ·
                    refine ⟨6939426774138055803848029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9252569032184074405130705 6939426774138055803848029)
                    ·
                      refine ⟨2602285040301770926443011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6939426774138055803848029 2602285040301770926443011)
                      ·
                        rfl

theorem cell23_5067932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5067932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067932 prefixEnd_5067932 := by exact prefixLift 5067932
  have htrace : WordTrace (prefixWord ++ tailWord_5067932) baseStart_5067932 baseEnd_5067932 := by
    simpa [prefixWord, tailWord_5067932, baseEnd_5067932] using wordTrace_append hprefix tailTrace_5067932
  have hstable : (prefixWord ++ tailWord_5067932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067932).length < 2 ^ (prefixWord ++ tailWord_5067932).sum := by decide
  have hdescent : baseEnd_5067932 < baseStart_5067932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067946 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5067946 : Nat := 118140960795 + 5067946 * 2 ^ 59
def prefixEnd_5067946 : Nat := 4983230072969 + 3 ^ 40 * 5067946 * 2
def baseEnd_5067946 : Nat := 2602292229030933871667947

theorem tailTrace_5067946 : CollatzResearch.WordTrace tailWord_5067946 prefixEnd_5067946 2602292229030933871667947 := by
  unfold tailWord_5067946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46210794024426163278261923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123228784065136435408698461 46210794024426163278261923)
  ·
    refine ⟨69316191036639244917392885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46210794024426163278261923 69316191036639244917392885)
    ·
      refine ⟨6498392909684929211005583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69316191036639244917392885 6498392909684929211005583)
      ·
        refine ⟨9747589364527393816508375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6498392909684929211005583 9747589364527393816508375)
        ·
          refine ⟨14621384046791090724762563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9747589364527393816508375 14621384046791090724762563)
          ·
            refine ⟨21932076070186636087143845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14621384046791090724762563 21932076070186636087143845)
            ·
              refine ⟨4112264263159994266339471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21932076070186636087143845 4112264263159994266339471)
              ·
                refine ⟨6168396394739991399509207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112264263159994266339471 6168396394739991399509207)
                ·
                  refine ⟨9252594592109987099263811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6168396394739991399509207 9252594592109987099263811)
                  ·
                    refine ⟨13878891888164980648895717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9252594592109987099263811 13878891888164980648895717)
                    ·
                      refine ⟨2602292229030933871667947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13878891888164980648895717 2602292229030933871667947)
                      ·
                        rfl

theorem cell23_5067946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5067946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067946 prefixEnd_5067946 := by exact prefixLift 5067946
  have htrace : WordTrace (prefixWord ++ tailWord_5067946) baseStart_5067946 baseEnd_5067946 := by
    simpa [prefixWord, tailWord_5067946, baseEnd_5067946] using wordTrace_append hprefix tailTrace_5067946
  have hstable : (prefixWord ++ tailWord_5067946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067946).length < 2 ^ (prefixWord ++ tailWord_5067946).sum := by decide
  have hdescent : baseEnd_5067946 < baseStart_5067946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067948 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_5067948 : Nat := 118140960795 + 5067948 * 2 ^ 59
def prefixEnd_5067948 : Nat := 4983230072969 + 3 ^ 40 * 5067948 * 2
def baseEnd_5067948 : Nat := 867431085330747621280979

theorem tailTrace_5067948 : CollatzResearch.WordTrace tailWord_5067948 prefixEnd_5067948 867431085330747621280979 := by
  unfold tailWord_5067948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92421624521848703727310249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123228832695798271636413665 92421624521848703727310249)
  ·
    refine ⟨69316218391386527795482687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92421624521848703727310249 69316218391386527795482687)
    ·
      refine ⟨103974327587079791693224031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69316218391386527795482687 103974327587079791693224031)
      ·
        refine ⟨155961491380619687539836047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103974327587079791693224031 155961491380619687539836047)
        ·
          refine ⟨233942237070929531309754071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155961491380619687539836047 233942237070929531309754071)
          ·
            refine ⟨350913355606394296964631107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233942237070929531309754071 350913355606394296964631107)
            ·
              refine ⟨526370033409591445446946661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350913355606394296964631107 526370033409591445446946661)
              ·
                refine ⟨98694381264298396021302499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526370033409591445446946661 98694381264298396021302499)
                ·
                  refine ⟨148041571896447594031953749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98694381264298396021302499 148041571896447594031953749)
                  ·
                    refine ⟨867431085330747621280979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 148041571896447594031953749 867431085330747621280979)
                    ·
                      rfl

theorem cell23_5067948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_5067948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067948 prefixEnd_5067948 := by exact prefixLift 5067948
  have htrace : WordTrace (prefixWord ++ tailWord_5067948) baseStart_5067948 baseEnd_5067948 := by
    simpa [prefixWord, tailWord_5067948, baseEnd_5067948] using wordTrace_append hprefix tailTrace_5067948
  have hstable : (prefixWord ++ tailWord_5067948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067948).length < 2 ^ (prefixWord ++ tailWord_5067948).sum := by decide
  have hdescent : baseEnd_5067948 < baseStart_5067948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5067997 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5067997 : Nat := 118140960795 + 5067997 * 2 ^ 59
def prefixEnd_5067997 : Nat := 4983230072969 + 3 ^ 40 * 5067997 * 2
def baseEnd_5067997 : Nat := 2602318416544313172130213

theorem tailTrace_5067997 : CollatzResearch.WordTrace tailWord_5067997 prefixEnd_5067997 2602318416544313172130213 := by
  unfold tailWord_5067997
  simp only [CollatzResearch.WordTrace]
  refine ⟨184845036220519888823154245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123230024147013259215436163 184845036220519888823154245)
  ·
    refine ⟨34658444291347479154341421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184845036220519888823154245 34658444291347479154341421)
    ·
      refine ⟨12996916609255304682878033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34658444291347479154341421 12996916609255304682878033)
      ·
        refine ⟨9747687456941478512158525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12996916609255304682878033 9747687456941478512158525)
        ·
          refine ⟨3655382796353054442059447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9747687456941478512158525 3655382796353054442059447)
          ·
            refine ⟨5483074194529581663089171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655382796353054442059447 5483074194529581663089171)
            ·
              refine ⟨8224611291794372494633757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483074194529581663089171 8224611291794372494633757)
              ·
                refine ⟨3084229234422889685487659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8224611291794372494633757 3084229234422889685487659)
                ·
                  refine ⟨4626343851634334528231489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084229234422889685487659 4626343851634334528231489)
                  ·
                    refine ⟨3469757888725750896173617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626343851634334528231489 3469757888725750896173617)
                    ·
                      refine ⟨2602318416544313172130213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469757888725750896173617 2602318416544313172130213)
                      ·
                        rfl

theorem cell23_5067997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5067997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5067997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5067997 prefixEnd_5067997 := by exact prefixLift 5067997
  have htrace : WordTrace (prefixWord ++ tailWord_5067997) baseStart_5067997 baseEnd_5067997 := by
    simpa [prefixWord, tailWord_5067997, baseEnd_5067997] using wordTrace_append hprefix tailTrace_5067997
  have hstable : (prefixWord ++ tailWord_5067997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5067997).length < 2 ^ (prefixWord ++ tailWord_5067997).sum := by decide
  have hdescent : baseEnd_5067997 < baseStart_5067997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5067997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068019 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 4, 2, 2]
def baseStart_5068019 : Nat := 118140960795 + 5068019 * 2 ^ 59
def prefixEnd_5068019 : Nat := 4983230072969 + 3 ^ 40 * 5068019 * 2
def baseEnd_5068019 : Nat := 2602329713118712086055111

theorem tailTrace_5068019 : CollatzResearch.WordTrace tailWord_5068019 prefixEnd_5068019 2602329713118712086055111 := by
  unfold tailWord_5068019
  simp only [CollatzResearch.WordTrace]
  refine ⟨184845838626440186580455111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123230559084293457720303407 184845838626440186580455111)
  ·
    refine ⟨277268757939660279870682667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184845838626440186580455111 277268757939660279870682667)
    ·
      refine ⟨415903136909490419806024001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277268757939660279870682667 415903136909490419806024001)
      ·
        refine ⟨311927352682117814854518001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415903136909490419806024001 311927352682117814854518001)
        ·
          refine ⟨233945514511588361140888501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311927352682117814854518001 233945514511588361140888501)
          ·
            refine ⟨21932391985461408856958297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233945514511588361140888501 21932391985461408856958297)
            ·
              refine ⟨16449293989096056642718723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21932391985461408856958297 16449293989096056642718723)
              ·
                refine ⟨24673940983644084964078085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449293989096056642718723 24673940983644084964078085)
                ·
                  refine ⟨4626363934433265930764641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24673940983644084964078085 4626363934433265930764641)
                  ·
                    refine ⟨3469772950824949448073481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626363934433265930764641 3469772950824949448073481)
                    ·
                      refine ⟨2602329713118712086055111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469772950824949448073481 2602329713118712086055111)
                      ·
                        rfl

theorem cell23_5068019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2, 2].length) (baseStart_5068019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068019 prefixEnd_5068019 := by exact prefixLift 5068019
  have htrace : WordTrace (prefixWord ++ tailWord_5068019) baseStart_5068019 baseEnd_5068019 := by
    simpa [prefixWord, tailWord_5068019, baseEnd_5068019] using wordTrace_append hprefix tailTrace_5068019
  have hstable : (prefixWord ++ tailWord_5068019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068019).length < 2 ^ (prefixWord ++ tailWord_5068019).sum := by decide
  have hdescent : baseEnd_5068019 < baseStart_5068019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068022 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_5068022 : Nat := 118140960795 + 5068022 * 2 ^ 59
def prefixEnd_5068022 : Nat := 4983230072969 + 3 ^ 40 * 5068022 * 2
def baseEnd_5068022 : Nat := 2602331253560675574317597

theorem tailTrace_5068022 : CollatzResearch.WordTrace tailWord_5068022 prefixEnd_5068022 2602331253560675574317597 := by
  unfold tailWord_5068022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552871752839332380800895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123230632030286212061876213 11552871752839332380800895)
  ·
    refine ⟨17329307629258998571201343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11552871752839332380800895 17329307629258998571201343)
    ·
      refine ⟨25993961443888497856802015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17329307629258998571201343 25993961443888497856802015)
      ·
        refine ⟨38990942165832746785203023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25993961443888497856802015 38990942165832746785203023)
        ·
          refine ⟨58486413248749120177804535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38990942165832746785203023 58486413248749120177804535)
          ·
            refine ⟨87729619873123680266706803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58486413248749120177804535 87729619873123680266706803)
            ·
              refine ⟨131594429809685520400060205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87729619873123680266706803 131594429809685520400060205)
              ·
                refine ⟨49347911178632070150022577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131594429809685520400060205 49347911178632070150022577)
                ·
                  refine ⟨37010933383974052612516933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49347911178632070150022577 37010933383974052612516933)
                  ·
                    refine ⟨6939550009495134864846925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37010933383974052612516933 6939550009495134864846925)
                    ·
                      refine ⟨2602331253560675574317597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6939550009495134864846925 2602331253560675574317597)
                      ·
                        rfl

theorem cell23_5068022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_5068022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068022 prefixEnd_5068022 := by exact prefixLift 5068022
  have htrace : WordTrace (prefixWord ++ tailWord_5068022) baseStart_5068022 baseEnd_5068022 := by
    simpa [prefixWord, tailWord_5068022, baseEnd_5068022] using wordTrace_append hprefix tailTrace_5068022
  have hstable : (prefixWord ++ tailWord_5068022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068022).length < 2 ^ (prefixWord ++ tailWord_5068022).sum := by decide
  have hdescent : baseEnd_5068022 < baseStart_5068022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068082 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_5068082 : Nat := 118140960795 + 5068082 * 2 ^ 59
def prefixEnd_5068082 : Nat := 4983230072969 + 3 ^ 40 * 5068082 * 2
def baseEnd_5068082 : Nat := 2602362062399945339567321

theorem tailTrace_5068082 : CollatzResearch.WordTrace tailWord_5068082 prefixEnd_5068082 2602362062399945339567321 := by
  unfold tailWord_5068082
  simp only [CollatzResearch.WordTrace]
  refine ⟨46212034106302987084999625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123232090950141298893332333 46212034106302987084999625)
  ·
    refine ⟨34659025579727240313749719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46212034106302987084999625 34659025579727240313749719)
    ·
      refine ⟨51988538369590860470624579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34659025579727240313749719 51988538369590860470624579)
      ·
        refine ⟨77982807554386290705936869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51988538369590860470624579 77982807554386290705936869)
        ·
          refine ⟨14621776416447429507363163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77982807554386290705936869 14621776416447429507363163)
          ·
            refine ⟨21932664624671144261044745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14621776416447429507363163 21932664624671144261044745)
            ·
              refine ⟨16449498468503358195783559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21932664624671144261044745 16449498468503358195783559)
              ·
                refine ⟨24674247702755037293675339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449498468503358195783559 24674247702755037293675339)
                ·
                  refine ⟨37011371554132555940513009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24674247702755037293675339 37011371554132555940513009)
                  ·
                    refine ⟨27758528665599416955384757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37011371554132555940513009 27758528665599416955384757)
                    ·
                      refine ⟨2602362062399945339567321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27758528665599416955384757 2602362062399945339567321)
                      ·
                        rfl

theorem cell23_5068082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_5068082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068082 prefixEnd_5068082 := by exact prefixLift 5068082
  have htrace : WordTrace (prefixWord ++ tailWord_5068082) baseStart_5068082 baseEnd_5068082 := by
    simpa [prefixWord, tailWord_5068082, baseEnd_5068082] using wordTrace_append hprefix tailTrace_5068082
  have hstable : (prefixWord ++ tailWord_5068082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068082).length < 2 ^ (prefixWord ++ tailWord_5068082).sum := by decide
  have hdescent : baseEnd_5068082 < baseStart_5068082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068112 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_5068112 : Nat := 118140960795 + 5068112 * 2 ^ 59
def prefixEnd_5068112 : Nat := 4983230072969 + 3 ^ 40 * 5068112 * 2
def baseEnd_5068112 : Nat := 2602377466819580222192183

theorem tailTrace_5068112 : CollatzResearch.WordTrace tailWord_5068112 prefixEnd_5068112 2602377466819580222192183 := by
  unfold tailWord_5068112
  simp only [CollatzResearch.WordTrace]
  refine ⟨92424615307551631731795295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123232820410068842309060393 92424615307551631731795295)
  ·
    refine ⟨138636922961327447597692943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92424615307551631731795295 138636922961327447597692943)
    ·
      refine ⟨207955384441991171396539415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138636922961327447597692943 207955384441991171396539415)
      ·
        refine ⟨311933076662986757094809123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207955384441991171396539415 311933076662986757094809123)
        ·
          refine ⟨467899614994480135642213685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311933076662986757094809123 467899614994480135642213685)
          ·
            refine ⟨43865588905732512716457533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 467899614994480135642213685 43865588905732512716457533)
            ·
              refine ⟨16449595839649692268671575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43865588905732512716457533 16449595839649692268671575)
              ·
                refine ⟨24674393759474538403007363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449595839649692268671575 24674393759474538403007363)
                ·
                  refine ⟨37011590639211807604511045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24674393759474538403007363 37011590639211807604511045)
                  ·
                    refine ⟨6939673244852213925845821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37011590639211807604511045 6939673244852213925845821)
                    ·
                      refine ⟨2602377466819580222192183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6939673244852213925845821 2602377466819580222192183)
                      ·
                        rfl

theorem cell23_5068112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_5068112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068112 prefixEnd_5068112 := by exact prefixLift 5068112
  have htrace : WordTrace (prefixWord ++ tailWord_5068112) baseStart_5068112 baseEnd_5068112 := by
    simpa [prefixWord, tailWord_5068112, baseEnd_5068112] using wordTrace_append hprefix tailTrace_5068112
  have hstable : (prefixWord ++ tailWord_5068112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068112).length < 2 ^ (prefixWord ++ tailWord_5068112).sum := by decide
  have hdescent : baseEnd_5068112 < baseStart_5068112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068115 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 8]
def baseStart_5068115 : Nat := 118140960795 + 5068115 * 2 ^ 59
def prefixEnd_5068115 : Nat := 4983230072969 + 3 ^ 40 * 5068115 * 2
def baseEnd_5068115 : Nat := 289153223029060412272741

theorem tailTrace_5068115 : CollatzResearch.WordTrace tailWord_5068115 prefixEnd_5068115 289153223029060412272741 := by
  unfold tailWord_5068115
  simp only [CollatzResearch.WordTrace]
  refine ⟨184849340034092394975949799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123232893356061596650633199 184849340034092394975949799)
  ·
    refine ⟨277274010051138592463924699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184849340034092394975949799 277274010051138592463924699)
    ·
      refine ⟨415911015076707888695887049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277274010051138592463924699 415911015076707888695887049)
      ·
        refine ⟨311933261307530916521915287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415911015076707888695887049 311933261307530916521915287)
        ·
          refine ⟨467899891961296374782872931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311933261307530916521915287 467899891961296374782872931)
          ·
            refine ⟨701849837941944562174309397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467899891961296374782872931 701849837941944562174309397)
            ·
              refine ⟨32899211153528651351920753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 701849837941944562174309397 32899211153528651351920753)
              ·
                refine ⟨24674408365146488513940565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32899211153528651351920753 24674408365146488513940565)
                ·
                  refine ⟨289153223029060412272741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24674408365146488513940565 289153223029060412272741)
                  ·
                    rfl

theorem cell23_5068115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 8].length) (baseStart_5068115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068115 prefixEnd_5068115 := by exact prefixLift 5068115
  have htrace : WordTrace (prefixWord ++ tailWord_5068115) baseStart_5068115 baseEnd_5068115 := by
    simpa [prefixWord, tailWord_5068115, baseEnd_5068115] using wordTrace_append hprefix tailTrace_5068115
  have hstable : (prefixWord ++ tailWord_5068115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068115).length < 2 ^ (prefixWord ++ tailWord_5068115).sum := by decide
  have hdescent : baseEnd_5068115 < baseStart_5068115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068132 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 8]
def baseStart_5068132 : Nat := 118140960795 + 5068132 * 2 ^ 59
def prefixEnd_5068132 : Nat := 4983230072969 + 3 ^ 40 * 5068132 * 2
def baseEnd_5068132 : Nat := 289154192936963349326899

theorem tailTrace_5068132 : CollatzResearch.WordTrace tailWord_5068132 prefixEnd_5068132 289154192936963349326899 := by
  unfold tailWord_5068132
  simp only [CollatzResearch.WordTrace]
  refine ⟨92424980037515403439659325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123233306716687204586212433 92424980037515403439659325)
  ·
    refine ⟨34659367514068276289872247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92424980037515403439659325 34659367514068276289872247)
    ·
      refine ⟨51989051271102414434808371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34659367514068276289872247 51989051271102414434808371)
      ·
        refine ⟨77983576906653621652212557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51989051271102414434808371 77983576906653621652212557)
        ·
          refine ⟨29243841339995108119579709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77983576906653621652212557 29243841339995108119579709)
          ·
            refine ⟨10966440502498165544842391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29243841339995108119579709 10966440502498165544842391)
            ·
              refine ⟨16449660753747248317263587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966440502498165544842391 16449660753747248317263587)
              ·
                refine ⟨24674491130620872475895381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449660753747248317263587 24674491130620872475895381)
                ·
                  refine ⟨289154192936963349326899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24674491130620872475895381 289154192936963349326899)
                  ·
                    rfl

theorem cell23_5068132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_5068132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068132 prefixEnd_5068132 := by exact prefixLift 5068132
  have htrace : WordTrace (prefixWord ++ tailWord_5068132) baseStart_5068132 baseEnd_5068132 := by
    simpa [prefixWord, tailWord_5068132, baseEnd_5068132] using wordTrace_append hprefix tailTrace_5068132
  have hstable : (prefixWord ++ tailWord_5068132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068132).length < 2 ^ (prefixWord ++ tailWord_5068132).sum := by decide
  have hdescent : baseEnd_5068132 < baseStart_5068132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068136 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5068136 : Nat := 118140960795 + 5068136 * 2 ^ 59
def prefixEnd_5068136 : Nat := 4983230072969 + 3 ^ 40 * 5068136 * 2
def baseEnd_5068136 : Nat := 867463263451762709430691

theorem tailTrace_5068136 : CollatzResearch.WordTrace tailWord_5068136 prefixEnd_5068136 867463263451762709430691 := by
  unfold tailWord_5068136
  simp only [CollatzResearch.WordTrace]
  refine ⟨92425052983508157781232131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123233403978010877041642841 92425052983508157781232131)
  ·
    refine ⟨138637579475262236671848197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92425052983508157781232131 138637579475262236671848197)
    ·
      refine ⟨25994546151611669375971537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138637579475262236671848197 25994546151611669375971537)
      ·
        refine ⟨19495909613708752031978653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25994546151611669375971537 19495909613708752031978653)
        ·
          refine ⟨7310966105140782011991995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19495909613708752031978653 7310966105140782011991995)
          ·
            refine ⟨10966449157711173017987993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7310966105140782011991995 10966449157711173017987993)
            ·
              refine ⟨8224836868283379763490995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10966449157711173017987993 8224836868283379763490995)
              ·
                refine ⟨12337255302425069645236493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224836868283379763490995 12337255302425069645236493)
                ·
                  refine ⟨4626470738409401116963685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12337255302425069645236493 4626470738409401116963685)
                  ·
                    refine ⟨867463263451762709430691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4626470738409401116963685 867463263451762709430691)
                    ·
                      rfl

theorem cell23_5068136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5068136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068136 prefixEnd_5068136 := by exact prefixLift 5068136
  have htrace : WordTrace (prefixWord ++ tailWord_5068136) baseStart_5068136 baseEnd_5068136 := by
    simpa [prefixWord, tailWord_5068136, baseEnd_5068136] using wordTrace_append hprefix tailTrace_5068136
  have hstable : (prefixWord ++ tailWord_5068136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068136).length < 2 ^ (prefixWord ++ tailWord_5068136).sum := by decide
  have hdescent : baseEnd_5068136 < baseStart_5068136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068186 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5068186 : Nat := 118140960795 + 5068186 * 2 ^ 59
def prefixEnd_5068186 : Nat := 4983230072969 + 3 ^ 40 * 5068186 * 2
def baseEnd_5068186 : Nat := 2602415464388012932666843

theorem tailTrace_5068186 : CollatzResearch.WordTrace tailWord_5068186 prefixEnd_5068186 2602415464388012932666843 := by
  unfold tailWord_5068186
  simp only [CollatzResearch.WordTrace]
  refine ⟨46212982404208793525446103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123234619744556782734522941 46212982404208793525446103)
  ·
    refine ⟨69319473606313190288169155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46212982404208793525446103 69319473606313190288169155)
    ·
      refine ⟨103979210409469785432253733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69319473606313190288169155 103979210409469785432253733)
      ·
        refine ⟨19496101951775584768547575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103979210409469785432253733 19496101951775584768547575)
        ·
          refine ⟨29244152927663377152821363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19496101951775584768547575 29244152927663377152821363)
          ·
            refine ⟨43866229391495065729232045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29244152927663377152821363 43866229391495065729232045)
            ·
              refine ⟨16449836021810649648462017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43866229391495065729232045 16449836021810649648462017)
              ·
                refine ⟨12337377016357987236346513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16449836021810649648462017 12337377016357987236346513)
                ·
                  refine ⟨9253032762268490427259885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12337377016357987236346513 9253032762268490427259885)
                  ·
                    refine ⟨3469887285850683910222457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9253032762268490427259885 3469887285850683910222457)
                    ·
                      refine ⟨2602415464388012932666843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469887285850683910222457 2602415464388012932666843)
                      ·
                        rfl

theorem cell23_5068186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5068186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068186 prefixEnd_5068186 := by exact prefixLift 5068186
  have htrace : WordTrace (prefixWord ++ tailWord_5068186) baseStart_5068186 baseEnd_5068186 := by
    simpa [prefixWord, tailWord_5068186, baseEnd_5068186] using wordTrace_append hprefix tailTrace_5068186
  have hstable : (prefixWord ++ tailWord_5068186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068186).length < 2 ^ (prefixWord ++ tailWord_5068186).sum := by decide
  have hdescent : baseEnd_5068186 < baseStart_5068186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068199 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5068199 : Nat := 118140960795 + 5068199 * 2 ^ 59
def prefixEnd_5068199 : Nat := 4983230072969 + 3 ^ 40 * 5068199 * 2
def baseEnd_5068199 : Nat := 2602422139636521381804283

theorem tailTrace_5068199 : CollatzResearch.WordTrace tailWord_5068199 prefixEnd_5068199 2602422139636521381804283 := by
  unfold tailWord_5068199
  simp only [CollatzResearch.WordTrace]
  refine ⟨184852403765788077322007651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123234935843858718214671767 184852403765788077322007651)
  ·
    refine ⟨277278605648682115983011477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184852403765788077322007651 277278605648682115983011477)
    ·
      refine ⟨12997434639781974186703663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 277278605648682115983011477 12997434639781974186703663)
      ·
        refine ⟨19496151959672961280055495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12997434639781974186703663 19496151959672961280055495)
        ·
          refine ⟨29244227939509441920083243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19496151959672961280055495 29244227939509441920083243)
          ·
            refine ⟨43866341909264162880124865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29244227939509441920083243 43866341909264162880124865)
            ·
              refine ⟨32899756431948122160093649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43866341909264162880124865 32899756431948122160093649)
              ·
                refine ⟨24674817323961091620070237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32899756431948122160093649 24674817323961091620070237)
                ·
                  refine ⟨9253056496485409357526339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24674817323961091620070237 9253056496485409357526339)
                  ·
                    refine ⟨13879584744728114036289509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9253056496485409357526339 13879584744728114036289509)
                    ·
                      refine ⟨2602422139636521381804283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13879584744728114036289509 2602422139636521381804283)
                      ·
                        rfl

theorem cell23_5068199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5068199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068199 prefixEnd_5068199 := by exact prefixLift 5068199
  have htrace : WordTrace (prefixWord ++ tailWord_5068199) baseStart_5068199 baseEnd_5068199 := by
    simpa [prefixWord, tailWord_5068199, baseEnd_5068199] using wordTrace_append hprefix tailTrace_5068199
  have hstable : (prefixWord ++ tailWord_5068199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068199).length < 2 ^ (prefixWord ++ tailWord_5068199).sum := by decide
  have hdescent : baseEnd_5068199 < baseStart_5068199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068200 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 6]
def baseStart_5068200 : Nat := 118140960795 + 5068200 * 2 ^ 59
def prefixEnd_5068200 : Nat := 4983230072969 + 3 ^ 40 * 5068200 * 2
def baseEnd_5068200 : Nat := 289158072568575097543531

theorem tailTrace_5068200 : CollatzResearch.WordTrace tailWord_5068200 prefixEnd_5068200 289158072568575097543531 := by
  unfold tailWord_5068200
  simp only [CollatzResearch.WordTrace]
  refine ⟨92426220119392227246397027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123234960159189636328529369 92426220119392227246397027)
  ·
    refine ⟨138639330179088340869595541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92426220119392227246397027 138639330179088340869595541)
    ·
      refine ⟨6498718602144765978262291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138639330179088340869595541 6498718602144765978262291)
      ·
        refine ⟨9748077903217148967393437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6498718602144765978262291 9748077903217148967393437)
        ·
          refine ⟨3655529213706430862772539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9748077903217148967393437 3655529213706430862772539)
          ·
            refine ⟨5483293820559646294158809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655529213706430862772539 5483293820559646294158809)
            ·
              refine ⟨4112470365419734720619107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483293820559646294158809 4112470365419734720619107)
              ·
                refine ⟨6168705548129602080928661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112470365419734720619107 6168705548129602080928661)
                ·
                  refine ⟨289158072568575097543531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6168705548129602080928661 289158072568575097543531)
                  ·
                    rfl

theorem cell23_5068200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 6].length) (baseStart_5068200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068200 prefixEnd_5068200 := by exact prefixLift 5068200
  have htrace : WordTrace (prefixWord ++ tailWord_5068200) baseStart_5068200 baseEnd_5068200 := by
    simpa [prefixWord, tailWord_5068200, baseEnd_5068200] using wordTrace_append hprefix tailTrace_5068200
  have hstable : (prefixWord ++ tailWord_5068200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068200).length < 2 ^ (prefixWord ++ tailWord_5068200).sum := by decide
  have hdescent : baseEnd_5068200 < baseStart_5068200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068216 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_5068216 : Nat := 118140960795 + 5068216 * 2 ^ 59
def prefixEnd_5068216 : Nat := 4983230072969 + 3 ^ 40 * 5068216 * 2
def baseEnd_5068216 : Nat := 2602430868807647815291705

theorem tailTrace_5068216 : CollatzResearch.WordTrace tailWord_5068216 prefixEnd_5068216 2602430868807647815291705 := by
  unfold tailWord_5068216
  simp only [CollatzResearch.WordTrace]
  refine ⟨92426511903363244612688251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123235349204484326150251001 92426511903363244612688251)
  ·
    refine ⟨138639767855044866919032377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92426511903363244612688251 138639767855044866919032377)
    ·
      refine ⟨103979825891283650189274283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138639767855044866919032377 103979825891283650189274283)
      ·
        refine ⟨155969738836925475283911425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103979825891283650189274283 155969738836925475283911425)
        ·
          refine ⟨116977304127694106462933569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155969738836925475283911425 116977304127694106462933569)
          ·
            refine ⟨87732978095770579847200177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116977304127694106462933569 87732978095770579847200177)
            ·
              refine ⟨65799733571827934885400133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87732978095770579847200177 65799733571827934885400133)
              ·
                refine ⟨12337450044717737791012525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65799733571827934885400133 12337450044717737791012525)
                ·
                  refine ⟨4626543766769151671629697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12337450044717737791012525 4626543766769151671629697)
                  ·
                    refine ⟨3469907825076863753722273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626543766769151671629697 3469907825076863753722273)
                    ·
                      refine ⟨2602430868807647815291705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469907825076863753722273 2602430868807647815291705)
                      ·
                        rfl

theorem cell23_5068216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_5068216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068216 prefixEnd_5068216 := by exact prefixLift 5068216
  have htrace : WordTrace (prefixWord ++ tailWord_5068216) baseStart_5068216 baseEnd_5068216 := by
    simpa [prefixWord, tailWord_5068216, baseEnd_5068216] using wordTrace_append hprefix tailTrace_5068216
  have hstable : (prefixWord ++ tailWord_5068216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068216).length < 2 ^ (prefixWord ++ tailWord_5068216).sum := by decide
  have hdescent : baseEnd_5068216 < baseStart_5068216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068233 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 1, 2, 2]
def baseStart_5068233 : Nat := 118140960795 + 5068233 * 2 ^ 59
def prefixEnd_5068233 : Nat := 4983230072969 + 3 ^ 40 * 5068233 * 2
def baseEnd_5068233 : Nat := 2602439597978774248779127

theorem tailTrace_5068233 : CollatzResearch.WordTrace tailWord_5068233 prefixEnd_5068233 2602439597978774248779127 := by
  unfold tailWord_5068233
  simp only [CollatzResearch.WordTrace]
  refine ⟨184853643847664901128745353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123235762565109934085830235 184853643847664901128745353)
  ·
    refine ⟨138640232885748675846559015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184853643847664901128745353 138640232885748675846559015)
    ·
      refine ⟨207960349328623013769838523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138640232885748675846559015 207960349328623013769838523)
      ·
        refine ⟨311940523992934520654757785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207960349328623013769838523 311940523992934520654757785)
        ·
          refine ⟨233955392994700890491068339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311940523992934520654757785 233955392994700890491068339)
          ·
            refine ⟨350933089492051335736602509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233955392994700890491068339 350933089492051335736602509)
            ·
              refine ⟨131599908559519250901225941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350933089492051335736602509 131599908559519250901225941)
              ·
                refine ⟨3084372856863732442997483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131599908559519250901225941 3084372856863732442997483)
                ·
                  refine ⟨4626559285295598664496225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084372856863732442997483 4626559285295598664496225)
                  ·
                    refine ⟨3469919463971698998372169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626559285295598664496225 3469919463971698998372169)
                    ·
                      refine ⟨2602439597978774248779127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469919463971698998372169 2602439597978774248779127)
                      ·
                        rfl

theorem cell23_5068233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 2, 2].length) (baseStart_5068233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068233 prefixEnd_5068233 := by exact prefixLift 5068233
  have htrace : WordTrace (prefixWord ++ tailWord_5068233) baseStart_5068233 baseEnd_5068233 := by
    simpa [prefixWord, tailWord_5068233, baseEnd_5068233] using wordTrace_append hprefix tailTrace_5068233
  have hstable : (prefixWord ++ tailWord_5068233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068233).length < 2 ^ (prefixWord ++ tailWord_5068233).sum := by decide
  have hdescent : baseEnd_5068233 < baseStart_5068233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068236 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5068236 : Nat := 118140960795 + 5068236 * 2 ^ 59
def prefixEnd_5068236 : Nat := 4983230072969 + 3 ^ 40 * 5068236 * 2
def baseEnd_5068236 : Nat := 2602441138420737737041613

theorem tailTrace_5068236 : CollatzResearch.WordTrace tailWord_5068236 prefixEnd_5068236 2602441138420737737041613 := by
  unfold tailWord_5068236
  simp only [CollatzResearch.WordTrace]
  refine ⟨92426876633327016320552281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123235835511102688427403041 92426876633327016320552281)
  ·
    refine ⟨69320157474995262240414211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92426876633327016320552281 69320157474995262240414211)
    ·
      refine ⟨103980236212492893360621317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69320157474995262240414211 103980236212492893360621317)
      ·
        refine ⟨19496294289842417505116497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103980236212492893360621317 19496294289842417505116497)
        ·
          refine ⟨14622220717381813128837373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19496294289842417505116497 14622220717381813128837373)
          ·
            refine ⟨5483332769018179923314015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14622220717381813128837373 5483332769018179923314015)
            ·
              refine ⟨8224999153527269884971023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483332769018179923314015 8224999153527269884971023)
              ·
                refine ⟨12337498730290904827456535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224999153527269884971023 12337498730290904827456535)
                ·
                  refine ⟨18506248095436357241184803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12337498730290904827456535 18506248095436357241184803)
                  ·
                    refine ⟨27759372143154535861777205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18506248095436357241184803 27759372143154535861777205)
                    ·
                      refine ⟨2602441138420737737041613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27759372143154535861777205 2602441138420737737041613)
                      ·
                        rfl

theorem cell23_5068236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5068236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068236 prefixEnd_5068236 := by exact prefixLift 5068236
  have htrace : WordTrace (prefixWord ++ tailWord_5068236) baseStart_5068236 baseEnd_5068236 := by
    simpa [prefixWord, tailWord_5068236, baseEnd_5068236] using wordTrace_append hprefix tailTrace_5068236
  have hstable : (prefixWord ++ tailWord_5068236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068236).length < 2 ^ (prefixWord ++ tailWord_5068236).sum := by decide
  have hdescent : baseEnd_5068236 < baseStart_5068236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068244 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5068244 : Nat := 118140960795 + 5068244 * 2 ^ 59
def prefixEnd_5068244 : Nat := 4983230072969 + 3 ^ 40 * 5068244 * 2
def baseEnd_5068244 : Nat := 2602445246265973705741577

theorem tailTrace_5068244 : CollatzResearch.WordTrace tailWord_5068244 prefixEnd_5068244 2602445246265973705741577 := by
  unfold tailWord_5068244
  simp only [CollatzResearch.WordTrace]
  refine ⟨92427022525312525003697893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123236030033750033338263857 92427022525312525003697893)
  ·
    refine ⟨17330066723496098438193355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92427022525312525003697893 17330066723496098438193355)
    ·
      refine ⟨25995100085244147657290033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17330066723496098438193355 25995100085244147657290033)
      ·
        refine ⟨19496325063933110742967525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25995100085244147657290033 19496325063933110742967525)
        ·
          refine ⟨3655560949487458264306411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19496325063933110742967525 3655560949487458264306411)
          ·
            refine ⟨5483341424231187396459617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655560949487458264306411 5483341424231187396459617)
            ·
              refine ⟨4112506068173390547344713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483341424231187396459617 4112506068173390547344713)
              ·
                refine ⟨3084379551130042910508535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112506068173390547344713 3084379551130042910508535)
                ·
                  refine ⟨4626569326695064365762803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084379551130042910508535 4626569326695064365762803)
                  ·
                    refine ⟨6939853990042596548644205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4626569326695064365762803 6939853990042596548644205)
                    ·
                      refine ⟨2602445246265973705741577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6939853990042596548644205 2602445246265973705741577)
                      ·
                        rfl

theorem cell23_5068244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5068244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068244 prefixEnd_5068244 := by exact prefixLift 5068244
  have htrace : WordTrace (prefixWord ++ tailWord_5068244) baseStart_5068244 baseEnd_5068244 := by
    simpa [prefixWord, tailWord_5068244, baseEnd_5068244] using wordTrace_append hprefix tailTrace_5068244
  have hstable : (prefixWord ++ tailWord_5068244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068244).length < 2 ^ (prefixWord ++ tailWord_5068244).sum := by decide
  have hdescent : baseEnd_5068244 < baseStart_5068244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068250 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2]
def baseStart_5068250 : Nat := 118140960795 + 5068250 * 2 ^ 59
def prefixEnd_5068250 : Nat := 4983230072969 + 3 ^ 40 * 5068250 * 2
def baseEnd_5068250 : Nat := 2602448327149900682266549

theorem tailTrace_5068250 : CollatzResearch.WordTrace tailWord_5068250 prefixEnd_5068250 2602448327149900682266549 := by
  unfold tailWord_5068250
  simp only [CollatzResearch.WordTrace]
  refine ⟨46213565972150828258028551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123236175925735542021409469 46213565972150828258028551)
  ·
    refine ⟨69320348958226242387042827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46213565972150828258028551 69320348958226242387042827)
    ·
      refine ⟨103980523437339363580564241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69320348958226242387042827 103980523437339363580564241)
      ·
        refine ⟨77985392578004522685423181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103980523437339363580564241 77985392578004522685423181)
        ·
          refine ⟨29244522216751696007033693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77985392578004522685423181 29244522216751696007033693)
          ·
            refine ⟨10966695831281886002637635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29244522216751696007033693 10966695831281886002637635)
            ·
              refine ⟨16450043746922829003956453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966695831281886002637635 16450043746922829003956453)
              ·
                refine ⟨3084383202548030438241835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16450043746922829003956453 3084383202548030438241835)
                ·
                  refine ⟨4626574803822045657362753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084383202548030438241835 4626574803822045657362753)
                  ·
                    refine ⟨3469931102866534243022065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626574803822045657362753 3469931102866534243022065)
                    ·
                      refine ⟨2602448327149900682266549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3469931102866534243022065 2602448327149900682266549)
                      ·
                        rfl

theorem cell23_5068250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_5068250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068250 prefixEnd_5068250 := by exact prefixLift 5068250
  have htrace : WordTrace (prefixWord ++ tailWord_5068250) baseStart_5068250 baseEnd_5068250 := by
    simpa [prefixWord, tailWord_5068250, baseEnd_5068250] using wordTrace_append hprefix tailTrace_5068250
  have hstable : (prefixWord ++ tailWord_5068250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068250).length < 2 ^ (prefixWord ++ tailWord_5068250).sum := by decide
  have hdescent : baseEnd_5068250 < baseStart_5068250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068282 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_5068282 : Nat := 118140960795 + 5068282 * 2 ^ 59
def prefixEnd_5068282 : Nat := 4983230072969 + 3 ^ 40 * 5068282 * 2
def baseEnd_5068282 : Nat := 867488252843614852355467

theorem tailTrace_5068282 : CollatzResearch.WordTrace tailWord_5068282 prefixEnd_5068282 867488252843614852355467 := by
  unfold tailWord_5068282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46213857756121845624319775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123236954016324921664852733 46213857756121845624319775)
  ·
    refine ⟨69320786634182768436479663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46213857756121845624319775 69320786634182768436479663)
    ·
      refine ⟨103981179951274152654719495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69320786634182768436479663 103981179951274152654719495)
      ·
        refine ⟨155971769926911228982079243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103981179951274152654719495 155971769926911228982079243)
        ·
          refine ⟨233957654890366843473118865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155971769926911228982079243 233957654890366843473118865)
          ·
            refine ⟨175468241167775132604839149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233957654890366843473118865 175468241167775132604839149)
            ·
              refine ⟨65800590437915674726814681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175468241167775132604839149 65800590437915674726814681)
              ·
                refine ⟨49350442828436756045111011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65800590437915674726814681 49350442828436756045111011)
                ·
                  refine ⟨74025664242655134067666517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49350442828436756045111011 74025664242655134067666517)
                  ·
                    refine ⟨867488252843614852355467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74025664242655134067666517 867488252843614852355467)
                    ·
                      rfl

theorem cell23_5068282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_5068282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068282 prefixEnd_5068282 := by exact prefixLift 5068282
  have htrace : WordTrace (prefixWord ++ tailWord_5068282) baseStart_5068282 baseEnd_5068282 := by
    simpa [prefixWord, tailWord_5068282, baseEnd_5068282] using wordTrace_append hprefix tailTrace_5068282
  have hstable : (prefixWord ++ tailWord_5068282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068282).length < 2 ^ (prefixWord ++ tailWord_5068282).sum := by decide
  have hdescent : baseEnd_5068282 < baseStart_5068282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068294 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5068294 : Nat := 118140960795 + 5068294 * 2 ^ 59
def prefixEnd_5068294 : Nat := 4983230072969 + 3 ^ 40 * 5068294 * 2
def baseEnd_5068294 : Nat := 867490306766232836705449

theorem tailTrace_5068294 : CollatzResearch.WordTrace tailWord_5068294 prefixEnd_5068294 867490306766232836705449 := by
  unfold tailWord_5068294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776745896888872142084873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123237245800295939031143957 5776745896888872142084873)
  ·
    refine ⟨4332559422666654106563655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5776745896888872142084873 4332559422666654106563655)
    ·
      refine ⟨6498839133999981159845483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4332559422666654106563655 6498839133999981159845483)
      ·
        refine ⟨9748258700999971739768225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6498839133999981159845483 9748258700999971739768225)
        ·
          refine ⟨7311194025749978804826169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9748258700999971739768225 7311194025749978804826169)
          ·
            refine ⟨5483395519312484103619627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311194025749978804826169 5483395519312484103619627)
            ·
              refine ⟨8225093278968726155429441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483395519312484103619627 8225093278968726155429441)
              ·
                refine ⟨6168819959226544616572081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8225093278968726155429441 6168819959226544616572081)
                ·
                  refine ⟨4626614969419908462429061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6168819959226544616572081 4626614969419908462429061)
                  ·
                    refine ⟨867490306766232836705449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4626614969419908462429061 867490306766232836705449)
                    ·
                      rfl

theorem cell23_5068294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5068294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068294 prefixEnd_5068294 := by exact prefixLift 5068294
  have htrace : WordTrace (prefixWord ++ tailWord_5068294) baseStart_5068294 baseEnd_5068294 := by
    simpa [prefixWord, tailWord_5068294, baseEnd_5068294] using wordTrace_append hprefix tailTrace_5068294
  have hstable : (prefixWord ++ tailWord_5068294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068294).length < 2 ^ (prefixWord ++ tailWord_5068294).sum := by decide
  have hdescent : baseEnd_5068294 < baseStart_5068294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068300 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_5068300 : Nat := 118140960795 + 5068300 * 2 ^ 59
def prefixEnd_5068300 : Nat := 4983230072969 + 3 ^ 40 * 5068300 * 2
def baseEnd_5068300 : Nat := 2602474001182625486641319

theorem tailTrace_5068300 : CollatzResearch.WordTrace tailWord_5068300 prefixEnd_5068300 2602474001182625486641319 := by
  unfold tailWord_5068300
  simp only [CollatzResearch.WordTrace]
  refine ⟨92428043769211085785717177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123237391692281447714289569 92428043769211085785717177)
  ·
    refine ⟨69321032826908314339287883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92428043769211085785717177 69321032826908314339287883)
    ·
      refine ⟨103981549240362471508931825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69321032826908314339287883 103981549240362471508931825)
      ·
        refine ⟨77986161930271853631698869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103981549240362471508931825 77986161930271853631698869)
        ·
          refine ⟨7311202680962986277971769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77986161930271853631698869 7311202680962986277971769)
          ·
            refine ⟨5483402010722239708478827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311202680962986277971769 5483402010722239708478827)
            ·
              refine ⟨8225103016083359562718241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483402010722239708478827 8225103016083359562718241)
              ·
                refine ⟨6168827262062519672038681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8225103016083359562718241 6168827262062519672038681)
                ·
                  refine ⟨4626620446546889754029011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6168827262062519672038681 4626620446546889754029011)
                  ·
                    refine ⟨6939930669820334631043517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4626620446546889754029011 6939930669820334631043517)
                    ·
                      refine ⟨2602474001182625486641319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6939930669820334631043517 2602474001182625486641319)
                      ·
                        rfl

theorem cell23_5068300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_5068300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068300 prefixEnd_5068300 := by exact prefixLift 5068300
  have htrace : WordTrace (prefixWord ++ tailWord_5068300) baseStart_5068300 baseEnd_5068300 := by
    simpa [prefixWord, tailWord_5068300, baseEnd_5068300] using wordTrace_append hprefix tailTrace_5068300
  have hstable : (prefixWord ++ tailWord_5068300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068300).length < 2 ^ (prefixWord ++ tailWord_5068300).sum := by decide
  have hdescent : baseEnd_5068300 < baseStart_5068300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068319 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5068319 : Nat := 118140960795 + 5068319 * 2 ^ 59
def prefixEnd_5068319 : Nat := 4983230072969 + 3 ^ 40 * 5068319 * 2
def baseEnd_5068319 : Nat := 2602483757315060912303731

theorem tailTrace_5068319 : CollatzResearch.WordTrace tailWord_5068319 prefixEnd_5068319 2602483757315060912303731 := by
  unfold tailWord_5068319
  simp only [CollatzResearch.WordTrace]
  refine ⟨184856780525353337816376011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123237853683568891877584007 184856780525353337816376011)
  ·
    refine ⟨277285170788030006724564017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184856780525353337816376011 277285170788030006724564017)
    ·
      refine ⟨207963878091022505043423013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277285170788030006724564017 207963878091022505043423013)
      ·
        refine ⟨38993227142066719695641815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207963878091022505043423013 38993227142066719695641815)
        ·
          refine ⟨58489840713100079543462723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38993227142066719695641815 58489840713100079543462723)
          ·
            refine ⟨87734761069650119315194085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58489840713100079543462723 87734761069650119315194085)
            ·
              refine ⟨16450267700559397371598891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87734761069650119315194085 16450267700559397371598891)
              ·
                refine ⟨24675401550839096057398337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16450267700559397371598891 24675401550839096057398337)
                ·
                  refine ⟨18506551163129322043048753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24675401550839096057398337 18506551163129322043048753)
                  ·
                    refine ⟨13879913372346991532286565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18506551163129322043048753 13879913372346991532286565)
                    ·
                      refine ⟨2602483757315060912303731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13879913372346991532286565 2602483757315060912303731)
                      ·
                        rfl

theorem cell23_5068319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5068319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068319 prefixEnd_5068319 := by exact prefixLift 5068319
  have htrace : WordTrace (prefixWord ++ tailWord_5068319) baseStart_5068319 baseEnd_5068319 := by
    simpa [prefixWord, tailWord_5068319, baseEnd_5068319] using wordTrace_append hprefix tailTrace_5068319
  have hstable : (prefixWord ++ tailWord_5068319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068319).length < 2 ^ (prefixWord ++ tailWord_5068319).sum := by decide
  have hdescent : baseEnd_5068319 < baseStart_5068319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068366 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_5068366 : Nat := 118140960795 + 5068366 * 2 ^ 59
def prefixEnd_5068366 : Nat := 4983230072969 + 3 ^ 40 * 5068366 * 2
def baseEnd_5068366 : Nat := 2602507890905822228416015

theorem tailTrace_5068366 : CollatzResearch.WordTrace tailWord_5068366 prefixEnd_5068366 2602507890905822228416015 := by
  unfold tailWord_5068366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23107311844522883105417119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123238996504122043228891301 23107311844522883105417119)
  ·
    refine ⟨34660967766784324658125679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23107311844522883105417119 34660967766784324658125679)
    ·
      refine ⟨51991451650176486987188519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34660967766784324658125679 51991451650176486987188519)
      ·
        refine ⟨77987177475264730480782779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51991451650176486987188519 77987177475264730480782779)
        ·
          refine ⟨116980766212897095721174169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77987177475264730480782779 116980766212897095721174169)
          ·
            refine ⟨87735574659672821790880627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116980766212897095721174169 87735574659672821790880627)
            ·
              refine ⟨131603361989509232686320941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87735574659672821790880627 131603361989509232686320941)
              ·
                refine ⟨49351260746065962257370353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131603361989509232686320941 49351260746065962257370353)
                ·
                  refine ⟨37013445559549471693027765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49351260746065962257370353 37013445559549471693027765)
                  ·
                    refine ⟨3470010521207762971221353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37013445559549471693027765 3470010521207762971221353)
                    ·
                      refine ⟨2602507890905822228416015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470010521207762971221353 2602507890905822228416015)
                      ·
                        rfl

theorem cell23_5068366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_5068366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068366 prefixEnd_5068366 := by exact prefixLift 5068366
  have htrace : WordTrace (prefixWord ++ tailWord_5068366) baseStart_5068366 baseEnd_5068366 := by
    simpa [prefixWord, tailWord_5068366, baseEnd_5068366] using wordTrace_append hprefix tailTrace_5068366
  have hstable : (prefixWord ++ tailWord_5068366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068366).length < 2 ^ (prefixWord ++ tailWord_5068366).sum := by decide
  have hdescent : baseEnd_5068366 < baseStart_5068366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068369 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_5068369 : Nat := 118140960795 + 5068369 * 2 ^ 59
def prefixEnd_5068369 : Nat := 4983230072969 + 3 ^ 40 * 5068369 * 2
def baseEnd_5068369 : Nat := 2602509431347785716678501

theorem tailTrace_5068369 : CollatzResearch.WordTrace tailWord_5068369 prefixEnd_5068369 2602509431347785716678501 := by
  unfold tailWord_5068369
  simp only [CollatzResearch.WordTrace]
  refine ⟨184858604175172196355696161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123239069450114797570464107 184858604175172196355696161)
  ·
    refine ⟨138643953131379147266772121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184858604175172196355696161 138643953131379147266772121)
    ·
      refine ⟨103982964848534360450079091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138643953131379147266772121 103982964848534360450079091)
      ·
        refine ⟨155974447272801540675118637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103982964848534360450079091 155974447272801540675118637)
        ·
          refine ⟨58490417727300577753169489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155974447272801540675118637 58490417727300577753169489)
          ·
            refine ⟨43867813295475433314877117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58490417727300577753169489 43867813295475433314877117)
            ·
              refine ⟨16450429985803287493078919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43867813295475433314877117 16450429985803287493078919)
              ·
                refine ⟨24675644978704931239618379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16450429985803287493078919 24675644978704931239618379)
                ·
                  refine ⟨37013467468057396859427569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24675644978704931239618379 37013467468057396859427569)
                  ·
                    refine ⟨27760100601043047644570677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37013467468057396859427569 27760100601043047644570677)
                    ·
                      refine ⟨2602509431347785716678501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27760100601043047644570677 2602509431347785716678501)
                      ·
                        rfl

theorem cell23_5068369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_5068369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068369 prefixEnd_5068369 := by exact prefixLift 5068369
  have htrace : WordTrace (prefixWord ++ tailWord_5068369) baseStart_5068369 baseEnd_5068369 := by
    simpa [prefixWord, tailWord_5068369, baseEnd_5068369] using wordTrace_append hprefix tailTrace_5068369
  have hstable : (prefixWord ++ tailWord_5068369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068369).length < 2 ^ (prefixWord ++ tailWord_5068369).sum := by decide
  have hdescent : baseEnd_5068369 < baseStart_5068369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068396 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_5068396 : Nat := 118140960795 + 5068396 * 2 ^ 59
def prefixEnd_5068396 : Nat := 4983230072969 + 3 ^ 40 * 5068396 * 2
def baseEnd_5068396 : Nat := 2602523295325457111040877

theorem tailTrace_5068396 : CollatzResearch.WordTrace tailWord_5068396 prefixEnd_5068396 2602523295325457111040877 := by
  unfold tailWord_5068396
  simp only [CollatzResearch.WordTrace]
  refine ⟨92429794473037189983464521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123239725964049586644619361 92429794473037189983464521)
  ·
    refine ⟨69322345854777892487598391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92429794473037189983464521 69322345854777892487598391)
    ·
      refine ⟨103983518782166838731397587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69322345854777892487598391 103983518782166838731397587)
      ·
        refine ⟨155975278173250258097096381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103983518782166838731397587 155975278173250258097096381)
        ·
          refine ⟨58490729314968846786411143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155975278173250258097096381 58490729314968846786411143)
          ·
            refine ⟨87736093972453270179616715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58490729314968846786411143 87736093972453270179616715)
            ·
              refine ⟨131604140958679905269425073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87736093972453270179616715 131604140958679905269425073)
              ·
                refine ⟨98703105719009928952068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131604140958679905269425073 98703105719009928952068805)
                ·
                  refine ⟨18506832322314361678512901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98703105719009928952068805 18506832322314361678512901)
                  ·
                    refine ⟨3470031060433942814721169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18506832322314361678512901 3470031060433942814721169)
                    ·
                      refine ⟨2602523295325457111040877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470031060433942814721169 2602523295325457111040877)
                      ·
                        rfl

theorem cell23_5068396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_5068396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068396 prefixEnd_5068396 := by exact prefixLift 5068396
  have htrace : WordTrace (prefixWord ++ tailWord_5068396) baseStart_5068396 baseEnd_5068396 := by
    simpa [prefixWord, tailWord_5068396, baseEnd_5068396] using wordTrace_append hprefix tailTrace_5068396
  have hstable : (prefixWord ++ tailWord_5068396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068396).length < 2 ^ (prefixWord ++ tailWord_5068396).sum := by decide
  have hdescent : baseEnd_5068396 < baseStart_5068396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068409 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_5068409 : Nat := 118140960795 + 5068409 * 2 ^ 59
def prefixEnd_5068409 : Nat := 4983230072969 + 3 ^ 40 * 5068409 * 2
def baseEnd_5068409 : Nat := 2602529970573965560178317

theorem tailTrace_5068409 : CollatzResearch.WordTrace tailWord_5068409 prefixEnd_5068409 2602529970573965560178317 := by
  unfold tailWord_5068409
  simp only [CollatzResearch.WordTrace]
  refine ⟨184860063095027283187152281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123240042063351522124768187 184860063095027283187152281)
  ·
    refine ⟨138645047321270462390364211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184860063095027283187152281 138645047321270462390364211)
    ·
      refine ⟨207967570981905693585546317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138645047321270462390364211 207967570981905693585546317)
      ·
        refine ⟨77987839118214635094579869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207967570981905693585546317 77987839118214635094579869)
        ·
          refine ⟨29245439669330488160467451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77987839118214635094579869 29245439669330488160467451)
          ·
            refine ⟨43868159503995732240701177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29245439669330488160467451 43868159503995732240701177)
            ·
              refine ⟨32901119627996799180525883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43868159503995732240701177 32901119627996799180525883)
              ·
                refine ⟨49351679441995198770788825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32901119627996799180525883 49351679441995198770788825)
                ·
                  refine ⟨37013759581496399078091619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49351679441995198770788825 37013759581496399078091619)
                  ·
                    refine ⟨55520639372244598617137429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37013759581496399078091619 55520639372244598617137429)
                    ·
                      refine ⟨2602529970573965560178317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55520639372244598617137429 2602529970573965560178317)
                      ·
                        rfl

theorem cell23_5068409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_5068409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068409 prefixEnd_5068409 := by exact prefixLift 5068409
  have htrace : WordTrace (prefixWord ++ tailWord_5068409) baseStart_5068409 baseEnd_5068409 := by
    simpa [prefixWord, tailWord_5068409, baseEnd_5068409] using wordTrace_append hprefix tailTrace_5068409
  have hstable : (prefixWord ++ tailWord_5068409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068409).length < 2 ^ (prefixWord ++ tailWord_5068409).sum := by decide
  have hdescent : baseEnd_5068409 < baseStart_5068409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068416 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_5068416 : Nat := 118140960795 + 5068416 * 2 ^ 59
def prefixEnd_5068416 : Nat := 4983230072969 + 3 ^ 40 * 5068416 * 2
def baseEnd_5068416 : Nat := 2602533564938547032790785

theorem tailTrace_5068416 : CollatzResearch.WordTrace tailWord_5068416 prefixEnd_5068416 2602533564938547032790785 := by
  unfold tailWord_5068416
  simp only [CollatzResearch.WordTrace]
  refine ⟨92430159203000961691328551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123240212270667948921771401 92430159203000961691328551)
  ·
    refine ⟨138645238804501442536992827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92430159203000961691328551 138645238804501442536992827)
    ·
      refine ⟨207967858206752163805489241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138645238804501442536992827 207967858206752163805489241)
      ·
        refine ⟨155975893655064122854116931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207967858206752163805489241 155975893655064122854116931)
        ·
          refine ⟨233963840482596184281175397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155975893655064122854116931 233963840482596184281175397)
          ·
            refine ⟨43868220090486784552720387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233963840482596184281175397 43868220090486784552720387)
            ·
              refine ⟨65802330135730176829080581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43868220090486784552720387 65802330135730176829080581)
              ·
                refine ⟨12337936900449408155452609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65802330135730176829080581 12337936900449408155452609)
                ·
                  refine ⟨9253452675337056116589457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12337936900449408155452609 9253452675337056116589457)
                  ·
                    refine ⟨6940089506502792087442093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9253452675337056116589457 6940089506502792087442093)
                    ·
                      refine ⟨2602533564938547032790785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6940089506502792087442093 2602533564938547032790785)
                      ·
                        rfl

theorem cell23_5068416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_5068416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068416 prefixEnd_5068416 := by exact prefixLift 5068416
  have htrace : WordTrace (prefixWord ++ tailWord_5068416) baseStart_5068416 baseEnd_5068416 := by
    simpa [prefixWord, tailWord_5068416, baseEnd_5068416] using wordTrace_append hprefix tailTrace_5068416
  have hstable : (prefixWord ++ tailWord_5068416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068416).length < 2 ^ (prefixWord ++ tailWord_5068416).sum := by decide
  have hdescent : baseEnd_5068416 < baseStart_5068416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068447 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5068447 : Nat := 118140960795 + 5068447 * 2 ^ 59
def prefixEnd_5068447 : Nat := 4983230072969 + 3 ^ 40 * 5068447 * 2
def baseEnd_5068447 : Nat := 2602549482838836411503143

theorem tailTrace_5068447 : CollatzResearch.WordTrace tailWord_5068447 prefixEnd_5068447 2602549482838836411503143 := by
  unfold tailWord_5068447
  simp only [CollatzResearch.WordTrace]
  refine ⟨184861449068889615677035595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123240966045926410451357063 184861449068889615677035595)
  ·
    refine ⟨277292173603334423515553393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184861449068889615677035595 277292173603334423515553393)
    ·
      refine ⟨207969130202500817636665045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277292173603334423515553393 207969130202500817636665045)
      ·
        refine ⟨4874276489121112913359337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 207969130202500817636665045 4874276489121112913359337)
        ·
          refine ⟨3655707366840834685019503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4874276489121112913359337 3655707366840834685019503)
          ·
            refine ⟨5483561050261252027529255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655707366840834685019503 5483561050261252027529255)
            ·
              refine ⟨8225341575391878041293883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483561050261252027529255 8225341575391878041293883)
              ·
                refine ⟨12338012363087817061940825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8225341575391878041293883 12338012363087817061940825)
                ·
                  refine ⟨9253509272315862796455619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12338012363087817061940825 9253509272315862796455619)
                  ·
                    refine ⟨13880263908473794194683429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9253509272315862796455619 13880263908473794194683429)
                    ·
                      refine ⟨2602549482838836411503143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13880263908473794194683429 2602549482838836411503143)
                      ·
                        rfl

theorem cell23_5068447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5068447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068447 prefixEnd_5068447 := by exact prefixLift 5068447
  have htrace : WordTrace (prefixWord ++ tailWord_5068447) baseStart_5068447 baseEnd_5068447 := by
    simpa [prefixWord, tailWord_5068447, baseEnd_5068447] using wordTrace_append hprefix tailTrace_5068447
  have hstable : (prefixWord ++ tailWord_5068447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068447).length < 2 ^ (prefixWord ++ tailWord_5068447).sum := by decide
  have hdescent : baseEnd_5068447 < baseStart_5068447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068450 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5068450 : Nat := 118140960795 + 5068450 * 2 ^ 59
def prefixEnd_5068450 : Nat := 4983230072969 + 3 ^ 40 * 5068450 * 2
def baseEnd_5068450 : Nat := 2602551023280799899765629

theorem tailTrace_5068450 : CollatzResearch.WordTrace tailWord_5068450 prefixEnd_5068450 2602551023280799899765629 := by
  unfold tailWord_5068450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46215389621969686797348701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123241038991919164792929869 46215389621969686797348701)
  ·
    refine ⟨17330771108238632549005763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46215389621969686797348701 17330771108238632549005763)
    ·
      refine ⟨25996156662357948823508645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17330771108238632549005763 25996156662357948823508645)
      ·
        refine ⟨4874279374192115404407871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25996156662357948823508645 4874279374192115404407871)
        ·
          refine ⟨7311419061288173106611807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874279374192115404407871 7311419061288173106611807)
          ·
            refine ⟨10967128591932259659917711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311419061288173106611807 10967128591932259659917711)
            ·
              refine ⟨16450692887898389489876567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967128591932259659917711 16450692887898389489876567)
              ·
                refine ⟨24676039331847584234814851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16450692887898389489876567 24676039331847584234814851)
                ·
                  refine ⟨37014058997771376352222277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24676039331847584234814851 37014058997771376352222277)
                  ·
                    refine ⟨6940136062082133066041677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37014058997771376352222277 6940136062082133066041677)
                    ·
                      refine ⟨2602551023280799899765629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6940136062082133066041677 2602551023280799899765629)
                      ·
                        rfl

theorem cell23_5068450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5068450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068450 prefixEnd_5068450 := by exact prefixLift 5068450
  have htrace : WordTrace (prefixWord ++ tailWord_5068450) baseStart_5068450 baseEnd_5068450 := by
    simpa [prefixWord, tailWord_5068450, baseEnd_5068450] using wordTrace_append hprefix tailTrace_5068450
  have hstable : (prefixWord ++ tailWord_5068450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068450).length < 2 ^ (prefixWord ++ tailWord_5068450).sum := by decide
  have hdescent : baseEnd_5068450 < baseStart_5068450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068470 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_5068470 : Nat := 118140960795 + 5068470 * 2 ^ 59
def prefixEnd_5068470 : Nat := 4983230072969 + 3 ^ 40 * 5068470 * 2
def baseEnd_5068470 : Nat := 289173476988209980168393

theorem tailTrace_5068470 : CollatzResearch.WordTrace tailWord_5068470 prefixEnd_5068470 289173476988209980168393 := by
  unfold tailWord_5068470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553892996737893162820179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123241525298537527070081909 11553892996737893162820179)
  ·
    refine ⟨17330839495106839744230269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11553892996737893162820179 17330839495106839744230269)
    ·
      refine ⟨6499064810665064904086351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17330839495106839744230269 6499064810665064904086351)
      ·
        refine ⟨9748597215997597356129527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6499064810665064904086351 9748597215997597356129527)
        ·
          refine ⟨14622895823996396034194291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748597215997597356129527 14622895823996396034194291)
          ·
            refine ⟨21934343735994594051291437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14622895823996396034194291 21934343735994594051291437)
            ·
              refine ⟨8225378900997972769234289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21934343735994594051291437 8225378900997972769234289)
              ·
                refine ⟨6169034175748479576925717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8225378900997972769234289 6169034175748479576925717)
                ·
                  refine ⟨289173476988209980168393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169034175748479576925717 289173476988209980168393)
                  ·
                    rfl

theorem cell23_5068470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_5068470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068470 prefixEnd_5068470 := by exact prefixLift 5068470
  have htrace : WordTrace (prefixWord ++ tailWord_5068470) baseStart_5068470 baseEnd_5068470 := by
    simpa [prefixWord, tailWord_5068470, baseEnd_5068470] using wordTrace_append hprefix tailTrace_5068470
  have hstable : (prefixWord ++ tailWord_5068470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068470).length < 2 ^ (prefixWord ++ tailWord_5068470).sum := by decide
  have hdescent : baseEnd_5068470 < baseStart_5068470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068473 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5068473 : Nat := 118140960795 + 5068473 * 2 ^ 59
def prefixEnd_5068473 : Nat := 4983230072969 + 3 ^ 40 * 5068473 * 2
def baseEnd_5068473 : Nat := 2602562833335853309778023

theorem tailTrace_5068473 : CollatzResearch.WordTrace tailWord_5068473 prefixEnd_5068473 2602562833335853309778023 := by
  unfold tailWord_5068473
  simp only [CollatzResearch.WordTrace]
  refine ⟨184862397366795422117482073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123241598244530281411654715 184862397366795422117482073)
  ·
    refine ⟨138646798025096566588111555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184862397366795422117482073 138646798025096566588111555)
    ·
      refine ⟨207970197037644849882167333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138646798025096566588111555 207970197037644849882167333)
      ·
        refine ⟨38994411944558409352906375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207970197037644849882167333 38994411944558409352906375)
        ·
          refine ⟨58491617916837614029359563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38994411944558409352906375 58491617916837614029359563)
          ·
            refine ⟨87737426875256421044039345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58491617916837614029359563 87737426875256421044039345)
            ·
              refine ⟨65803070156442315783029509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87737426875256421044039345 65803070156442315783029509)
              ·
                refine ⟨12338075654332934209318033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65803070156442315783029509 12338075654332934209318033)
                ·
                  refine ⟨9253556740749700656988525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12338075654332934209318033 9253556740749700656988525)
                  ·
                    refine ⟨3470083777781137746370697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9253556740749700656988525 3470083777781137746370697)
                    ·
                      refine ⟨2602562833335853309778023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470083777781137746370697 2602562833335853309778023)
                      ·
                        rfl

theorem cell23_5068473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5068473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068473 prefixEnd_5068473 := by exact prefixLift 5068473
  have htrace : WordTrace (prefixWord ++ tailWord_5068473) baseStart_5068473 baseEnd_5068473 := by
    simpa [prefixWord, tailWord_5068473, baseEnd_5068473] using wordTrace_append hprefix tailTrace_5068473
  have hstable : (prefixWord ++ tailWord_5068473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068473).length < 2 ^ (prefixWord ++ tailWord_5068473).sum := by decide
  have hdescent : baseEnd_5068473 < baseStart_5068473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068480 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 1, 1, 3]
def baseStart_5068480 : Nat := 118140960795 + 5068480 * 2 ^ 59
def prefixEnd_5068480 : Nat := 4983230072969 + 3 ^ 40 * 5068480 * 2
def baseEnd_5068480 : Nat := 2602566427700434782390491

theorem tailTrace_5068480 : CollatzResearch.WordTrace tailWord_5068480 prefixEnd_5068480 2602566427700434782390491 := by
  unfold tailWord_5068480
  simp only [CollatzResearch.WordTrace]
  refine ⟨92431326338885031156493447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123241768451846708208657929 92431326338885031156493447)
  ·
    refine ⟨138646989508327546734740171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92431326338885031156493447 138646989508327546734740171)
    ·
      refine ⟨207970484262491320102110257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138646989508327546734740171 207970484262491320102110257)
      ·
        refine ⟨155977863196868490076582693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207970484262491320102110257 155977863196868490076582693)
        ·
          refine ⟨29245849349412841889359255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155977863196868490076582693 29245849349412841889359255)
          ·
            refine ⟨43868774024119262834038883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29245849349412841889359255 43868774024119262834038883)
            ·
              refine ⟨65803161036178894251058325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43868774024119262834038883 65803161036178894251058325)
              ·
                refine ⟨3084523173570885668018359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65803161036178894251058325 3084523173570885668018359)
                ·
                  refine ⟨4626784760356328502027539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084523173570885668018359 4626784760356328502027539)
                  ·
                    refine ⟨6940177140534492753041309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4626784760356328502027539 6940177140534492753041309)
                    ·
                      refine ⟨2602566427700434782390491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6940177140534492753041309 2602566427700434782390491)
                      ·
                        rfl

theorem cell23_5068480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_5068480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068480 prefixEnd_5068480 := by exact prefixLift 5068480
  have htrace : WordTrace (prefixWord ++ tailWord_5068480) baseStart_5068480 baseEnd_5068480 := by
    simpa [prefixWord, tailWord_5068480, baseEnd_5068480] using wordTrace_append hprefix tailTrace_5068480
  have hstable : (prefixWord ++ tailWord_5068480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068480).length < 2 ^ (prefixWord ++ tailWord_5068480).sum := by decide
  have hdescent : baseEnd_5068480 < baseStart_5068480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068500 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5068500 : Nat := 118140960795 + 5068500 * 2 ^ 59
def prefixEnd_5068500 : Nat := 4983230072969 + 3 ^ 40 * 5068500 * 2
def baseEnd_5068500 : Nat := 867525565771174901380133

theorem tailTrace_5068500 : CollatzResearch.WordTrace tailWord_5068500 prefixEnd_5068500 867525565771174901380133 := by
  unfold tailWord_5068500
  simp only [CollatzResearch.WordTrace]
  refine ⟨92431691068848802864357477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123242254758465070485809969 92431691068848802864357477)
  ·
    refine ⟨17330942075409150537067027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92431691068848802864357477 17330942075409150537067027)
    ·
      refine ⟨25996413113113725805600541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17330942075409150537067027 25996413113113725805600541)
      ·
        refine ⟨9748654917417647177100203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25996413113113725805600541 9748654917417647177100203)
        ·
          refine ⟨14622982376126470765650305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748654917417647177100203 14622982376126470765650305)
          ·
            refine ⟨10967236782094853074237729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14622982376126470765650305 10967236782094853074237729)
            ·
              refine ⟨8225427586571139805678297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10967236782094853074237729 8225427586571139805678297)
              ·
                refine ⟨6169070689928354854258723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8225427586571139805678297 6169070689928354854258723)
                ·
                  refine ⟨9253606034892532281388085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169070689928354854258723 9253606034892532281388085)
                  ·
                    refine ⟨867525565771174901380133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9253606034892532281388085 867525565771174901380133)
                    ·
                      rfl

theorem cell23_5068500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5068500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068500 prefixEnd_5068500 := by exact prefixLift 5068500
  have htrace : WordTrace (prefixWord ++ tailWord_5068500) baseStart_5068500 baseEnd_5068500 := by
    simpa [prefixWord, tailWord_5068500, baseEnd_5068500] using wordTrace_append hprefix tailTrace_5068500
  have hstable : (prefixWord ++ tailWord_5068500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068500).length < 2 ^ (prefixWord ++ tailWord_5068500).sum := by decide
  have hdescent : baseEnd_5068500 < baseStart_5068500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068503 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_5068503 : Nat := 118140960795 + 5068503 * 2 ^ 59
def prefixEnd_5068503 : Nat := 4983230072969 + 3 ^ 40 * 5068503 * 2
def baseEnd_5068503 : Nat := 2602578237755488192402885

theorem tailTrace_5068503 : CollatzResearch.WordTrace tailWord_5068503 prefixEnd_5068503 2602578237755488192402885 := by
  unfold tailWord_5068503
  simp only [CollatzResearch.WordTrace]
  refine ⟨184863491556686737241074163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123242327704457824827382775 184863491556686737241074163)
  ·
    refine ⟨277295237335030105861611245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184863491556686737241074163 277295237335030105861611245)
    ·
      refine ⟨103985714000636289698104217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277295237335030105861611245 103985714000636289698104217)
      ·
        refine ⟨77989285500477217273578163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103985714000636289698104217 77989285500477217273578163)
        ·
          refine ⟨116983928250715825910367245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77989285500477217273578163 116983928250715825910367245)
          ·
            refine ⟨43868973094018434716387717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116983928250715825910367245 43868973094018434716387717)
            ·
              refine ⟨8225432455128456509322697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43868973094018434716387717 8225432455128456509322697)
              ·
                refine ⟨6169074341346342381992023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8225432455128456509322697 6169074341346342381992023)
                ·
                  refine ⟨9253611512019513572988035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169074341346342381992023 9253611512019513572988035)
                  ·
                    refine ⟨13880417268029270359482053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9253611512019513572988035 13880417268029270359482053)
                    ·
                      refine ⟨2602578237755488192402885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13880417268029270359482053 2602578237755488192402885)
                      ·
                        rfl

theorem cell23_5068503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_5068503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068503 prefixEnd_5068503 := by exact prefixLift 5068503
  have htrace : WordTrace (prefixWord ++ tailWord_5068503) baseStart_5068503 baseEnd_5068503 := by
    simpa [prefixWord, tailWord_5068503, baseEnd_5068503] using wordTrace_append hprefix tailTrace_5068503
  have hstable : (prefixWord ++ tailWord_5068503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068503).length < 2 ^ (prefixWord ++ tailWord_5068503).sum := by decide
  have hdescent : baseEnd_5068503 < baseStart_5068503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068516 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_5068516 : Nat := 118140960795 + 5068516 * 2 ^ 59
def prefixEnd_5068516 : Nat := 4983230072969 + 3 ^ 40 * 5068516 * 2
def baseEnd_5068516 : Nat := 2602584913003996641540325

theorem tailTrace_5068516 : CollatzResearch.WordTrace tailWord_5068516 prefixEnd_5068516 2602584913003996641540325 := by
  unfold tailWord_5068516
  simp only [CollatzResearch.WordTrace]
  refine ⟨92431982852819820230648701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123242643803759760307531601 92431982852819820230648701)
  ·
    refine ⟨34661993569807432586493263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92431982852819820230648701 34661993569807432586493263)
    ·
      refine ⟨51992990354711148879739895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34661993569807432586493263 51992990354711148879739895)
      ·
        refine ⟨77989485532066723319609843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51992990354711148879739895 77989485532066723319609843)
        ·
          refine ⟨116984228298100084979414765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77989485532066723319609843 116984228298100084979414765)
          ·
            refine ⟨43869085611787531867280537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116984228298100084979414765 43869085611787531867280537)
            ·
              refine ⟨32901814208840648900460403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43869085611787531867280537 32901814208840648900460403)
              ·
                refine ⟨49352721313260973350690605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32901814208840648900460403 49352721313260973350690605)
                ·
                  refine ⟨18507270492472865006508977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49352721313260973350690605 18507270492472865006508977)
                  ·
                    refine ⟨13880452869354648754881733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18507270492472865006508977 13880452869354648754881733)
                    ·
                      refine ⟨2602584913003996641540325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13880452869354648754881733 2602584913003996641540325)
                      ·
                        rfl

theorem cell23_5068516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_5068516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068516 prefixEnd_5068516 := by exact prefixLift 5068516
  have htrace : WordTrace (prefixWord ++ tailWord_5068516) baseStart_5068516 baseEnd_5068516 := by
    simpa [prefixWord, tailWord_5068516, baseEnd_5068516] using wordTrace_append hprefix tailTrace_5068516
  have hstable : (prefixWord ++ tailWord_5068516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068516).length < 2 ^ (prefixWord ++ tailWord_5068516).sum := by decide
  have hdescent : baseEnd_5068516 < baseStart_5068516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068523 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 3]
def baseStart_5068523 : Nat := 118140960795 + 5068523 * 2 ^ 59
def prefixEnd_5068523 : Nat := 4983230072969 + 3 ^ 40 * 5068523 * 2
def baseEnd_5068523 : Nat := 2602588507368578114152793

theorem tailTrace_5068523 : CollatzResearch.WordTrace tailWord_5068523 prefixEnd_5068523 2602588507368578114152793 := by
  unfold tailWord_5068523
  simp only [CollatzResearch.WordTrace]
  refine ⟨184864221016614280656802223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123242814011076187104534815 184864221016614280656802223)
  ·
    refine ⟨277296331524921420985203335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184864221016614280656802223 277296331524921420985203335)
    ·
      refine ⟨415944497287382131477805003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277296331524921420985203335 415944497287382131477805003)
      ·
        refine ⟨623916745931073197216707505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415944497287382131477805003 623916745931073197216707505)
        ·
          refine ⟨467937559448304897912530629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623916745931073197216707505 467937559448304897912530629)
          ·
            refine ⟨87738292396557168358599493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 467937559448304897912530629 87738292396557168358599493)
            ·
              refine ⟨16450929824354469067237405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87738292396557168358599493 16450929824354469067237405)
              ·
                refine ⟨6169098684132925900214027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16450929824354469067237405 6169098684132925900214027)
                ·
                  refine ⟨9253648026199388850321041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169098684132925900214027 9253648026199388850321041)
                  ·
                    refine ⟨6940236019649541637740781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9253648026199388850321041 6940236019649541637740781)
                    ·
                      refine ⟨2602588507368578114152793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6940236019649541637740781 2602588507368578114152793)
                      ·
                        rfl

theorem cell23_5068523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 3].length) (baseStart_5068523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068523 prefixEnd_5068523 := by exact prefixLift 5068523
  have htrace : WordTrace (prefixWord ++ tailWord_5068523) baseStart_5068523 baseEnd_5068523 := by
    simpa [prefixWord, tailWord_5068523, baseEnd_5068523] using wordTrace_append hprefix tailTrace_5068523
  have hstable : (prefixWord ++ tailWord_5068523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068523).length < 2 ^ (prefixWord ++ tailWord_5068523).sum := by decide
  have hdescent : baseEnd_5068523 < baseStart_5068523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068536 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_5068536 : Nat := 118140960795 + 5068536 * 2 ^ 59
def prefixEnd_5068536 : Nat := 4983230072969 + 3 ^ 40 * 5068536 * 2
def baseEnd_5068536 : Nat := 2602595182617086563290233

theorem tailTrace_5068536 : CollatzResearch.WordTrace tailWord_5068536 prefixEnd_5068536 2602595182617086563290233 := by
  unfold tailWord_5068536
  simp only [CollatzResearch.WordTrace]
  refine ⟨92432347582783591938512731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123243130110378122584683641 92432347582783591938512731)
  ·
    refine ⟨138648521374175387907769097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92432347582783591938512731 138648521374175387907769097)
    ·
      refine ⟨103986391030631540930826823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138648521374175387907769097 103986391030631540930826823)
      ·
        refine ⟨155979586545947311396240235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103986391030631540930826823 155979586545947311396240235)
        ·
          refine ⟨233969379818920967094360353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155979586545947311396240235 233969379818920967094360353)
          ·
            refine ⟨175477034864190725320770265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233969379818920967094360353 175477034864190725320770265)
            ·
              refine ⟨131607776148143043990577699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175477034864190725320770265 131607776148143043990577699)
              ·
                refine ⟨197411664222214565985866549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131607776148143043990577699 197411664222214565985866549)
                ·
                  refine ⟨18507343520832615561174989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197411664222214565985866549 18507343520832615561174989)
                  ·
                    refine ⟨6940253820312230835440621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18507343520832615561174989 6940253820312230835440621)
                    ·
                      refine ⟨2602595182617086563290233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6940253820312230835440621 2602595182617086563290233)
                      ·
                        rfl

theorem cell23_5068536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_5068536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068536 prefixEnd_5068536 := by exact prefixLift 5068536
  have htrace : WordTrace (prefixWord ++ tailWord_5068536) baseStart_5068536 baseEnd_5068536 := by
    simpa [prefixWord, tailWord_5068536, baseEnd_5068536] using wordTrace_append hprefix tailTrace_5068536
  have hstable : (prefixWord ++ tailWord_5068536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068536).length < 2 ^ (prefixWord ++ tailWord_5068536).sum := by decide
  have hdescent : baseEnd_5068536 < baseStart_5068536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068574 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5068574 : Nat := 118140960795 + 5068574 * 2 ^ 59
def prefixEnd_5068574 : Nat := 4983230072969 + 3 ^ 40 * 5068574 * 2
def baseEnd_5068574 : Nat := 2602614694881957414615059

theorem tailTrace_5068574 : CollatzResearch.WordTrace tailWord_5068574 prefixEnd_5068574 2602614694881957414615059 := by
  unfold tailWord_5068574
  simp only [CollatzResearch.WordTrace]
  refine ⟨23108260142428689545863597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123244054092953010911272517 23108260142428689545863597)
  ·
    refine ⟨8665597553410758579698849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23108260142428689545863597 8665597553410758579698849)
    ·
      refine ⟨6499198165058068934774137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8665597553410758579698849 6499198165058068934774137)
      ·
        refine ⟨4874398623793551701080603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6499198165058068934774137 4874398623793551701080603)
        ·
          refine ⟨7311597935690327551620905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874398623793551701080603 7311597935690327551620905)
          ·
            refine ⟨5483698451767745663715679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311597935690327551620905 5483698451767745663715679)
            ·
              refine ⟨8225547677651618495573519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483698451767745663715679 8225547677651618495573519)
              ·
                refine ⟨12338321516477427743360279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8225547677651618495573519 12338321516477427743360279)
                ·
                  refine ⟨18507482274716141615040419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12338321516477427743360279 18507482274716141615040419)
                  ·
                    refine ⟨27761223412074212422560629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18507482274716141615040419 27761223412074212422560629)
                    ·
                      refine ⟨2602614694881957414615059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27761223412074212422560629 2602614694881957414615059)
                      ·
                        rfl

theorem cell23_5068574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5068574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068574 prefixEnd_5068574 := by exact prefixLift 5068574
  have htrace : WordTrace (prefixWord ++ tailWord_5068574) baseStart_5068574 baseEnd_5068574 := by
    simpa [prefixWord, tailWord_5068574, baseEnd_5068574] using wordTrace_append hprefix tailTrace_5068574
  have hstable : (prefixWord ++ tailWord_5068574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068574).length < 2 ^ (prefixWord ++ tailWord_5068574).sum := by decide
  have hdescent : baseEnd_5068574 < baseStart_5068574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068614 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5068614 : Nat := 118140960795 + 5068614 * 2 ^ 59
def prefixEnd_5068614 : Nat := 4983230072969 + 3 ^ 40 * 5068614 * 2
def baseEnd_5068614 : Nat := 2602635234108137258114875

theorem tailTrace_5068614 : CollatzResearch.WordTrace tailWord_5068614 prefixEnd_5068614 2602635234108137258114875 := by
  unfold tailWord_5068614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777110626852643849948903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123245026706189735465576597 5777110626852643849948903)
  ·
    refine ⟨8665665940278965774923355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5777110626852643849948903 8665665940278965774923355)
    ·
      refine ⟨12998498910418448662385033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665665940278965774923355 12998498910418448662385033)
      ·
        refine ⟨9748874182813836496788775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12998498910418448662385033 9748874182813836496788775)
        ·
          refine ⟨14623311274220754745183163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748874182813836496788775 14623311274220754745183163)
          ·
            refine ⟨21934966911331132117774745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14623311274220754745183163 21934966911331132117774745)
            ·
              refine ⟨16451225183498349088331059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21934966911331132117774745 16451225183498349088331059)
              ·
                refine ⟨24676837775247523632496589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16451225183498349088331059 24676837775247523632496589)
                ·
                  refine ⟨9253814165717821362186221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24676837775247523632496589 9253814165717821362186221)
                  ·
                    refine ⟨3470180312144183010819833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9253814165717821362186221 3470180312144183010819833)
                    ·
                      refine ⟨2602635234108137258114875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470180312144183010819833 2602635234108137258114875)
                      ·
                        rfl

theorem cell23_5068614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5068614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068614 prefixEnd_5068614 := by exact prefixLift 5068614
  have htrace : WordTrace (prefixWord ++ tailWord_5068614) baseStart_5068614 baseEnd_5068614 := by
    simpa [prefixWord, tailWord_5068614, baseEnd_5068614] using wordTrace_append hprefix tailTrace_5068614
  have hstable : (prefixWord ++ tailWord_5068614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068614).length < 2 ^ (prefixWord ++ tailWord_5068614).sum := by decide
  have hdescent : baseEnd_5068614 < baseStart_5068614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068616 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 9]
def baseStart_5068616 : Nat := 118140960795 + 5068616 * 2 ^ 59
def prefixEnd_5068616 : Nat := 4983230072969 + 3 ^ 40 * 5068616 * 2
def baseEnd_5068616 : Nat := 289181806785494027809985

theorem tailTrace_5068616 : CollatzResearch.WordTrace tailWord_5068616 prefixEnd_5068616 289181806785494027809985 := by
  unfold tailWord_5068616
  simp only [CollatzResearch.WordTrace]
  refine ⟨92433806502638678769968851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123245075336851571693291801 92433806502638678769968851)
  ·
    refine ⟨138650709753958018154953277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92433806502638678769968851 138650709753958018154953277)
    ·
      refine ⟨51994016157734256808107479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138650709753958018154953277 51994016157734256808107479)
      ·
        refine ⟨77991024236601385212161219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51994016157734256808107479 77991024236601385212161219)
        ·
          refine ⟨116986536354902077818241829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77991024236601385212161219 116986536354902077818241829)
          ·
            refine ⟨21934975566544139590920343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116986536354902077818241829 21934975566544139590920343)
            ·
              refine ⟨32902463349816209386380515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21934975566544139590920343 32902463349816209386380515)
              ·
                refine ⟨49353695024724314079570773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32902463349816209386380515 49353695024724314079570773)
                ·
                  refine ⟨289181806785494027809985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49353695024724314079570773 289181806785494027809985)
                  ·
                    rfl

theorem cell23_5068616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_5068616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068616 prefixEnd_5068616 := by exact prefixLift 5068616
  have htrace : WordTrace (prefixWord ++ tailWord_5068616) baseStart_5068616 baseEnd_5068616 := by
    simpa [prefixWord, tailWord_5068616, baseEnd_5068616] using wordTrace_append hprefix tailTrace_5068616
  have hstable : (prefixWord ++ tailWord_5068616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068616).length < 2 ^ (prefixWord ++ tailWord_5068616).sum := by decide
  have hdescent : baseEnd_5068616 < baseStart_5068616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068631 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_5068631 : Nat := 118140960795 + 5068631 * 2 ^ 59
def prefixEnd_5068631 : Nat := 4983230072969 + 3 ^ 40 * 5068631 * 2
def baseEnd_5068631 : Nat := 2602643963279263691602297

theorem tailTrace_5068631 : CollatzResearch.WordTrace tailWord_5068631 prefixEnd_5068631 2602643963279263691602297 := by
  unfold tailWord_5068631
  simp only [CollatzResearch.WordTrace]
  refine ⟨184868160100223015101733747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123245440066815343401155831 184868160100223015101733747)
  ·
    refine ⟨277302240150334522652600621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184868160100223015101733747 277302240150334522652600621)
    ·
      refine ⟨103988340056375445994725233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277302240150334522652600621 103988340056375445994725233)
      ·
        refine ⟨77991255042281584496043925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103988340056375445994725233 77991255042281584496043925)
        ·
          refine ⟨3655840080106949273252059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77991255042281584496043925 3655840080106949273252059)
          ·
            refine ⟨5483760120160423909878089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655840080106949273252059 5483760120160423909878089)
            ·
              refine ⟨4112820090120317932408567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483760120160423909878089 4112820090120317932408567)
              ·
                refine ⟨6169230135180476898612851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112820090120317932408567 6169230135180476898612851)
                ·
                  refine ⟨9253845202770715347919277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169230135180476898612851 9253845202770715347919277)
                  ·
                    refine ⟨3470191951039018255469729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9253845202770715347919277 3470191951039018255469729)
                    ·
                      refine ⟨2602643963279263691602297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470191951039018255469729 2602643963279263691602297)
                      ·
                        rfl

theorem cell23_5068631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_5068631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068631 prefixEnd_5068631 := by exact prefixLift 5068631
  have htrace : WordTrace (prefixWord ++ tailWord_5068631) baseStart_5068631 baseEnd_5068631 := by
    simpa [prefixWord, tailWord_5068631, baseEnd_5068631] using wordTrace_append hprefix tailTrace_5068631
  have hstable : (prefixWord ++ tailWord_5068631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068631).length < 2 ^ (prefixWord ++ tailWord_5068631).sum := by decide
  have hdescent : baseEnd_5068631 < baseStart_5068631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068656 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_5068656 : Nat := 118140960795 + 5068656 * 2 ^ 59
def prefixEnd_5068656 : Nat := 4983230072969 + 3 ^ 40 * 5068656 * 2
def baseEnd_5068656 : Nat := 2602656800295626093789681

theorem tailTrace_5068656 : CollatzResearch.WordTrace tailWord_5068656 prefixEnd_5068656 2602656800295626093789681 := by
  unfold tailWord_5068656
  simp only [CollatzResearch.WordTrace]
  refine ⟨92434535962566222185696911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123246047950088296247595881 92434535962566222185696911)
  ·
    refine ⟨138651803943849333278545367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92434535962566222185696911 138651803943849333278545367)
    ·
      refine ⟨207977705915773999917818051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138651803943849333278545367 207977705915773999917818051)
      ·
        refine ⟨311966558873660999876727077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207977705915773999917818051 311966558873660999876727077)
        ·
          refine ⟨58493729788811437476886327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311966558873660999876727077 58493729788811437476886327)
          ·
            refine ⟨87740594683217156215329491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58493729788811437476886327 87740594683217156215329491)
            ·
              refine ⟨131610892024825734322994237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87740594683217156215329491 131610892024825734322994237)
              ·
                refine ⟨49354084509309650371122839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131610892024825734322994237 49354084509309650371122839)
                ·
                  refine ⟨74031126763964475556684259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49354084509309650371122839 74031126763964475556684259)
                  ·
                    refine ⟨111046690145946713335026389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74031126763964475556684259 111046690145946713335026389)
                    ·
                      refine ⟨2602656800295626093789681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111046690145946713335026389 2602656800295626093789681)
                      ·
                        rfl

theorem cell23_5068656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_5068656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068656 prefixEnd_5068656 := by exact prefixLift 5068656
  have htrace : WordTrace (prefixWord ++ tailWord_5068656) baseStart_5068656 baseEnd_5068656 := by
    simpa [prefixWord, tailWord_5068656, baseEnd_5068656] using wordTrace_append hprefix tailTrace_5068656
  have hstable : (prefixWord ++ tailWord_5068656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068656).length < 2 ^ (prefixWord ++ tailWord_5068656).sum := by decide
  have hdescent : baseEnd_5068656 < baseStart_5068656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068683 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4]
def baseStart_5068683 : Nat := 118140960795 + 5068683 * 2 ^ 59
def prefixEnd_5068683 : Nat := 4983230072969 + 3 ^ 40 * 5068683 * 2
def baseEnd_5068683 : Nat := 2602670664273297488152057

theorem tailTrace_5068683 : CollatzResearch.WordTrace tailWord_5068683 prefixEnd_5068683 2602670664273297488152057 := by
  unfold tailWord_5068683
  simp only [CollatzResearch.WordTrace]
  refine ⟨184870056696034627982626703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123246704464023085321751135 184870056696034627982626703)
  ·
    refine ⟨277305085044051941973940055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184870056696034627982626703 277305085044051941973940055)
    ·
      refine ⟨415957627566077912960910083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277305085044051941973940055 415957627566077912960910083)
      ·
        refine ⟨623936441349116869441365125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415957627566077912960910083 623936441349116869441365125)
        ·
          refine ⟨116988082752959413020255961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 623936441349116869441365125 116988082752959413020255961)
          ·
            refine ⟨87741062064719559765191971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116988082752959413020255961 87741062064719559765191971)
            ·
              refine ⟨131611593097079339647787957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87741062064719559765191971 131611593097079339647787957)
              ·
                refine ⟨12338586852851188091980121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131611593097079339647787957 12338586852851188091980121)
                ·
                  refine ⟨9253940139638391068985091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12338586852851188091980121 9253940139638391068985091)
                  ·
                    refine ⟨13880910209457586603477637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9253940139638391068985091 13880910209457586603477637)
                    ·
                      refine ⟨2602670664273297488152057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13880910209457586603477637 2602670664273297488152057)
                      ·
                        rfl

theorem cell23_5068683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4].length) (baseStart_5068683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068683 prefixEnd_5068683 := by exact prefixLift 5068683
  have htrace : WordTrace (prefixWord ++ tailWord_5068683) baseStart_5068683 baseEnd_5068683 := by
    simpa [prefixWord, tailWord_5068683, baseEnd_5068683] using wordTrace_append hprefix tailTrace_5068683
  have hstable : (prefixWord ++ tailWord_5068683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068683).length < 2 ^ (prefixWord ++ tailWord_5068683).sum := by decide
  have hdescent : baseEnd_5068683 < baseStart_5068683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068700 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5068700 : Nat := 118140960795 + 5068700 * 2 ^ 59
def prefixEnd_5068700 : Nat := 4983230072969 + 3 ^ 40 * 5068700 * 2
def baseEnd_5068700 : Nat := 2602679393444423921639479

theorem tailTrace_5068700 : CollatzResearch.WordTrace tailWord_5068700 prefixEnd_5068700 2602679393444423921639479 := by
  unfold tailWord_5068700
  simp only [CollatzResearch.WordTrace]
  refine ⟨92435338368486519942997777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123247117824648693257330369 92435338368486519942997777)
  ·
    refine ⟨69326503776364889957248333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92435338368486519942997777 69326503776364889957248333)
    ·
      refine ⟨25997438916136833733968125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69326503776364889957248333 25997438916136833733968125)
      ·
        refine ⟨9749039593551312650238047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25997438916136833733968125 9749039593551312650238047)
        ·
          refine ⟨14623559390326968975357071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9749039593551312650238047 14623559390326968975357071)
          ·
            refine ⟨21935339085490453463035607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14623559390326968975357071 21935339085490453463035607)
            ·
              refine ⟨32903008628235680194553411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21935339085490453463035607 32903008628235680194553411)
              ·
                refine ⟨49354512942353520291830117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32903008628235680194553411 49354512942353520291830117)
                ·
                  refine ⟨9253971176691285054718147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49354512942353520291830117 9253971176691285054718147)
                  ·
                    refine ⟨13880956765036927582077221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9253971176691285054718147 13880956765036927582077221)
                    ·
                      refine ⟨2602679393444423921639479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13880956765036927582077221 2602679393444423921639479)
                      ·
                        rfl

theorem cell23_5068700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5068700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068700 prefixEnd_5068700 := by exact prefixLift 5068700
  have htrace : WordTrace (prefixWord ++ tailWord_5068700) baseStart_5068700 baseEnd_5068700 := by
    simpa [prefixWord, tailWord_5068700, baseEnd_5068700] using wordTrace_append hprefix tailTrace_5068700
  have hstable : (prefixWord ++ tailWord_5068700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068700).length < 2 ^ (prefixWord ++ tailWord_5068700).sum := by decide
  have hdescent : baseEnd_5068700 < baseStart_5068700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068723 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 6]
def baseStart_5068723 : Nat := 118140960795 + 5068723 * 2 ^ 59
def prefixEnd_5068723 : Nat := 4983230072969 + 3 ^ 40 * 5068723 * 2
def baseEnd_5068723 : Nat := 289187911499941925739097

theorem tailTrace_5068723 : CollatzResearch.WordTrace tailWord_5068723 prefixEnd_5068723 289187911499941925739097 := by
  unfold tailWord_5068723
  simp only [CollatzResearch.WordTrace]
  refine ⟨184871515615889714814082823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123247677077259809876055215 184871515615889714814082823)
  ·
    refine ⟨277307273423834572221124235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184871515615889714814082823 277307273423834572221124235)
    ·
      refine ⟨415960910135751858331686353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277307273423834572221124235 415960910135751858331686353)
      ·
        refine ⟨311970682601813893748764765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415960910135751858331686353 311970682601813893748764765)
        ·
          refine ⟨116989005975680210155786787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311970682601813893748764765 116989005975680210155786787)
          ·
            refine ⟨175483508963520315233680181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116989005975680210155786787 175483508963520315233680181)
            ·
              refine ⟨16451578965330029553157517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175483508963520315233680181 16451578965330029553157517)
              ·
                refine ⟨6169342111998761082434069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16451578965330029553157517 6169342111998761082434069)
                ·
                  refine ⟨289187911499941925739097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169342111998761082434069 289187911499941925739097)
                  ·
                    rfl

theorem cell23_5068723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 6].length) (baseStart_5068723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068723 prefixEnd_5068723 := by exact prefixLift 5068723
  have htrace : WordTrace (prefixWord ++ tailWord_5068723) baseStart_5068723 baseEnd_5068723 := by
    simpa [prefixWord, tailWord_5068723, baseEnd_5068723] using wordTrace_append hprefix tailTrace_5068723
  have hstable : (prefixWord ++ tailWord_5068723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068723).length < 2 ^ (prefixWord ++ tailWord_5068723).sum := by decide
  have hdescent : baseEnd_5068723 < baseStart_5068723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068761 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 1, 4]
def baseStart_5068761 : Nat := 118140960795 + 5068761 * 2 ^ 59
def prefixEnd_5068761 : Nat := 4983230072969 + 3 ^ 40 * 5068761 * 2
def baseEnd_5068761 : Nat := 867570238588116060992233

theorem tailTrace_5068761 : CollatzResearch.WordTrace tailWord_5068761 prefixEnd_5068761 867570238588116060992233 := by
  unfold tailWord_5068761
  simp only [CollatzResearch.WordTrace]
  refine ⟨184872901589752047303966137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123248601059834698202644091 184872901589752047303966137)
  ·
    refine ⟨138654676192314035477974603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184872901589752047303966137 138654676192314035477974603)
    ·
      refine ⟨207982014288471053216961905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138654676192314035477974603 207982014288471053216961905)
      ·
        refine ⟨155986510716353289912721429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207982014288471053216961905 155986510716353289912721429)
        ·
          refine ⟨7311867689829060464658817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155986510716353289912721429 7311867689829060464658817)
          ·
            refine ⟨5483900767371795348494113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311867689829060464658817 5483900767371795348494113)
            ·
              refine ⟨4112925575528846511370585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483900767371795348494113 4112925575528846511370585)
              ·
                refine ⟨3084694181646634883527939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112925575528846511370585 3084694181646634883527939)
                ·
                  refine ⟨4627041272469952325291909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084694181646634883527939 4627041272469952325291909)
                  ·
                    refine ⟨867570238588116060992233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627041272469952325291909 867570238588116060992233)
                    ·
                      rfl

theorem cell23_5068761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 4].length) (baseStart_5068761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068761 prefixEnd_5068761 := by exact prefixLift 5068761
  have htrace : WordTrace (prefixWord ++ tailWord_5068761) baseStart_5068761 baseEnd_5068761 := by
    simpa [prefixWord, tailWord_5068761, baseEnd_5068761] using wordTrace_append hprefix tailTrace_5068761
  have hstable : (prefixWord ++ tailWord_5068761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068761).length < 2 ^ (prefixWord ++ tailWord_5068761).sum := by decide
  have hdescent : baseEnd_5068761 < baseStart_5068761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068804 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_5068804 : Nat := 118140960795 + 5068804 * 2 ^ 59
def prefixEnd_5068804 : Nat := 4983230072969 + 3 ^ 40 * 5068804 * 2
def baseEnd_5068804 : Nat := 867577598477497171579667

theorem tailTrace_5068804 : CollatzResearch.WordTrace tailWord_5068804 prefixEnd_5068804 867577598477497171579667 := by
  unfold tailWord_5068804
  simp only [CollatzResearch.WordTrace]
  refine ⟨92437234964298132823890733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123249646619064177098520977 92437234964298132823890733)
  ·
    refine ⟨34663963111611799808959025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92437234964298132823890733 34663963111611799808959025)
    ·
      refine ⟨25997972333708849856719269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34663963111611799808959025 25997972333708849856719269)
      ·
        refine ⟨4874619812570409348134863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25997972333708849856719269 4874619812570409348134863)
        ·
          refine ⟨7311929718855614022202295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874619812570409348134863 7311929718855614022202295)
          ·
            refine ⟨10967894578283421033303443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311929718855614022202295 10967894578283421033303443)
            ·
              refine ⟨16451841867425131549955165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967894578283421033303443 16451841867425131549955165)
              ·
                refine ⟨6169440700284424331233187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16451841867425131549955165 6169440700284424331233187)
                ·
                  refine ⟨9254161050426636496849781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169440700284424331233187 9254161050426636496849781)
                  ·
                    refine ⟨867577598477497171579667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9254161050426636496849781 867577598477497171579667)
                    ·
                      rfl

theorem cell23_5068804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_5068804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068804 prefixEnd_5068804 := by exact prefixLift 5068804
  have htrace : WordTrace (prefixWord ++ tailWord_5068804) baseStart_5068804 baseEnd_5068804 := by
    simpa [prefixWord, tailWord_5068804, baseEnd_5068804] using wordTrace_append hprefix tailTrace_5068804
  have hstable : (prefixWord ++ tailWord_5068804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068804).length < 2 ^ (prefixWord ++ tailWord_5068804).sum := by decide
  have hdescent : baseEnd_5068804 < baseStart_5068804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068807 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_5068807 : Nat := 118140960795 + 5068807 * 2 ^ 59
def prefixEnd_5068807 : Nat := 4983230072969 + 3 ^ 40 * 5068807 * 2
def baseEnd_5068807 : Nat := 2602734335874455003001487

theorem tailTrace_5068807 : CollatzResearch.WordTrace tailWord_5068807 prefixEnd_5068807 2602734335874455003001487 := by
  unfold tailWord_5068807
  simp only [CollatzResearch.WordTrace]
  refine ⟨184874579347585397160140675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123249719565056931440093783 184874579347585397160140675)
  ·
    refine ⟨277311869021378095740211013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184874579347585397160140675 277311869021378095740211013)
    ·
      refine ⟨51995975441508392951289565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277311869021378095740211013 51995975441508392951289565)
      ·
        refine ⟨19498490790565647356733587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51995975441508392951289565 19498490790565647356733587)
        ·
          refine ⟨29247736185848471035100381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19498490790565647356733587 29247736185848471035100381)
          ·
            refine ⟨10967901069693176638162643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29247736185848471035100381 10967901069693176638162643)
            ·
              refine ⟨16451851604539764957243965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967901069693176638162643 16451851604539764957243965)
              ·
                refine ⟨6169444351702411858966487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16451851604539764957243965 6169444351702411858966487)
                ·
                  refine ⟨9254166527553617788449731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169444351702411858966487 9254166527553617788449731)
                  ·
                    refine ⟨13881249791330426682674597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9254166527553617788449731 13881249791330426682674597)
                    ·
                      refine ⟨2602734335874455003001487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13881249791330426682674597 2602734335874455003001487)
                      ·
                        rfl

theorem cell23_5068807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_5068807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068807 prefixEnd_5068807 := by exact prefixLift 5068807
  have htrace : WordTrace (prefixWord ++ tailWord_5068807) baseStart_5068807 baseEnd_5068807 := by
    simpa [prefixWord, tailWord_5068807, baseEnd_5068807] using wordTrace_append hprefix tailTrace_5068807
  have hstable : (prefixWord ++ tailWord_5068807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068807).length < 2 ^ (prefixWord ++ tailWord_5068807).sum := by decide
  have hdescent : baseEnd_5068807 < baseStart_5068807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068824 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5068824 : Nat := 118140960795 + 5068824 * 2 ^ 59
def prefixEnd_5068824 : Nat := 4983230072969 + 3 ^ 40 * 5068824 * 2
def baseEnd_5068824 : Nat := 2602743065045581436488909

theorem tailTrace_5068824 : CollatzResearch.WordTrace tailWord_5068824 prefixEnd_5068824 2602743065045581436488909 := by
  unfold tailWord_5068824
  simp only [CollatzResearch.WordTrace]
  refine ⟨92437599694261904531754763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123250132925682539375673017 92437599694261904531754763)
  ·
    refine ⟨138656399541392856797632145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92437599694261904531754763 138656399541392856797632145)
    ·
      refine ⟨103992299656044642598224109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138656399541392856797632145 103992299656044642598224109)
      ·
        refine ⟨38997112371016740974334041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103992299656044642598224109 38997112371016740974334041)
        ·
          refine ⟨29247834278262555730750531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38997112371016740974334041 29247834278262555730750531)
          ·
            refine ⟨43871751417393833596125797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29247834278262555730750531 43871751417393833596125797)
            ·
              refine ⟨8225953390761343799273587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43871751417393833596125797 8225953390761343799273587)
              ·
                refine ⟨12338930086142015698910381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8225953390761343799273587 12338930086142015698910381)
                ·
                  refine ⟨4627098782303255887091393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12338930086142015698910381 4627098782303255887091393)
                  ·
                    refine ⟨3470324086727441915318545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4627098782303255887091393 3470324086727441915318545)
                    ·
                      refine ⟨2602743065045581436488909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470324086727441915318545 2602743065045581436488909)
                      ·
                        rfl

theorem cell23_5068824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5068824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068824 prefixEnd_5068824 := by exact prefixLift 5068824
  have htrace : WordTrace (prefixWord ++ tailWord_5068824) baseStart_5068824 baseEnd_5068824 := by
    simpa [prefixWord, tailWord_5068824, baseEnd_5068824] using wordTrace_append hprefix tailTrace_5068824
  have hstable : (prefixWord ++ tailWord_5068824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068824).length < 2 ^ (prefixWord ++ tailWord_5068824).sum := by decide
  have hdescent : baseEnd_5068824 < baseStart_5068824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068834 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_5068834 : Nat := 118140960795 + 5068834 * 2 ^ 59
def prefixEnd_5068834 : Nat := 4983230072969 + 3 ^ 40 * 5068834 * 2
def baseEnd_5068834 : Nat := 867582733284042132454621

theorem tailTrace_5068834 : CollatzResearch.WordTrace tailWord_5068834 prefixEnd_5068834 867582733284042132454621 := by
  unfold tailWord_5068834
  simp only [CollatzResearch.WordTrace]
  refine ⟨46218891029621895192843389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123250376078991720514249037 46218891029621895192843389)
  ·
    refine ⟨17332084136108210697316271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46218891029621895192843389 17332084136108210697316271)
    ·
      refine ⟨25998126204162316045974407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17332084136108210697316271 25998126204162316045974407)
      ·
        refine ⟨38997189306243474068961611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25998126204162316045974407 38997189306243474068961611)
        ·
          refine ⟨58495783959365211103442417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38997189306243474068961611 58495783959365211103442417)
          ·
            refine ⟨43871837969523908327581813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58495783959365211103442417 43871837969523908327581813)
            ·
              refine ⟨4112984809642866405710795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43871837969523908327581813 4112984809642866405710795)
              ·
                refine ⟨6169477214464299608566193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112984809642866405710795 6169477214464299608566193)
                ·
                  refine ⟨4627107910848224706424645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6169477214464299608566193 4627107910848224706424645)
                  ·
                    refine ⟨867582733284042132454621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627107910848224706424645 867582733284042132454621)
                    ·
                      rfl

theorem cell23_5068834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_5068834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068834 prefixEnd_5068834 := by exact prefixLift 5068834
  have htrace : WordTrace (prefixWord ++ tailWord_5068834) baseStart_5068834 baseEnd_5068834 := by
    simpa [prefixWord, tailWord_5068834, baseEnd_5068834] using wordTrace_append hprefix tailTrace_5068834
  have hstable : (prefixWord ++ tailWord_5068834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068834).length < 2 ^ (prefixWord ++ tailWord_5068834).sum := by decide
  have hdescent : baseEnd_5068834 < baseStart_5068834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068837 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_5068837 : Nat := 118140960795 + 5068837 * 2 ^ 59
def prefixEnd_5068837 : Nat := 4983230072969 + 3 ^ 40 * 5068837 * 2
def baseEnd_5068837 : Nat := 2602749740294089885626349

theorem tailTrace_5068837 : CollatzResearch.WordTrace tailWord_5068837 prefixEnd_5068837 2602749740294089885626349 := by
  unfold tailWord_5068837
  simp only [CollatzResearch.WordTrace]
  refine ⟨184875673537476712283732765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123250449024984474855821843 184875673537476712283732765)
  ·
    refine ⟨69328377576553767106399787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184875673537476712283732765 69328377576553767106399787)
    ·
      refine ⟨103992566364830650659599681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69328377576553767106399787 103992566364830650659599681)
      ·
        refine ⟨77994424773622987994699761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103992566364830650659599681 77994424773622987994699761)
        ·
          refine ⟨58495818580217240996024821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77994424773622987994699761 58495818580217240996024821)
          ·
            refine ⟨5483982991895366343377327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58495818580217240996024821 5483982991895366343377327)
            ·
              refine ⟨8225974487843049515065991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483982991895366343377327 8225974487843049515065991)
              ·
                refine ⟨12338961731764574272598987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8225974487843049515065991 12338961731764574272598987)
                ·
                  refine ⟨18508442597646861408898481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12338961731764574272598987 18508442597646861408898481)
                  ·
                    refine ⟨13881331948235146056673861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18508442597646861408898481 13881331948235146056673861)
                    ·
                      refine ⟨2602749740294089885626349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13881331948235146056673861 2602749740294089885626349)
                      ·
                        rfl

theorem cell23_5068837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_5068837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068837 prefixEnd_5068837 := by exact prefixLift 5068837
  have htrace : WordTrace (prefixWord ++ tailWord_5068837) baseStart_5068837 baseEnd_5068837 := by
    simpa [prefixWord, tailWord_5068837, baseEnd_5068837] using wordTrace_append hprefix tailTrace_5068837
  have hstable : (prefixWord ++ tailWord_5068837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068837).length < 2 ^ (prefixWord ++ tailWord_5068837).sum := by decide
  have hdescent : baseEnd_5068837 < baseStart_5068837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068897 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_5068897 : Nat := 118140960795 + 5068897 * 2 ^ 59
def prefixEnd_5068897 : Nat := 4983230072969 + 3 ^ 40 * 5068897 * 2
def baseEnd_5068897 : Nat := 2602780549133359650876073

theorem tailTrace_5068897 : CollatzResearch.WordTrace tailWord_5068897 prefixEnd_5068897 2602780549133359650876073 := by
  unfold tailWord_5068897
  simp only [CollatzResearch.WordTrace]
  refine ⟨184877861917259342530916945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123251907944839561687277963 184877861917259342530916945)
  ·
    refine ⟨138658396437944506898187709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184877861917259342530916945 138658396437944506898187709)
    ·
      refine ⟨51996898664229190086820391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138658396437944506898187709 51996898664229190086820391)
      ·
        refine ⟨77995347996343785130230587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51996898664229190086820391 77995347996343785130230587)
        ·
          refine ⟨116993021994515677695345881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77995347996343785130230587 116993021994515677695345881)
          ·
            refine ⟨87744766495886758271509411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116993021994515677695345881 87744766495886758271509411)
            ·
              refine ⟨131617149743830137407264117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87744766495886758271509411 131617149743830137407264117)
              ·
                refine ⟨12339107788484075381931011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131617149743830137407264117 12339107788484075381931011)
                ·
                  refine ⟨18508661682726113072896517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339107788484075381931011 18508661682726113072896517)
                  ·
                    refine ⟨3470374065511146201168097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18508661682726113072896517 3470374065511146201168097)
                    ·
                      refine ⟨2602780549133359650876073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470374065511146201168097 2602780549133359650876073)
                      ·
                        rfl

theorem cell23_5068897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_5068897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068897 prefixEnd_5068897 := by exact prefixLift 5068897
  have htrace : WordTrace (prefixWord ++ tailWord_5068897) baseStart_5068897 baseEnd_5068897 := by
    simpa [prefixWord, tailWord_5068897, baseEnd_5068897] using wordTrace_append hprefix tailTrace_5068897
  have hstable : (prefixWord ++ tailWord_5068897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068897).length < 2 ^ (prefixWord ++ tailWord_5068897).sum := by decide
  have hdescent : baseEnd_5068897 < baseStart_5068897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068900 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_5068900 : Nat := 118140960795 + 5068900 * 2 ^ 59
def prefixEnd_5068900 : Nat := 4983230072969 + 3 ^ 40 * 5068900 * 2
def baseEnd_5068900 : Nat := 2602782089575323139138559

theorem tailTrace_5068900 : CollatzResearch.WordTrace tailWord_5068900 prefixEnd_5068900 2602782089575323139138559 := by
  unfold tailWord_5068900
  simp only [CollatzResearch.WordTrace]
  refine ⟨92438985668124237021638077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123251980890832316028850769 92438985668124237021638077)
  ·
    refine ⟨34664619625546588883114279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92438985668124237021638077 34664619625546588883114279)
    ·
      refine ⟨51996929438319883324671419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34664619625546588883114279 51996929438319883324671419)
      ·
        refine ⟨77995394157479824987007129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51996929438319883324671419 77995394157479824987007129)
        ·
          refine ⟨58496545618109868740255347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77995394157479824987007129 58496545618109868740255347)
          ·
            refine ⟨87744818427164803110383021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58496545618109868740255347 87744818427164803110383021)
            ·
              refine ⟨32904306910186801166393633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87744818427164803110383021 32904306910186801166393633)
              ·
                refine ⟨24678230182640100874795225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32904306910186801166393633 24678230182640100874795225)
                ·
                  refine ⟨18508672636980075656096419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24678230182640100874795225 18508672636980075656096419)
                  ·
                    refine ⟨27763008955470113484144629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18508672636980075656096419 27763008955470113484144629)
                    ·
                      refine ⟨2602782089575323139138559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27763008955470113484144629 2602782089575323139138559)
                      ·
                        rfl

theorem cell23_5068900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_5068900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068900 prefixEnd_5068900 := by exact prefixLift 5068900
  have htrace : WordTrace (prefixWord ++ tailWord_5068900) baseStart_5068900 baseEnd_5068900 := by
    simpa [prefixWord, tailWord_5068900, baseEnd_5068900] using wordTrace_append hprefix tailTrace_5068900
  have hstable : (prefixWord ++ tailWord_5068900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068900).length < 2 ^ (prefixWord ++ tailWord_5068900).sum := by decide
  have hdescent : baseEnd_5068900 < baseStart_5068900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068901 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_5068901 : Nat := 118140960795 + 5068901 * 2 ^ 59
def prefixEnd_5068901 : Nat := 4983230072969 + 3 ^ 40 * 5068901 * 2
def baseEnd_5068901 : Nat := 2602782603055977635226055

theorem tailTrace_5068901 : CollatzResearch.WordTrace tailWord_5068901 prefixEnd_5068901 2602782603055977635226055 := by
  unfold tailWord_5068901
  simp only [CollatzResearch.WordTrace]
  refine ⟨184878007809244851214062557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123252005206163234142708371 184878007809244851214062557)
  ·
    refine ⟨69329252928466819205273459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184878007809244851214062557 69329252928466819205273459)
    ·
      refine ⟨103993879392700228807910189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69329252928466819205273459 103993879392700228807910189)
      ·
        refine ⟨38997704772262585802966321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103993879392700228807910189 38997704772262585802966321)
        ·
          refine ⟨29248278579196939352224741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38997704772262585802966321 29248278579196939352224741)
          ·
            refine ⟨5484052233599426128542139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29248278579196939352224741 5484052233599426128542139)
            ·
              refine ⟨8226078350399139192813209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484052233599426128542139 8226078350399139192813209)
              ·
                refine ⟨6169558762799354394609907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226078350399139192813209 6169558762799354394609907)
                ·
                  refine ⟨9254338144199031591914861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169558762799354394609907 9254338144199031591914861)
                  ·
                    refine ⟨3470376804074636846968073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9254338144199031591914861 3470376804074636846968073)
                    ·
                      refine ⟨2602782603055977635226055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470376804074636846968073 2602782603055977635226055)
                      ·
                        rfl

theorem cell23_5068901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_5068901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068901 prefixEnd_5068901 := by exact prefixLift 5068901
  have htrace : WordTrace (prefixWord ++ tailWord_5068901) baseStart_5068901 baseEnd_5068901 := by
    simpa [prefixWord, tailWord_5068901, baseEnd_5068901] using wordTrace_append hprefix tailTrace_5068901
  have hstable : (prefixWord ++ tailWord_5068901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068901).length < 2 ^ (prefixWord ++ tailWord_5068901).sum := by decide
  have hdescent : baseEnd_5068901 < baseStart_5068901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068914 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5068914 : Nat := 118140960795 + 5068914 * 2 ^ 59
def prefixEnd_5068914 : Nat := 4983230072969 + 3 ^ 40 * 5068914 * 2
def baseEnd_5068914 : Nat := 2602789278304486084363495

theorem tailTrace_5068914 : CollatzResearch.WordTrace tailWord_5068914 prefixEnd_5068914 2602789278304486084363495 := by
  unfold tailWord_5068914
  simp only [CollatzResearch.WordTrace]
  refine ⟨46219620489549438608571449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123252321305465169622857197 46219620489549438608571449)
  ·
    refine ⟨34664715367162078956428587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46219620489549438608571449 34664715367162078956428587)
    ·
      refine ⟨51997073050743118434642881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34664715367162078956428587 51997073050743118434642881)
      ·
        refine ⟨38997804788057338825982161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51997073050743118434642881 38997804788057338825982161)
        ·
          refine ⟨29248353591043004119486621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38997804788057338825982161 29248353591043004119486621)
          ·
            refine ⟨10968132596641126544807483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29248353591043004119486621 10968132596641126544807483)
            ·
              refine ⟨16452198894961689817211225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10968132596641126544807483 16452198894961689817211225)
              ·
                refine ⟨12339149171221267362908419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16452198894961689817211225 12339149171221267362908419)
                ·
                  refine ⟨18508723756831901044362629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339149171221267362908419 18508723756831901044362629)
                  ·
                    refine ⟨3470385704405981445817993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18508723756831901044362629 3470385704405981445817993)
                    ·
                      refine ⟨2602789278304486084363495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470385704405981445817993 2602789278304486084363495)
                      ·
                        rfl

theorem cell23_5068914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5068914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068914 prefixEnd_5068914 := by exact prefixLift 5068914
  have htrace : WordTrace (prefixWord ++ tailWord_5068914) baseStart_5068914 baseEnd_5068914 := by
    simpa [prefixWord, tailWord_5068914, baseEnd_5068914] using wordTrace_append hprefix tailTrace_5068914
  have hstable : (prefixWord ++ tailWord_5068914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068914).length < 2 ^ (prefixWord ++ tailWord_5068914).sum := by decide
  have hdescent : baseEnd_5068914 < baseStart_5068914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068918 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5068918 : Nat := 118140960795 + 5068918 * 2 ^ 59
def prefixEnd_5068918 : Nat := 4983230072969 + 3 ^ 40 * 5068918 * 2
def baseEnd_5068918 : Nat := 2602791332227104068713477

theorem tailTrace_5068918 : CollatzResearch.WordTrace tailWord_5068918 prefixEnd_5068918 2602791332227104068713477 := by
  unfold tailWord_5068918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554914240636453944839463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123252418566788842078287605 11554914240636453944839463)
  ·
    refine ⟨17332371360954680917259195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11554914240636453944839463 17332371360954680917259195)
    ·
      refine ⟨25998557041432021375888793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17332371360954680917259195 25998557041432021375888793)
      ·
        refine ⟨19498917781074016031916595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25998557041432021375888793 19498917781074016031916595)
        ·
          refine ⟨29248376671611024047874893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19498917781074016031916595 29248376671611024047874893)
          ·
            refine ⟨10968141251854134017953085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29248376671611024047874893 10968141251854134017953085)
            ·
              refine ⟨4113052969445300256732407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10968141251854134017953085 4113052969445300256732407)
              ·
                refine ⟨6169579454167950385098611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113052969445300256732407 6169579454167950385098611)
                ·
                  refine ⟨9254369181251925577647917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169579454167950385098611 9254369181251925577647917)
                  ·
                    refine ⟨3470388442969472091617969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9254369181251925577647917 3470388442969472091617969)
                    ·
                      refine ⟨2602791332227104068713477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470388442969472091617969 2602791332227104068713477)
                      ·
                        rfl

theorem cell23_5068918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5068918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068918 prefixEnd_5068918 := by exact prefixLift 5068918
  have htrace : WordTrace (prefixWord ++ tailWord_5068918) baseStart_5068918 baseEnd_5068918 := by
    simpa [prefixWord, tailWord_5068918, baseEnd_5068918] using wordTrace_append hprefix tailTrace_5068918
  have hstable : (prefixWord ++ tailWord_5068918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068918).length < 2 ^ (prefixWord ++ tailWord_5068918).sum := by decide
  have hdescent : baseEnd_5068918 < baseStart_5068918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068931 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 2, 2, 2]
def baseStart_5068931 : Nat := 118140960795 + 5068931 * 2 ^ 59
def prefixEnd_5068931 : Nat := 4983230072969 + 3 ^ 40 * 5068931 * 2
def baseEnd_5068931 : Nat := 2602798007475612517850917

theorem tailTrace_5068931 : CollatzResearch.WordTrace tailWord_5068931 prefixEnd_5068931 2602798007475612517850917 := by
  unfold tailWord_5068931
  simp only [CollatzResearch.WordTrace]
  refine ⟨184879101999136166337654647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123252734666090777558436431 184879101999136166337654647)
  ·
    refine ⟨277318652998704249506481971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184879101999136166337654647 277318652998704249506481971)
    ·
      refine ⟨415977979498056374259722957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277318652998704249506481971 415977979498056374259722957)
      ·
        refine ⟨155991742311771140347396109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 415977979498056374259722957 155991742311771140347396109)
        ·
          refine ⟨58496903366914177630273541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155991742311771140347396109 58496903366914177630273541)
          ·
            refine ⟨10968169381296408305676289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58496903366914177630273541 10968169381296408305676289)
            ·
              refine ⟨8226127035972306229257217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10968169381296408305676289 8226127035972306229257217)
              ·
                refine ⟨6169595276979229671942913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226127035972306229257217 6169595276979229671942913)
                ·
                  refine ⟨4627196457734422253957185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6169595276979229671942913 4627196457734422253957185)
                  ·
                    refine ⟨3470397343300816690467889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4627196457734422253957185 3470397343300816690467889)
                    ·
                      refine ⟨2602798007475612517850917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470397343300816690467889 2602798007475612517850917)
                      ·
                        rfl

theorem cell23_5068931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_5068931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068931 prefixEnd_5068931 := by exact prefixLift 5068931
  have htrace : WordTrace (prefixWord ++ tailWord_5068931) baseStart_5068931 baseEnd_5068931 := by
    simpa [prefixWord, tailWord_5068931, baseEnd_5068931] using wordTrace_append hprefix tailTrace_5068931
  have hstable : (prefixWord ++ tailWord_5068931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068931).length < 2 ^ (prefixWord ++ tailWord_5068931).sum := by decide
  have hdescent : baseEnd_5068931 < baseStart_5068931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068937 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 5]
def baseStart_5068937 : Nat := 118140960795 + 5068937 * 2 ^ 59
def prefixEnd_5068937 : Nat := 4983230072969 + 3 ^ 40 * 5068937 * 2
def baseEnd_5068937 : Nat := 289200120928837721597321

theorem tailTrace_5068937 : CollatzResearch.WordTrace tailWord_5068937 prefixEnd_5068937 289200120928837721597321 := by
  unfold tailWord_5068937
  simp only [CollatzResearch.WordTrace]
  refine ⟨184879320837114429362373065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123252880558076286241582043 184879320837114429362373065)
  ·
    refine ⟨138659490627835822021779799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184879320837114429362373065 138659490627835822021779799)
    ·
      refine ⟨207989235941753733032669699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138659490627835822021779799 207989235941753733032669699)
      ·
        refine ⟨311983853912630599549004549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207989235941753733032669699 311983853912630599549004549)
        ·
          refine ⟨58496972608618237415438353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311983853912630599549004549 58496972608618237415438353)
          ·
            refine ⟨43872729456463678061578765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58496972608618237415438353 43872729456463678061578765)
            ·
              refine ⟨16452273546173879273092037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43872729456463678061578765 16452273546173879273092037)
              ·
                refine ⟨3084801289907602363704757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16452273546173879273092037 3084801289907602363704757)
                ·
                  refine ⟨289200120928837721597321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3084801289907602363704757 289200120928837721597321)
                  ·
                    rfl

theorem cell23_5068937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 5].length) (baseStart_5068937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068937 prefixEnd_5068937 := by exact prefixLift 5068937
  have htrace : WordTrace (prefixWord ++ tailWord_5068937) baseStart_5068937 baseEnd_5068937 := by
    simpa [prefixWord, tailWord_5068937, baseEnd_5068937] using wordTrace_append hprefix tailTrace_5068937
  have hstable : (prefixWord ++ tailWord_5068937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068937).length < 2 ^ (prefixWord ++ tailWord_5068937).sum := by decide
  have hdescent : baseEnd_5068937 < baseStart_5068937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068948 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5068948 : Nat := 118140960795 + 5068948 * 2 ^ 59
def prefixEnd_5068948 : Nat := 4983230072969 + 3 ^ 40 * 5068948 * 2
def baseEnd_5068948 : Nat := 2602806736646738951338339

theorem tailTrace_5068948 : CollatzResearch.WordTrace tailWord_5068948 prefixEnd_5068948 2602806736646738951338339 := by
  unfold tailWord_5068948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92439861020037289120511749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123253148026716385494015665 92439861020037289120511749)
  ·
    refine ⟨17332473941256991710095953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92439861020037289120511749 17332473941256991710095953)
    ·
      refine ⟨12999355455942743782571965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17332473941256991710095953 12999355455942743782571965)
      ·
        refine ⟨4874758295978528918464487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12999355455942743782571965 4874758295978528918464487)
        ·
          refine ⟨7312137443967793377696731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874758295978528918464487 7312137443967793377696731)
          ·
            refine ⟨10968206165951690066545097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312137443967793377696731 10968206165951690066545097)
            ·
              refine ⟨8226154624463767549908823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10968206165951690066545097 8226154624463767549908823)
              ·
                refine ⟨12339231936695651324863235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8226154624463767549908823 12339231936695651324863235)
                ·
                  refine ⟨18508847905043476987294853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339231936695651324863235 18508847905043476987294853)
                  ·
                    refine ⟨3470408982195651935117785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18508847905043476987294853 3470408982195651935117785)
                    ·
                      refine ⟨2602806736646738951338339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470408982195651935117785 2602806736646738951338339)
                      ·
                        rfl

theorem cell23_5068948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5068948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068948 prefixEnd_5068948 := by exact prefixLift 5068948
  have htrace : WordTrace (prefixWord ++ tailWord_5068948) baseStart_5068948 baseEnd_5068948 := by
    simpa [prefixWord, tailWord_5068948, baseEnd_5068948] using wordTrace_append hprefix tailTrace_5068948
  have hstable : (prefixWord ++ tailWord_5068948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068948).length < 2 ^ (prefixWord ++ tailWord_5068948).sum := by decide
  have hdescent : baseEnd_5068948 < baseStart_5068948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068987 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 4, 4, 2]
def baseStart_5068987 : Nat := 118140960795 + 5068987 * 2 ^ 59
def prefixEnd_5068987 : Nat := 4983230072969 + 3 ^ 40 * 5068987 * 2
def baseEnd_5068987 : Nat := 2602826762392264298750659

theorem tailTrace_5068987 : CollatzResearch.WordTrace tailWord_5068987 prefixEnd_5068987 2602826762392264298750659 := by
  unfold tailWord_5068987
  simp only [CollatzResearch.WordTrace]
  refine ⟨184881144486933287901693215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123254096324622191934462143 184881144486933287901693215)
  ·
    refine ⟨277321716730399931852539823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184881144486933287901693215 277321716730399931852539823)
    ·
      refine ⟨415982575095599897778809735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277321716730399931852539823 415982575095599897778809735)
      ·
        refine ⟨623973862643399846668214603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415982575095599897778809735 623973862643399846668214603)
        ·
          refine ⟨935960793965099770002321905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623973862643399846668214603 935960793965099770002321905)
          ·
            refine ⟨701970595473824827501741429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935960793965099770002321905 701970595473824827501741429)
            ·
              refine ⟨65809743325671077578288259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 701970595473824827501741429 65809743325671077578288259)
              ·
                refine ⟨98714614988506616367432389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65809743325671077578288259 98714614988506616367432389)
                ·
                  refine ⟨18508990310344990568893573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98714614988506616367432389 18508990310344990568893573)
                  ·
                    refine ⟨3470435683189685731667545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18508990310344990568893573 3470435683189685731667545)
                    ·
                      refine ⟨2602826762392264298750659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470435683189685731667545 2602826762392264298750659)
                      ·
                        rfl

theorem cell23_5068987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4, 2].length) (baseStart_5068987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068987 prefixEnd_5068987 := by exact prefixLift 5068987
  have htrace : WordTrace (prefixWord ++ tailWord_5068987) baseStart_5068987 baseEnd_5068987 := by
    simpa [prefixWord, tailWord_5068987, baseEnd_5068987] using wordTrace_append hprefix tailTrace_5068987
  have hstable : (prefixWord ++ tailWord_5068987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068987).length < 2 ^ (prefixWord ++ tailWord_5068987).sum := by decide
  have hdescent : baseEnd_5068987 < baseStart_5068987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5068997 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_5068997 : Nat := 118140960795 + 5068997 * 2 ^ 59
def prefixEnd_5068997 : Nat := 4983230072969 + 3 ^ 40 * 5068997 * 2
def baseEnd_5068997 : Nat := 867610632399603086541871

theorem tailTrace_5068997 : CollatzResearch.WordTrace tailWord_5068997 prefixEnd_5068997 867610632399603086541871 := by
  unfold tailWord_5068997
  simp only [CollatzResearch.WordTrace]
  refine ⟨184881509216897059609557245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123254339477931373073038163 184881509216897059609557245)
  ·
    refine ⟨69330565956336397353583967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184881509216897059609557245 69330565956336397353583967)
    ·
      refine ⟨103995848934504596030375951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69330565956336397353583967 103995848934504596030375951)
      ·
        refine ⟨155993773401756894045563927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103995848934504596030375951 155993773401756894045563927)
        ·
          refine ⟨233990660102635341068345891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155993773401756894045563927 233990660102635341068345891)
          ·
            refine ⟨350985990153953011602518837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233990660102635341068345891 350985990153953011602518837)
            ·
              refine ⟨32904936576933094837736141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350985990153953011602518837 32904936576933094837736141)
              ·
                refine ⟨12339351216349910564151053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32904936576933094837736141 12339351216349910564151053)
                ·
                  refine ⟨4627256706131216461556645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12339351216349910564151053 4627256706131216461556645)
                  ·
                    refine ⟨867610632399603086541871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627256706131216461556645 867610632399603086541871)
                    ·
                      rfl

theorem cell23_5068997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_5068997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5068997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5068997 prefixEnd_5068997 := by exact prefixLift 5068997
  have htrace : WordTrace (prefixWord ++ tailWord_5068997) baseStart_5068997 baseEnd_5068997 := by
    simpa [prefixWord, tailWord_5068997, baseEnd_5068997] using wordTrace_append hprefix tailTrace_5068997
  have hstable : (prefixWord ++ tailWord_5068997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5068997).length < 2 ^ (prefixWord ++ tailWord_5068997).sum := by decide
  have hdescent : baseEnd_5068997 < baseStart_5068997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5068997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069000 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_5069000 : Nat := 118140960795 + 5069000 * 2 ^ 59
def prefixEnd_5069000 : Nat := 4983230072969 + 3 ^ 40 * 5069000 * 2
def baseEnd_5069000 : Nat := 2602833437640772747888099

theorem tailTrace_5069000 : CollatzResearch.WordTrace tailWord_5069000 prefixEnd_5069000 2602833437640772747888099 := by
  unfold tailWord_5069000
  simp only [CollatzResearch.WordTrace]
  refine ⟨92440809317943095560958227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123254412423924127414610969 92440809317943095560958227)
  ·
    refine ⟨138661213976914643341437341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92440809317943095560958227 138661213976914643341437341)
    ·
      refine ⟨51997955241342991253039003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138661213976914643341437341 51997955241342991253039003)
      ·
        refine ⟨77996932862014486879558505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51997955241342991253039003 77996932862014486879558505)
        ·
          refine ⟨58497699646510865159668879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77996932862014486879558505 58497699646510865159668879)
          ·
            refine ⟨87746549469766297739503319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58497699646510865159668879 87746549469766297739503319)
            ·
              refine ⟨131619824204649446609254979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87746549469766297739503319 131619824204649446609254979)
              ·
                refine ⟨197429736306974169913882469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131619824204649446609254979 197429736306974169913882469)
                ·
                  refine ⟨37018075557557656858852963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197429736306974169913882469 37018075557557656858852963)
                  ·
                    refine ⟨55527113336336485288279445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37018075557557656858852963 55527113336336485288279445)
                    ·
                      refine ⟨2602833437640772747888099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55527113336336485288279445 2602833437640772747888099)
                      ·
                        rfl

theorem cell23_5069000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_5069000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069000 prefixEnd_5069000 := by exact prefixLift 5069000
  have htrace : WordTrace (prefixWord ++ tailWord_5069000) baseStart_5069000 baseEnd_5069000 := by
    simpa [prefixWord, tailWord_5069000, baseEnd_5069000] using wordTrace_append hprefix tailTrace_5069000
  have hstable : (prefixWord ++ tailWord_5069000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069000).length < 2 ^ (prefixWord ++ tailWord_5069000).sum := by decide
  have hdescent : baseEnd_5069000 < baseStart_5069000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069057 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_5069057 : Nat := 118140960795 + 5069057 * 2 ^ 59
def prefixEnd_5069057 : Nat := 4983230072969 + 3 ^ 40 * 5069057 * 2
def baseEnd_5069057 : Nat := 867620902012693008291779

theorem tailTrace_5069057 : CollatzResearch.WordTrace tailWord_5069057 prefixEnd_5069057 867620902012693008291779 := by
  unfold tailWord_5069057
  simp only [CollatzResearch.WordTrace]
  refine ⟨184883697596679689856741425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123255798397786459904494283 184883697596679689856741425)
  ·
    refine ⟨138662773197509767392556069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184883697596679689856741425 138662773197509767392556069)
    ·
      refine ⟨25999269974533081386104263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138662773197509767392556069 25999269974533081386104263)
      ·
        refine ⟨38998904961799622079156395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25999269974533081386104263 38998904961799622079156395)
        ·
          refine ⟨58498357442699433118734593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38998904961799622079156395 58498357442699433118734593)
          ·
            refine ⟨43873768082024574839050945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58498357442699433118734593 43873768082024574839050945)
            ·
              refine ⟨32905326061518431129288209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43873768082024574839050945 32905326061518431129288209)
              ·
                refine ⟨24678994546138823346966157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32905326061518431129288209 24678994546138823346966157)
                ·
                  refine ⟨9254622954802058755112309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24678994546138823346966157 9254622954802058755112309)
                  ·
                    refine ⟨867620902012693008291779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9254622954802058755112309 867620902012693008291779)
                    ·
                      rfl

theorem cell23_5069057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_5069057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069057 prefixEnd_5069057 := by exact prefixLift 5069057
  have htrace : WordTrace (prefixWord ++ tailWord_5069057) baseStart_5069057 baseEnd_5069057 := by
    simpa [prefixWord, tailWord_5069057, baseEnd_5069057] using wordTrace_append hprefix tailTrace_5069057
  have hstable : (prefixWord ++ tailWord_5069057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069057).length < 2 ^ (prefixWord ++ tailWord_5069057).sum := by decide
  have hdescent : baseEnd_5069057 < baseStart_5069057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069087 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 3, 6]
def baseStart_5069087 : Nat := 118140960795 + 5069087 * 2 ^ 59
def prefixEnd_5069087 : Nat := 4983230072969 + 3 ^ 40 * 5069087 * 2
def baseEnd_5069087 : Nat := 867626036819237969166733

theorem tailTrace_5069087 : CollatzResearch.WordTrace tailWord_5069087 prefixEnd_5069087 867626036819237969166733 := by
  unfold tailWord_5069087
  simp only [CollatzResearch.WordTrace]
  refine ⟨184884791786571004980333515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123256527857714003320222343 184884791786571004980333515)
  ·
    refine ⟨277327187679856507470500273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184884791786571004980333515 277327187679856507470500273)
    ·
      refine ⟨207995390759892380602875205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277327187679856507470500273 207995390759892380602875205)
      ·
        refine ⟨38999135767479821363039101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207995390759892380602875205 38999135767479821363039101)
        ·
          refine ⟨14624675912804933011139663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38999135767479821363039101 14624675912804933011139663)
          ·
            refine ⟨21937013869207399516709495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14624675912804933011139663 21937013869207399516709495)
            ·
              refine ⟨32905520803811099275064243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21937013869207399516709495 32905520803811099275064243)
              ·
                refine ⟨49358281205716648912596365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32905520803811099275064243 49358281205716648912596365)
                ·
                  refine ⟨18509355452143743342223637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49358281205716648912596365 18509355452143743342223637)
                  ·
                    refine ⟨867626036819237969166733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18509355452143743342223637 867626036819237969166733)
                    ·
                      rfl

theorem cell23_5069087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_5069087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069087 prefixEnd_5069087 := by exact prefixLift 5069087
  have htrace : WordTrace (prefixWord ++ tailWord_5069087) baseStart_5069087 baseEnd_5069087 := by
    simpa [prefixWord, tailWord_5069087, baseEnd_5069087] using wordTrace_append hprefix tailTrace_5069087
  have hstable : (prefixWord ++ tailWord_5069087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069087).length < 2 ^ (prefixWord ++ tailWord_5069087).sum := by decide
  have hdescent : baseEnd_5069087 < baseStart_5069087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069107 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_5069107 : Nat := 118140960795 + 5069107 * 2 ^ 59
def prefixEnd_5069107 : Nat := 4983230072969 + 3 ^ 40 * 5069107 * 2
def baseEnd_5069107 : Nat := 2602888380070803829250107

theorem tailTrace_5069107 : CollatzResearch.WordTrace tailWord_5069107 prefixEnd_5069107 2602888380070803829250107 := by
  unfold tailWord_5069107
  simp only [CollatzResearch.WordTrace]
  refine ⟨184885521246498548396061575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123257014164332365597374383 184885521246498548396061575)
  ·
    refine ⟨277328281869747822594092363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184885521246498548396061575 277328281869747822594092363)
    ·
      refine ⟨415992422804621733891138545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277328281869747822594092363 415992422804621733891138545)
      ·
        refine ⟨311994317103466300418353909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415992422804621733891138545 311994317103466300418353909)
        ·
          refine ⟨29249467228449965664220679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 311994317103466300418353909 29249467228449965664220679)
          ·
            refine ⟨43874200842674948496331019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29249467228449965664220679 43874200842674948496331019)
            ·
              refine ⟨65811301264012422744496529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43874200842674948496331019 65811301264012422744496529)
              ·
                refine ⟨49358475948009317058372397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65811301264012422744496529 49358475948009317058372397)
                ·
                  refine ⟨18509428480503493896889649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49358475948009317058372397 18509428480503493896889649)
                  ·
                    refine ⟨13882071360377620422667237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18509428480503493896889649 13882071360377620422667237)
                    ·
                      refine ⟨2602888380070803829250107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13882071360377620422667237 2602888380070803829250107)
                      ·
                        rfl

theorem cell23_5069107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_5069107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069107 prefixEnd_5069107 := by exact prefixLift 5069107
  have htrace : WordTrace (prefixWord ++ tailWord_5069107) baseStart_5069107 baseEnd_5069107 := by
    simpa [prefixWord, tailWord_5069107, baseEnd_5069107] using wordTrace_append hprefix tailTrace_5069107
  have hstable : (prefixWord ++ tailWord_5069107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069107).length < 2 ^ (prefixWord ++ tailWord_5069107).sum := by decide
  have hdescent : baseEnd_5069107 < baseStart_5069107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069114 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_5069114 : Nat := 118140960795 + 5069114 * 2 ^ 59
def prefixEnd_5069114 : Nat := 4983230072969 + 3 ^ 40 * 5069114 * 2
def baseEnd_5069114 : Nat := 2602891974435385301862575

theorem tailTrace_5069114 : CollatzResearch.WordTrace tailWord_5069114 prefixEnd_5069114 2602891974435385301862575 := by
  unfold tailWord_5069114
  simp only [CollatzResearch.WordTrace]
  refine ⟨46221444139368297147891599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123257184371648792394377597 46221444139368297147891599)
  ·
    refine ⟨69332166209052445721837399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46221444139368297147891599 69332166209052445721837399)
    ·
      refine ⟨103998249313578668582756099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69332166209052445721837399 103998249313578668582756099)
      ·
        refine ⟨155997373970368002874134149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103998249313578668582756099 155997373970368002874134149)
        ·
          refine ⟨29249507619444000538900153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155997373970368002874134149 29249507619444000538900153)
          ·
            refine ⟨21937130714583000404175115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29249507619444000538900153 21937130714583000404175115)
            ·
              refine ⟨32905696071874500606262673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21937130714583000404175115 32905696071874500606262673)
              ·
                refine ⟨24679272053905875454697005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32905696071874500606262673 24679272053905875454697005)
                ·
                  refine ⟨9254727020214703295511377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24679272053905875454697005 9254727020214703295511377)
                  ·
                    refine ⟨6941045265161027471633533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9254727020214703295511377 6941045265161027471633533)
                    ·
                      refine ⟨2602891974435385301862575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941045265161027471633533 2602891974435385301862575)
                      ·
                        rfl

theorem cell23_5069114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_5069114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069114 prefixEnd_5069114 := by exact prefixLift 5069114
  have htrace : WordTrace (prefixWord ++ tailWord_5069114) baseStart_5069114 baseEnd_5069114 := by
    simpa [prefixWord, tailWord_5069114, baseEnd_5069114] using wordTrace_append hprefix tailTrace_5069114
  have hstable : (prefixWord ++ tailWord_5069114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069114).length < 2 ^ (prefixWord ++ tailWord_5069114).sum := by decide
  have hdescent : baseEnd_5069114 < baseStart_5069114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069121 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5069121 : Nat := 118140960795 + 5069121 * 2 ^ 59
def prefixEnd_5069121 : Nat := 4983230072969 + 3 ^ 40 * 5069121 * 2
def baseEnd_5069121 : Nat := 867631856266655591491681

theorem tailTrace_5069121 : CollatzResearch.WordTrace tailWord_5069121 prefixEnd_5069121 867631856266655591491681 := by
  unfold tailWord_5069121
  simp only [CollatzResearch.WordTrace]
  refine ⟨184886031868447828787071217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123257354578965219191380811 184886031868447828787071217)
  ·
    refine ⟨138664523901335871590303413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184886031868447828787071217 138664523901335871590303413)
    ·
      refine ⟨12999799115750237961590945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138664523901335871590303413 12999799115750237961590945)
      ·
        refine ⟨9749849336812678471193209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12999799115750237961590945 9749849336812678471193209)
        ·
          refine ⟨7312387002609508853394907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9749849336812678471193209 7312387002609508853394907)
          ·
            refine ⟨10968580503914263280092361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312387002609508853394907 10968580503914263280092361)
            ·
              refine ⟨8226435377935697460069271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10968580503914263280092361 8226435377935697460069271)
              ·
                refine ⟨12339653066903546190103907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8226435377935697460069271 12339653066903546190103907)
                ·
                  refine ⟨18509479600355319285155861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339653066903546190103907 18509479600355319285155861)
                  ·
                    refine ⟨867631856266655591491681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18509479600355319285155861 867631856266655591491681)
                    ·
                      rfl

theorem cell23_5069121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5069121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069121 prefixEnd_5069121 := by exact prefixLift 5069121
  have htrace : WordTrace (prefixWord ++ tailWord_5069121) baseStart_5069121 baseEnd_5069121 := by
    simpa [prefixWord, tailWord_5069121, baseEnd_5069121] using wordTrace_append hprefix tailTrace_5069121
  have hstable : (prefixWord ++ tailWord_5069121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069121).length < 2 ^ (prefixWord ++ tailWord_5069121).sum := by decide
  have hdescent : baseEnd_5069121 < baseStart_5069121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069167 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_5069167 : Nat := 118140960795 + 5069167 * 2 ^ 59
def prefixEnd_5069167 : Nat := 4983230072969 + 3 ^ 40 * 5069167 * 2
def baseEnd_5069167 : Nat := 2602919188910073594499831

theorem tailTrace_5069167 : CollatzResearch.WordTrace tailWord_5069167 prefixEnd_5069167 2602919188910073594499831 := by
  unfold tailWord_5069167
  simp only [CollatzResearch.WordTrace]
  refine ⟨184887709626281178643245755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123258473084187452428830503 184887709626281178643245755)
  ·
    refine ⟨277331564439421767964868633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184887709626281178643245755 277331564439421767964868633)
    ·
      refine ⟨207998673329566325973651475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277331564439421767964868633 207998673329566325973651475)
      ·
        refine ⟨311998009994349488960477213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207998673329566325973651475 311998009994349488960477213)
        ·
          refine ⟨116999253747881058360178955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311998009994349488960477213 116999253747881058360178955)
          ·
            refine ⟨175498880621821587540268433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116999253747881058360178955 175498880621821587540268433)
            ·
              refine ⟨131624160466366190655201325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175498880621821587540268433 131624160466366190655201325)
              ·
                refine ⟨49359060174887321495700497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131624160466366190655201325 49359060174887321495700497)
                ·
                  refine ⟨37019295131165491121775373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49359060174887321495700497 37019295131165491121775373)
                  ·
                    refine ⟨13882235674187059170665765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37019295131165491121775373 13882235674187059170665765)
                    ·
                      refine ⟨2602919188910073594499831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13882235674187059170665765 2602919188910073594499831)
                      ·
                        rfl

theorem cell23_5069167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_5069167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069167 prefixEnd_5069167 := by exact prefixLift 5069167
  have htrace : WordTrace (prefixWord ++ tailWord_5069167) baseStart_5069167 baseEnd_5069167 := by
    simpa [prefixWord, tailWord_5069167, baseEnd_5069167] using wordTrace_append hprefix tailTrace_5069167
  have hstable : (prefixWord ++ tailWord_5069167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069167).length < 2 ^ (prefixWord ++ tailWord_5069167).sum := by decide
  have hdescent : baseEnd_5069167 < baseStart_5069167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069188 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_5069188 : Nat := 118140960795 + 5069188 * 2 ^ 59
def prefixEnd_5069188 : Nat := 4983230072969 + 3 ^ 40 * 5069188 * 2
def baseEnd_5069188 : Nat := 2602929972003818012337235

theorem tailTrace_5069188 : CollatzResearch.WordTrace tailWord_5069188 prefixEnd_5069188 2602929972003818012337235 := by
  unfold tailWord_5069188
  simp only [CollatzResearch.WordTrace]
  refine ⟨92444237779602549614880109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123258983706136732819840145 92444237779602549614880109)
  ·
    refine ⟨34666589167350956105580041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92444237779602549614880109 34666589167350956105580041)
    ·
      refine ⟨25999941875513217079185031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34666589167350956105580041 25999941875513217079185031)
      ·
        refine ⟨38999912813269825618777547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25999941875513217079185031 38999912813269825618777547)
        ·
          refine ⟨58499869219904738428166321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38999912813269825618777547 58499869219904738428166321)
          ·
            refine ⟨43874901914928553821124741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58499869219904738428166321 43874901914928553821124741)
            ·
              refine ⟨8226544109049103841460889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43874901914928553821124741 8226544109049103841460889)
              ·
                refine ⟨6169908081786827881095667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226544109049103841460889 6169908081786827881095667)
                ·
                  refine ⟨9254862122680241821643501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169908081786827881095667 9254862122680241821643501)
                  ·
                    refine ⟨3470573296005090683116313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9254862122680241821643501 3470573296005090683116313)
                    ·
                      refine ⟨2602929972003818012337235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470573296005090683116313 2602929972003818012337235)
                      ·
                        rfl

theorem cell23_5069188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_5069188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069188 prefixEnd_5069188 := by exact prefixLift 5069188
  have htrace : WordTrace (prefixWord ++ tailWord_5069188) baseStart_5069188 baseEnd_5069188 := by
    simpa [prefixWord, tailWord_5069188, baseEnd_5069188] using wordTrace_append hprefix tailTrace_5069188
  have hstable : (prefixWord ++ tailWord_5069188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069188).length < 2 ^ (prefixWord ++ tailWord_5069188).sum := by decide
  have hdescent : baseEnd_5069188 < baseStart_5069188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069207 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 9]
def baseStart_5069207 : Nat := 118140960795 + 5069207 * 2 ^ 59
def prefixEnd_5069207 : Nat := 4983230072969 + 3 ^ 40 * 5069207 * 2
def baseEnd_5069207 : Nat := 289215525348472604222183

theorem tailTrace_5069207 : CollatzResearch.WordTrace tailWord_5069207 prefixEnd_5069207 289215525348472604222183 := by
  unfold tailWord_5069207
  simp only [CollatzResearch.WordTrace]
  refine ⟨184889168546136265474701875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123259445697424176983134583 184889168546136265474701875)
  ·
    refine ⟨277333752819204398212052813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184889168546136265474701875 277333752819204398212052813)
    ·
      refine ⟨104000157307201649329519805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277333752819204398212052813 104000157307201649329519805)
      ·
        refine ⟨39000058990200618498569927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104000157307201649329519805 39000058990200618498569927)
        ·
          refine ⟨58500088485300927747854891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39000058990200618498569927 58500088485300927747854891)
          ·
            refine ⟨87750132727951391621782337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58500088485300927747854891 87750132727951391621782337)
            ·
              refine ⟨65812599545963543716336753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87750132727951391621782337 65812599545963543716336753)
              ·
                refine ⟨49359449659472657787252565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65812599545963543716336753 49359449659472657787252565)
                ·
                  refine ⟨289215525348472604222183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49359449659472657787252565 289215525348472604222183)
                  ·
                    rfl

theorem cell23_5069207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 9].length) (baseStart_5069207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069207 prefixEnd_5069207 := by exact prefixLift 5069207
  have htrace : WordTrace (prefixWord ++ tailWord_5069207) baseStart_5069207 baseEnd_5069207 := by
    simpa [prefixWord, tailWord_5069207, baseEnd_5069207] using wordTrace_append hprefix tailTrace_5069207
  have hstable : (prefixWord ++ tailWord_5069207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069207).length < 2 ^ (prefixWord ++ tailWord_5069207).sum := by decide
  have hdescent : baseEnd_5069207 < baseStart_5069207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069218 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_5069218 : Nat := 118140960795 + 5069218 * 2 ^ 59
def prefixEnd_5069218 : Nat := 4983230072969 + 3 ^ 40 * 5069218 * 2
def baseEnd_5069218 : Nat := 2602945376423452894962097

theorem tailTrace_5069218 : CollatzResearch.WordTrace tailWord_5069218 prefixEnd_5069218 2602945376423452894962097 := by
  unfold tailWord_5069218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46222392437274103588338077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123259713166064276235568205 46222392437274103588338077)
  ·
    refine ⟨17333397163977788845626779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46222392437274103588338077 17333397163977788845626779)
    ·
      refine ⟨26000095745966683268440169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17333397163977788845626779 26000095745966683268440169)
      ·
        refine ⟨19500071809475012451330127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26000095745966683268440169 19500071809475012451330127)
        ·
          refine ⟨29250107714212518676995191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19500071809475012451330127 29250107714212518676995191)
          ·
            refine ⟨43875161571318778015492787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29250107714212518676995191 43875161571318778015492787)
            ·
              refine ⟨65812742356978167023239181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43875161571318778015492787 65812742356978167023239181)
              ·
                refine ⟨24679778383866812633714693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65812742356978167023239181 24679778383866812633714693)
                ·
                  refine ⟨4627458446975027368821505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24679778383866812633714693 4627458446975027368821505)
                  ·
                    refine ⟨3470593835231270526616129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4627458446975027368821505 3470593835231270526616129)
                    ·
                      refine ⟨2602945376423452894962097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470593835231270526616129 2602945376423452894962097)
                      ·
                        rfl

theorem cell23_5069218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_5069218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069218 prefixEnd_5069218 := by exact prefixLift 5069218
  have htrace : WordTrace (prefixWord ++ tailWord_5069218) baseStart_5069218 baseEnd_5069218 := by
    simpa [prefixWord, tailWord_5069218, baseEnd_5069218] using wordTrace_append hprefix tailTrace_5069218
  have hstable : (prefixWord ++ tailWord_5069218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069218).length < 2 ^ (prefixWord ++ tailWord_5069218).sum := by decide
  have hdescent : baseEnd_5069218 < baseStart_5069218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069229 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5069229 : Nat := 118140960795 + 5069229 * 2 ^ 59
def prefixEnd_5069229 : Nat := 4983230072969 + 3 ^ 40 * 5069229 * 2
def baseEnd_5069229 : Nat := 2602951024710652351924547

theorem tailTrace_5069229 : CollatzResearch.WordTrace tailWord_5069229 prefixEnd_5069229 2602951024710652351924547 := by
  unfold tailWord_5069229
  simp only [CollatzResearch.WordTrace]
  refine ⟨184889970952056563232002741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123259980634704375488001827 184889970952056563232002741)
  ·
    refine ⟨17333434776755302803000257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184889970952056563232002741 17333434776755302803000257)
    ·
      refine ⟨13000076082566477102250193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17333434776755302803000257 13000076082566477102250193)
      ·
        refine ⟨9750057061924857826687645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13000076082566477102250193 9750057061924857826687645)
        ·
          refine ⟨3656271398221821685007867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9750057061924857826687645 3656271398221821685007867)
          ·
            refine ⟨5484407097332732527511801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656271398221821685007867 5484407097332732527511801)
            ·
              refine ⟨4113305322999549395633851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5484407097332732527511801 4113305322999549395633851)
              ·
                refine ⟨6169957984499324093450777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113305322999549395633851 6169957984499324093450777)
                ·
                  refine ⟨4627468488374493070088083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6169957984499324093450777 4627468488374493070088083)
                  ·
                    refine ⟨6941202732561739605132125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4627468488374493070088083 6941202732561739605132125)
                    ·
                      refine ⟨2602951024710652351924547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941202732561739605132125 2602951024710652351924547)
                      ·
                        rfl

theorem cell23_5069229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5069229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069229 prefixEnd_5069229 := by exact prefixLift 5069229
  have htrace : WordTrace (prefixWord ++ tailWord_5069229) baseStart_5069229 baseEnd_5069229 := by
    simpa [prefixWord, tailWord_5069229, baseEnd_5069229] using wordTrace_append hprefix tailTrace_5069229
  have hstable : (prefixWord ++ tailWord_5069229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069229).length < 2 ^ (prefixWord ++ tailWord_5069229).sum := by decide
  have hdescent : baseEnd_5069229 < baseStart_5069229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069234 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_5069234 : Nat := 118140960795 + 5069234 * 2 ^ 59
def prefixEnd_5069234 : Nat := 4983230072969 + 3 ^ 40 * 5069234 * 2
def baseEnd_5069234 : Nat := 2602953592113924832362023

theorem tailTrace_5069234 : CollatzResearch.WordTrace tailWord_5069234 prefixEnd_5069234 2602953592113924832362023 := by
  unfold tailWord_5069234
  simp only [CollatzResearch.WordTrace]
  refine ⟨46222538329259612271483689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123260102211358966057289837 46222538329259612271483689)
  ·
    refine ⟨34666903746944709203612767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46222538329259612271483689 34666903746944709203612767)
    ·
      refine ⟨52000355620417063805419151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34666903746944709203612767 52000355620417063805419151)
      ·
        refine ⟨78000533430625595708128727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52000355620417063805419151 78000533430625595708128727)
        ·
          refine ⟨117000800145938393562193091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78000533430625595708128727 117000800145938393562193091)
          ·
            refine ⟨175501200218907590343289637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117000800145938393562193091 175501200218907590343289637)
            ·
              refine ⟨32906475041045173189366807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175501200218907590343289637 32906475041045173189366807)
              ·
                refine ⟨49359712561567759784050211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32906475041045173189366807 49359712561567759784050211)
                ·
                  refine ⟨74039568842351639676075317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49359712561567759784050211 74039568842351639676075317)
                  ·
                    refine ⟨6941209578970466219632061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74039568842351639676075317 6941209578970466219632061)
                    ·
                      refine ⟨2602953592113924832362023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941209578970466219632061 2602953592113924832362023)
                      ·
                        rfl

theorem cell23_5069234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_5069234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069234 prefixEnd_5069234 := by exact prefixLift 5069234
  have htrace : WordTrace (prefixWord ++ tailWord_5069234) baseStart_5069234 baseEnd_5069234 := by
    simpa [prefixWord, tailWord_5069234, baseEnd_5069234] using wordTrace_append hprefix tailTrace_5069234
  have hstable : (prefixWord ++ tailWord_5069234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069234).length < 2 ^ (prefixWord ++ tailWord_5069234).sum := by decide
  have hdescent : baseEnd_5069234 < baseStart_5069234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069267 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 8]
def baseStart_5069267 : Nat := 118140960795 + 5069267 * 2 ^ 59
def prefixEnd_5069267 : Nat := 4983230072969 + 3 ^ 40 * 5069267 * 2
def baseEnd_5069267 : Nat := 867656845658507734416457

theorem tailTrace_5069267 : CollatzResearch.WordTrace tailWord_5069267 prefixEnd_5069267 867656845658507734416457 := by
  unfold tailWord_5069267
  simp only [CollatzResearch.WordTrace]
  refine ⟨184891356925918895721886055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123260904617279263814590703 184891356925918895721886055)
  ·
    refine ⟨277337035388878343582829083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184891356925918895721886055 277337035388878343582829083)
    ·
      refine ⟨416005553083317515374243625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277337035388878343582829083 416005553083317515374243625)
      ·
        refine ⟨312004164812488136530682719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416005553083317515374243625 312004164812488136530682719)
        ·
          refine ⟨468006247218732204796024079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312004164812488136530682719 468006247218732204796024079)
          ·
            refine ⟨702009370828098307194036119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468006247218732204796024079 702009370828098307194036119)
            ·
              refine ⟨1053014056242147460791054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702009370828098307194036119 1053014056242147460791054179)
              ·
                refine ⟨1579521084363221191186581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053014056242147460791054179 1579521084363221191186581269)
                ·
                  refine ⟨74040050829525993336870997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1579521084363221191186581269 74040050829525993336870997)
                  ·
                    refine ⟨867656845658507734416457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74040050829525993336870997 867656845658507734416457)
                    ·
                      rfl

theorem cell23_5069267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_5069267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069267 prefixEnd_5069267 := by exact prefixLift 5069267
  have htrace : WordTrace (prefixWord ++ tailWord_5069267) baseStart_5069267 baseEnd_5069267 := by
    simpa [prefixWord, tailWord_5069267, baseEnd_5069267] using wordTrace_append hprefix tailTrace_5069267
  have hstable : (prefixWord ++ tailWord_5069267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069267).length < 2 ^ (prefixWord ++ tailWord_5069267).sum := by decide
  have hdescent : baseEnd_5069267 < baseStart_5069267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069291 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 2, 4, 2]
def baseStart_5069291 : Nat := 118140960795 + 5069291 * 2 ^ 59
def prefixEnd_5069291 : Nat := 4983230072969 + 3 ^ 40 * 5069291 * 2
def baseEnd_5069291 : Nat := 2602982860511231109349261

theorem tailTrace_5069291 : CollatzResearch.WordTrace tailWord_5069291 prefixEnd_5069291 2602982860511231109349261 := by
  unfold tailWord_5069291
  simp only [CollatzResearch.WordTrace]
  refine ⟨184892232277831947820759727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123261488185221298547173151 184892232277831947820759727)
  ·
    refine ⟨277338348416747921731139591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184892232277831947820759727 277338348416747921731139591)
    ·
      refine ⟨416007522625121882596709387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277338348416747921731139591 416007522625121882596709387)
      ·
        refine ⟨624011283937682823895064081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416007522625121882596709387 624011283937682823895064081)
        ·
          refine ⟨468008462953262117921298061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624011283937682823895064081 468008462953262117921298061)
          ·
            refine ⟨175503173607473294220486773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468008462953262117921298061 175503173607473294220486773)
            ·
              refine ⟨16453422525700621333170635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175503173607473294220486773 16453422525700621333170635)
              ·
                refine ⟨24680133788550931999755953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16453422525700621333170635 24680133788550931999755953)
                ·
                  refine ⟨18510100341413198999816965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24680133788550931999755953 18510100341413198999816965)
                  ·
                    refine ⟨3470643814014974812465681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18510100341413198999816965 3470643814014974812465681)
                    ·
                      refine ⟨2602982860511231109349261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470643814014974812465681 2602982860511231109349261)
                      ·
                        rfl

theorem cell23_5069291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4, 2].length) (baseStart_5069291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069291 prefixEnd_5069291 := by exact prefixLift 5069291
  have htrace : WordTrace (prefixWord ++ tailWord_5069291) baseStart_5069291 baseEnd_5069291 := by
    simpa [prefixWord, tailWord_5069291, baseEnd_5069291] using wordTrace_append hprefix tailTrace_5069291
  have hstable : (prefixWord ++ tailWord_5069291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069291).length < 2 ^ (prefixWord ++ tailWord_5069291).sum := by decide
  have hdescent : baseEnd_5069291 < baseStart_5069291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069335 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 3, 4]
def baseStart_5069335 : Nat := 118140960795 + 5069335 * 2 ^ 59
def prefixEnd_5069335 : Nat := 4983230072969 + 3 ^ 40 * 5069335 * 2
def baseEnd_5069335 : Nat := 867668484553342979066353

theorem tailTrace_5069335 : CollatzResearch.WordTrace tailWord_5069335 prefixEnd_5069335 867668484553342979066353 := by
  unfold tailWord_5069335
  simp only [CollatzResearch.WordTrace]
  refine ⟨184893837089672543335361459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123262558059781695556907639 184893837089672543335361459)
  ·
    refine ⟨277340755634508815003042189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184893837089672543335361459 277340755634508815003042189)
    ·
      refine ⟨104002783362940805626140821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277340755634508815003042189 104002783362940805626140821)
      ·
        refine ⟨4875130470137850263725351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104002783362940805626140821 4875130470137850263725351)
        ·
          refine ⟨7312695705206775395588027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875130470137850263725351 7312695705206775395588027)
          ·
            refine ⟨10969043557810163093382041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312695705206775395588027 10969043557810163093382041)
            ·
              refine ⟨8226782668357622320036531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10969043557810163093382041 8226782668357622320036531)
              ·
                refine ⟨12340174002536433480054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8226782668357622320036531 12340174002536433480054797)
                ·
                  refine ⟨4627565250951162555020549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12340174002536433480054797 4627565250951162555020549)
                  ·
                    refine ⟨867668484553342979066353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627565250951162555020549 867668484553342979066353)
                    ·
                      rfl

theorem cell23_5069335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_5069335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069335 prefixEnd_5069335 := by exact prefixLift 5069335
  have htrace : WordTrace (prefixWord ++ tailWord_5069335) baseStart_5069335 baseEnd_5069335 := by
    simpa [prefixWord, tailWord_5069335, baseEnd_5069335] using wordTrace_append hprefix tailTrace_5069335
  have hstable : (prefixWord ++ tailWord_5069335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069335).length < 2 ^ (prefixWord ++ tailWord_5069335).sum := by decide
  have hdescent : baseEnd_5069335 < baseStart_5069335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069361 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_5069361 : Nat := 118140960795 + 5069361 * 2 ^ 59
def prefixEnd_5069361 : Nat := 4983230072969 + 3 ^ 40 * 5069361 * 2
def baseEnd_5069361 : Nat := 867672934719015278491313

theorem tailTrace_5069361 : CollatzResearch.WordTrace tailWord_5069361 prefixEnd_5069361 867672934719015278491313 := by
  unfold tailWord_5069361
  simp only [CollatzResearch.WordTrace]
  refine ⟨184894785387578349775807937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123263190258385566517205291 184894785387578349775807937)
  ·
    refine ⟨138671089040683762331855953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184894785387578349775807937 138671089040683762331855953)
    ·
      refine ⟨104003316780512821748891965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138671089040683762331855953 104003316780512821748891965)
      ·
        refine ⟨39001243792692308155834487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104003316780512821748891965 39001243792692308155834487)
        ·
          refine ⟨58501865689038462233751731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39001243792692308155834487 58501865689038462233751731)
          ·
            refine ⟨87752798533557693350627597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58501865689038462233751731 87752798533557693350627597)
            ·
              refine ⟨32907299450084135006485349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87752798533557693350627597 32907299450084135006485349)
              ·
                refine ⟨6170118646890775313716003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32907299450084135006485349 6170118646890775313716003)
                ·
                  refine ⟨9255177970336162970574005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6170118646890775313716003 9255177970336162970574005)
                  ·
                    refine ⟨867672934719015278491313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9255177970336162970574005 867672934719015278491313)
                    ·
                      rfl

theorem cell23_5069361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_5069361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069361 prefixEnd_5069361 := by exact prefixLift 5069361
  have htrace : WordTrace (prefixWord ++ tailWord_5069361) baseStart_5069361 baseEnd_5069361 := by
    simpa [prefixWord, tailWord_5069361, baseEnd_5069361] using wordTrace_append hprefix tailTrace_5069361
  have hstable : (prefixWord ++ tailWord_5069361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069361).length < 2 ^ (prefixWord ++ tailWord_5069361).sum := by decide
  have hdescent : baseEnd_5069361 < baseStart_5069361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069368 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_5069368 : Nat := 118140960795 + 5069368 * 2 ^ 59
def prefixEnd_5069368 : Nat := 4983230072969 + 3 ^ 40 * 5069368 * 2
def baseEnd_5069368 : Nat := 2603022398521627308086407

theorem tailTrace_5069368 : CollatzResearch.WordTrace tailWord_5069368 prefixEnd_5069368 2603022398521627308086407 := by
  unfold tailWord_5069368
  simp only [CollatzResearch.WordTrace]
  refine ⟨92447520349276494985656379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123263360465701993314208505 92447520349276494985656379)
  ·
    refine ⟨138671280523914742478484569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92447520349276494985656379 138671280523914742478484569)
    ·
      refine ⟨104003460392936056858863427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138671280523914742478484569 104003460392936056858863427)
      ·
        refine ⟨156005190589404085288295141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104003460392936056858863427 156005190589404085288295141)
        ·
          refine ⟨29250973235513265991555339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156005190589404085288295141 29250973235513265991555339)
          ·
            refine ⟨43876459853269898987333009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29250973235513265991555339 43876459853269898987333009)
            ·
              refine ⟨32907344889952424240499757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43876459853269898987333009 32907344889952424240499757)
              ·
                refine ⟨12340254333732159090187409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32907344889952424240499757 12340254333732159090187409)
                ·
                  refine ⟨9255190750299119317640557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12340254333732159090187409 9255190750299119317640557)
                  ·
                    refine ⟨3470696531362169744115209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9255190750299119317640557 3470696531362169744115209)
                    ·
                      refine ⟨2603022398521627308086407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470696531362169744115209 2603022398521627308086407)
                      ·
                        rfl

theorem cell23_5069368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_5069368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069368 prefixEnd_5069368 := by exact prefixLift 5069368
  have htrace : WordTrace (prefixWord ++ tailWord_5069368) baseStart_5069368 baseEnd_5069368 := by
    simpa [prefixWord, tailWord_5069368, baseEnd_5069368] using wordTrace_append hprefix tailTrace_5069368
  have hstable : (prefixWord ++ tailWord_5069368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069368).length < 2 ^ (prefixWord ++ tailWord_5069368).sum := by decide
  have hdescent : baseEnd_5069368 < baseStart_5069368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069391 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 4, 4]
def baseStart_5069391 : Nat := 118140960795 + 5069391 * 2 ^ 59
def prefixEnd_5069391 : Nat := 4983230072969 + 3 ^ 40 * 5069391 * 2
def baseEnd_5069391 : Nat := 867678069525560239366267

theorem tailTrace_5069391 : CollatzResearch.WordTrace tailWord_5069391 prefixEnd_5069391 867678069525560239366267 := by
  unfold tailWord_5069391
  simp only [CollatzResearch.WordTrace]
  refine ⟨184895879577469664899400027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123263919718313109932933351 184895879577469664899400027)
  ·
    refine ⟨277343819366204497349100041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184895879577469664899400027 277343819366204497349100041)
    ·
      refine ⟨208007864524653373011825031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277343819366204497349100041 208007864524653373011825031)
      ·
        refine ⟨312011796786980059517737547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208007864524653373011825031 312011796786980059517737547)
        ·
          refine ⟨468017695180470089276606321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312011796786980059517737547 468017695180470089276606321)
          ·
            refine ⟨351013271385352566957454741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468017695180470089276606321 351013271385352566957454741)
            ·
              refine ⟨16453747096188401576130691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 351013271385352566957454741 16453747096188401576130691)
              ·
                refine ⟨24680620644282602364196037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16453747096188401576130691 24680620644282602364196037)
                ·
                  refine ⟨4627616370802987943286757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24680620644282602364196037 4627616370802987943286757)
                  ·
                    refine ⟨867678069525560239366267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627616370802987943286757 867678069525560239366267)
                    ·
                      rfl

theorem cell23_5069391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_5069391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069391 prefixEnd_5069391 := by exact prefixLift 5069391
  have htrace : WordTrace (prefixWord ++ tailWord_5069391) baseStart_5069391 baseEnd_5069391 := by
    simpa [prefixWord, tailWord_5069391, baseEnd_5069391] using wordTrace_append hprefix tailTrace_5069391
  have hstable : (prefixWord ++ tailWord_5069391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069391).length < 2 ^ (prefixWord ++ tailWord_5069391).sum := by decide
  have hdescent : baseEnd_5069391 < baseStart_5069391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069411 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5069411 : Nat := 118140960795 + 5069411 * 2 ^ 59
def prefixEnd_5069411 : Nat := 4983230072969 + 3 ^ 40 * 5069411 * 2
def baseEnd_5069411 : Nat := 2603044478189770639848709

theorem tailTrace_5069411 : CollatzResearch.WordTrace tailWord_5069411 prefixEnd_5069411 2603044478189770639848709 := by
  unfold tailWord_5069411
  simp only [CollatzResearch.WordTrace]
  refine ⟨184896609037397208315128087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123264406024931472210085391 184896609037397208315128087)
  ·
    refine ⟨277344913556095812472692131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184896609037397208315128087 277344913556095812472692131)
    ·
      refine ⟨416017370334143718709038197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277344913556095812472692131 416017370334143718709038197)
      ·
        refine ⟨39001628468825973628972331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 416017370334143718709038197 39001628468825973628972331)
        ·
          refine ⟨58502442703238960443458497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39001628468825973628972331 58502442703238960443458497)
          ·
            refine ⟨43876832027429220332593873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58502442703238960443458497 43876832027429220332593873)
            ·
              refine ⟨32907624020571915249445405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43876832027429220332593873 32907624020571915249445405)
              ·
                refine ⟨12340359007714468218542027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32907624020571915249445405 12340359007714468218542027)
                ·
                  refine ⟨18510538511571702327813041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12340359007714468218542027 18510538511571702327813041)
                  ·
                    refine ⟨13882903883678776745859781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18510538511571702327813041 13882903883678776745859781)
                    ·
                      refine ⟨2603044478189770639848709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13882903883678776745859781 2603044478189770639848709)
                      ·
                        rfl

theorem cell23_5069411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5069411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069411 prefixEnd_5069411 := by exact prefixLift 5069411
  have htrace : WordTrace (prefixWord ++ tailWord_5069411) baseStart_5069411 baseEnd_5069411 := by
    simpa [prefixWord, tailWord_5069411, baseEnd_5069411] using wordTrace_append hprefix tailTrace_5069411
  have hstable : (prefixWord ++ tailWord_5069411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069411).length < 2 ^ (prefixWord ++ tailWord_5069411).sum := by decide
  have hdescent : baseEnd_5069411 < baseStart_5069411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069418 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5069418 : Nat := 118140960795 + 5069418 * 2 ^ 59
def prefixEnd_5069418 : Nat := 4983230072969 + 3 ^ 40 * 5069418 * 2
def baseEnd_5069418 : Nat := 2603048072554352112461177

theorem tailTrace_5069418 : CollatzResearch.WordTrace tailWord_5069418 prefixEnd_5069418 2603048072554352112461177 := by
  unfold tailWord_5069418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46224216087092962127658227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123264576232247899007088605 46224216087092962127658227)
  ·
    refine ⟨69336324130639443191487341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46224216087092962127658227 69336324130639443191487341)
    ·
      refine ⟨26001121548989791196807753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69336324130639443191487341 26001121548989791196807753)
      ·
        refine ⟨19500841161742343397605815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26001121548989791196807753 19500841161742343397605815)
        ·
          refine ⟨29251261742613515096408723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19500841161742343397605815 29251261742613515096408723)
          ·
            refine ⟨43876892613920272644613085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29251261742613515096408723 43876892613920272644613085)
            ·
              refine ⟨16453834730220102241729907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43876892613920272644613085 16453834730220102241729907)
              ·
                refine ⟨24680752095330153362594861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16453834730220102241729907 24680752095330153362594861)
                ·
                  refine ⟨9255282035748807510973073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24680752095330153362594861 9255282035748807510973073)
                  ·
                    refine ⟨6941461526811605633229805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9255282035748807510973073 6941461526811605633229805)
                    ·
                      refine ⟨2603048072554352112461177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941461526811605633229805 2603048072554352112461177)
                      ·
                        rfl

theorem cell23_5069418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5069418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069418 prefixEnd_5069418 := by exact prefixLift 5069418
  have htrace : WordTrace (prefixWord ++ tailWord_5069418) baseStart_5069418 baseEnd_5069418 := by
    simpa [prefixWord, tailWord_5069418, baseEnd_5069418] using wordTrace_append hprefix tailTrace_5069418
  have hstable : (prefixWord ++ tailWord_5069418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069418).length < 2 ^ (prefixWord ++ tailWord_5069418).sum := by decide
  have hdescent : baseEnd_5069418 < baseStart_5069418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069421 : List Nat := [1, 5, 1, 1, 3, 1, 2, 9]
def baseStart_5069421 : Nat := 118140960795 + 5069421 * 2 ^ 59
def prefixEnd_5069421 : Nat := 4983230072969 + 3 ^ 40 * 5069421 * 2
def baseEnd_5069421 : Nat := 96409244925789466693469

theorem tailTrace_5069421 : CollatzResearch.WordTrace tailWord_5069421 prefixEnd_5069421 96409244925789466693469 := by
  unfold tailWord_5069421
  simp only [CollatzResearch.WordTrace]
  refine ⟨184896973767360980022992117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123264649178240653348661411 184896973767360980022992117)
  ·
    refine ⟨17334091290690091877155511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184896973767360980022992117 17334091290690091877155511)
    ·
      refine ⟨26001136936035137815733267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17334091290690091877155511 26001136936035137815733267)
      ·
        refine ⟨39001705404052706723599901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26001136936035137815733267 39001705404052706723599901)
        ·
          refine ⟨14625639526519765021349963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39001705404052706723599901 14625639526519765021349963)
          ·
            refine ⟨21938459289779647532024945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14625639526519765021349963 21938459289779647532024945)
            ·
              refine ⟨16453844467334735649018709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21938459289779647532024945 16453844467334735649018709)
              ·
                refine ⟨96409244925789466693469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16453844467334735649018709 96409244925789466693469)
                ·
                  rfl

theorem cell23_5069421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 9].length) (baseStart_5069421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069421 prefixEnd_5069421 := by exact prefixLift 5069421
  have htrace : WordTrace (prefixWord ++ tailWord_5069421) baseStart_5069421 baseEnd_5069421 := by
    simpa [prefixWord, tailWord_5069421, baseEnd_5069421] using wordTrace_append hprefix tailTrace_5069421
  have hstable : (prefixWord ++ tailWord_5069421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069421).length < 2 ^ (prefixWord ++ tailWord_5069421).sum := by decide
  have hdescent : baseEnd_5069421 < baseStart_5069421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069431 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_5069431 : Nat := 118140960795 + 5069431 * 2 ^ 59
def prefixEnd_5069431 : Nat := 4983230072969 + 3 ^ 40 * 5069431 * 2
def baseEnd_5069431 : Nat := 2603054747802860561598617

theorem tailTrace_5069431 : CollatzResearch.WordTrace tailWord_5069431 prefixEnd_5069431 2603054747802860561598617 := by
  unfold tailWord_5069431
  simp only [CollatzResearch.WordTrace]
  refine ⟨184897338497324751730856147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123264892331549834487237431 184897338497324751730856147)
  ·
    refine ⟨277346007745987127596284221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184897338497324751730856147 277346007745987127596284221)
    ·
      refine ⟨104004752904745172848606583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277346007745987127596284221 104004752904745172848606583)
      ·
        refine ⟨156007129357117759272909875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104004752904745172848606583 156007129357117759272909875)
        ·
          refine ⟨234010694035676638909364813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156007129357117759272909875 234010694035676638909364813)
          ·
            refine ⟨87754010263378739591011805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234010694035676638909364813 87754010263378739591011805)
            ·
              refine ⟨32907753848767027346629427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87754010263378739591011805 32907753848767027346629427)
              ·
                refine ⟨49361630773150541019944141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32907753848767027346629427 49361630773150541019944141)
                ·
                  refine ⟨18510611539931452882479053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49361630773150541019944141 18510611539931452882479053)
                  ·
                    refine ⟨6941479327474294830929645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18510611539931452882479053 6941479327474294830929645)
                    ·
                      refine ⟨2603054747802860561598617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941479327474294830929645 2603054747802860561598617)
                      ·
                        rfl

theorem cell23_5069431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_5069431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069431 prefixEnd_5069431 := by exact prefixLift 5069431
  have htrace : WordTrace (prefixWord ++ tailWord_5069431) baseStart_5069431 baseEnd_5069431 := by
    simpa [prefixWord, tailWord_5069431, baseEnd_5069431] using wordTrace_append hprefix tailTrace_5069431
  have hstable : (prefixWord ++ tailWord_5069431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069431).length < 2 ^ (prefixWord ++ tailWord_5069431).sum := by decide
  have hdescent : baseEnd_5069431 < baseStart_5069431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069518 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_5069518 : Nat := 118140960795 + 5069518 * 2 ^ 59
def prefixEnd_5069518 : Nat := 4983230072969 + 3 ^ 40 * 5069518 * 2
def baseEnd_5069518 : Nat := 2603099420619801721210717

theorem tailTrace_5069518 : CollatzResearch.WordTrace tailWord_5069518 prefixEnd_5069518 2603099420619801721210717 := by
  unfold tailWord_5069518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112563956001195698659151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123267007765339710392848805 23112563956001195698659151)
  ·
    refine ⟨34668845934001793547988727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23112563956001195698659151 34668845934001793547988727)
    ·
      refine ⟨52003268901002690321983091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34668845934001793547988727 52003268901002690321983091)
      ·
        refine ⟨78004903351504035482974637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52003268901002690321983091 78004903351504035482974637)
        ·
          refine ⟨29251838756814013306115489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78004903351504035482974637 29251838756814013306115489)
          ·
            refine ⟨21938879067610509979586617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29251838756814013306115489 21938879067610509979586617)
            ·
              refine ⟨16454159300707882484689963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21938879067610509979586617 16454159300707882484689963)
              ·
                refine ⟨24681238951061823727034945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16454159300707882484689963 24681238951061823727034945)
                ·
                  refine ⟨18510929213296367795276209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24681238951061823727034945 18510929213296367795276209)
                  ·
                    refine ⟨13883196909972275846457157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18510929213296367795276209 13883196909972275846457157)
                    ·
                      refine ⟨2603099420619801721210717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13883196909972275846457157 2603099420619801721210717)
                      ·
                        rfl

theorem cell23_5069518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_5069518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069518 prefixEnd_5069518 := by exact prefixLift 5069518
  have htrace : WordTrace (prefixWord ++ tailWord_5069518) baseStart_5069518 baseEnd_5069518 := by
    simpa [prefixWord, tailWord_5069518, baseEnd_5069518] using wordTrace_append hprefix tailTrace_5069518
  have hstable : (prefixWord ++ tailWord_5069518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069518).length < 2 ^ (prefixWord ++ tailWord_5069518).sum := by decide
  have hdescent : baseEnd_5069518 < baseStart_5069518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069548 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_5069548 : Nat := 118140960795 + 5069548 * 2 ^ 59
def prefixEnd_5069548 : Nat := 4983230072969 + 3 ^ 40 * 5069548 * 2
def baseEnd_5069548 : Nat := 2603114825039436603835579

theorem tailTrace_5069548 : CollatzResearch.WordTrace tailWord_5069548 prefixEnd_5069548 2603114825039436603835579 := by
  unfold tailWord_5069548
  simp only [CollatzResearch.WordTrace]
  refine ⟨92450802918950440356432649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123267737225267253808576865 92450802918950440356432649)
  ·
    refine ⟨69338102189212830267324487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92450802918950440356432649 69338102189212830267324487)
    ·
      refine ⟨104007153283819245400986731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69338102189212830267324487 104007153283819245400986731)
      ·
        refine ⟨156010729925728868101480097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104007153283819245400986731 156010729925728868101480097)
        ·
          refine ⟨117008047444296651076110073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156010729925728868101480097 117008047444296651076110073)
          ·
            refine ⟨87756035583222488307082555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117008047444296651076110073 87756035583222488307082555)
            ·
              refine ⟨131634053374833732460623833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87756035583222488307082555 131634053374833732460623833)
              ·
                refine ⟨98725540031125299345467875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131634053374833732460623833 98725540031125299345467875)
                ·
                  refine ⟨148088310046687949018201813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98725540031125299345467875 148088310046687949018201813)
                  ·
                    refine ⟨3470819766719248805114105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148088310046687949018201813 3470819766719248805114105)
                    ·
                      refine ⟨2603114825039436603835579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470819766719248805114105 2603114825039436603835579)
                      ·
                        rfl

theorem cell23_5069548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_5069548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069548 prefixEnd_5069548 := by exact prefixLift 5069548
  have htrace : WordTrace (prefixWord ++ tailWord_5069548) baseStart_5069548 baseEnd_5069548 := by
    simpa [prefixWord, tailWord_5069548, baseEnd_5069548] using wordTrace_append hprefix tailTrace_5069548
  have hstable : (prefixWord ++ tailWord_5069548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069548).length < 2 ^ (prefixWord ++ tailWord_5069548).sum := by decide
  have hdescent : baseEnd_5069548 < baseStart_5069548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069578 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5069578 : Nat := 118140960795 + 5069578 * 2 ^ 59
def prefixEnd_5069578 : Nat := 4983230072969 + 3 ^ 40 * 5069578 * 2
def baseEnd_5069578 : Nat := 2603130229459071486460441

theorem tailTrace_5069578 : CollatzResearch.WordTrace tailWord_5069578 prefixEnd_5069578 2603130229459071486460441 := by
  unfold tailWord_5069578
  simp only [CollatzResearch.WordTrace]
  refine ⟨46225675006948048959114347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123268466685194797224304925 46225675006948048959114347)
  ·
    refine ⟨69338512510422073438671521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46225675006948048959114347 69338512510422073438671521)
    ·
      refine ⟨52003884382816555079003641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69338512510422073438671521 52003884382816555079003641)
      ·
        refine ⟨39002913287112416309252731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52003884382816555079003641 39002913287112416309252731)
        ·
          refine ⟨58504369930668624463879097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39002913287112416309252731 58504369930668624463879097)
          ·
            refine ⟨43878277448001468347909323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58504369930668624463879097 43878277448001468347909323)
            ·
              refine ⟨65817416172002202521863985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43878277448001468347909323 65817416172002202521863985)
              ·
                refine ⟨49363062129001651891397989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65817416172002202521863985 49363062129001651891397989)
                ·
                  refine ⟨9255574149187809729637123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49363062129001651891397989 9255574149187809729637123)
                  ·
                    refine ⟨13883361223781714594455685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9255574149187809729637123 13883361223781714594455685)
                    ·
                      refine ⟨2603130229459071486460441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13883361223781714594455685 2603130229459071486460441)
                      ·
                        rfl

theorem cell23_5069578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5069578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069578 prefixEnd_5069578 := by exact prefixLift 5069578
  have htrace : WordTrace (prefixWord ++ tailWord_5069578) baseStart_5069578 baseEnd_5069578 := by
    simpa [prefixWord, tailWord_5069578, baseEnd_5069578] using wordTrace_append hprefix tailTrace_5069578
  have hstable : (prefixWord ++ tailWord_5069578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069578).length < 2 ^ (prefixWord ++ tailWord_5069578).sum := by decide
  have hdescent : baseEnd_5069578 < baseStart_5069578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069608 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5069608 : Nat := 118140960795 + 5069608 * 2 ^ 59
def prefixEnd_5069608 : Nat := 4983230072969 + 3 ^ 40 * 5069608 * 2
def baseEnd_5069608 : Nat := 2603145633878706369085303

theorem tailTrace_5069608 : CollatzResearch.WordTrace tailWord_5069608 prefixEnd_5069608 2603145633878706369085303 := by
  unfold tailWord_5069608
  simp only [CollatzResearch.WordTrace]
  refine ⟨92451897108841755480024739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123269196145122340640032985 92451897108841755480024739)
  ·
    refine ⟨138677845663262633220037109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92451897108841755480024739 138677845663262633220037109)
    ·
      refine ⟨13001048030930871864378479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138677845663262633220037109 13001048030930871864378479)
      ·
        refine ⟨19501572046396307796567719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13001048030930871864378479 19501572046396307796567719)
        ·
          refine ⟨29252358069594461694851579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19501572046396307796567719 29252358069594461694851579)
          ·
            refine ⟨43878537104391692542277369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29252358069594461694851579 43878537104391692542277369)
            ·
              refine ⟨32908902828293769406708027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43878537104391692542277369 32908902828293769406708027)
              ·
                refine ⟨49363354242440654110062041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32908902828293769406708027 49363354242440654110062041)
                ·
                  refine ⟨37022515681830490582546531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49363354242440654110062041 37022515681830490582546531)
                  ·
                    refine ⟨55533773522745735873819797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37022515681830490582546531 55533773522745735873819797)
                    ·
                      refine ⟨2603145633878706369085303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55533773522745735873819797 2603145633878706369085303)
                      ·
                        rfl

theorem cell23_5069608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5069608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069608 prefixEnd_5069608 := by exact prefixLift 5069608
  have htrace : WordTrace (prefixWord ++ tailWord_5069608) baseStart_5069608 baseEnd_5069608 := by
    simpa [prefixWord, tailWord_5069608, baseEnd_5069608] using wordTrace_append hprefix tailTrace_5069608
  have hstable : (prefixWord ++ tailWord_5069608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069608).length < 2 ^ (prefixWord ++ tailWord_5069608).sum := by decide
  have hdescent : baseEnd_5069608 < baseStart_5069608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069613 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 5]
def baseStart_5069613 : Nat := 118140960795 + 5069613 * 2 ^ 59
def prefixEnd_5069613 : Nat := 4983230072969 + 3 ^ 40 * 5069613 * 2
def baseEnd_5069613 : Nat := 289238689031330983280309

theorem tailTrace_5069613 : CollatzResearch.WordTrace tailWord_5069613 prefixEnd_5069613 289238689031330983280309 := by
  unfold tailWord_5069613
  simp only [CollatzResearch.WordTrace]
  refine ⟨184903976582665396813981493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123269317721776931209320995 184903976582665396813981493)
  ·
    refine ⟨17334747804624880951310765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 184903976582665396813981493 17334747804624880951310765)
    ·
      refine ⟨6500530426734330356741537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17334747804624880951310765 6500530426734330356741537)
      ·
        refine ⟨4875397820050747767556153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6500530426734330356741537 4875397820050747767556153)
        ·
          refine ⟨3656548365038060825667115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4875397820050747767556153 3656548365038060825667115)
          ·
            refine ⟨5484822547557091238500673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656548365038060825667115 5484822547557091238500673)
            ·
              refine ⟨4113616910667818428875505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5484822547557091238500673 4113616910667818428875505)
              ·
                refine ⟨3085212683000863821656629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4113616910667818428875505 3085212683000863821656629)
                ·
                  refine ⟨289238689031330983280309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085212683000863821656629 289238689031330983280309)
                  ·
                    rfl

theorem cell23_5069613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_5069613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069613 prefixEnd_5069613 := by exact prefixLift 5069613
  have htrace : WordTrace (prefixWord ++ tailWord_5069613) baseStart_5069613 baseEnd_5069613 := by
    simpa [prefixWord, tailWord_5069613, baseEnd_5069613] using wordTrace_append hprefix tailTrace_5069613
  have hstable : (prefixWord ++ tailWord_5069613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069613).length < 2 ^ (prefixWord ++ tailWord_5069613).sum := by decide
  have hdescent : baseEnd_5069613 < baseStart_5069613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069628 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_5069628 : Nat := 118140960795 + 5069628 * 2 ^ 59
def prefixEnd_5069628 : Nat := 4983230072969 + 3 ^ 40 * 5069628 * 2
def baseEnd_5069628 : Nat := 2603155903491796290835211

theorem tailTrace_5069628 : CollatzResearch.WordTrace tailWord_5069628 prefixEnd_5069628 2603155903491796290835211 := by
  unfold tailWord_5069628
  simp only [CollatzResearch.WordTrace]
  refine ⟨92452261838805527187888769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123269682451740702917185025 92452261838805527187888769)
  ·
    refine ⟨69339196379104145390916577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92452261838805527187888769 69339196379104145390916577)
    ·
      refine ⟨52004397284328109043187433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69339196379104145390916577 52004397284328109043187433)
      ·
        refine ⟨39003297963246081782390575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52004397284328109043187433 39003297963246081782390575)
        ·
          refine ⟨58504946944869122673585863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39003297963246081782390575 58504946944869122673585863)
          ·
            refine ⟨87757420417303684010378795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58504946944869122673585863 87757420417303684010378795)
            ·
              refine ⟨131636130625955526015568193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87757420417303684010378795 131636130625955526015568193)
              ·
                refine ⟨98727097969466644511676145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131636130625955526015568193 98727097969466644511676145)
                ·
                  refine ⟨74045323477099983383757109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98727097969466644511676145 74045323477099983383757109)
                  ·
                    refine ⟨6941749075978123442227229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74045323477099983383757109 6941749075978123442227229)
                    ·
                      refine ⟨2603155903491796290835211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941749075978123442227229 2603155903491796290835211)
                      ·
                        rfl

theorem cell23_5069628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_5069628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069628 prefixEnd_5069628 := by exact prefixLift 5069628
  have htrace : WordTrace (prefixWord ++ tailWord_5069628) baseStart_5069628 baseEnd_5069628 := by
    simpa [prefixWord, tailWord_5069628, baseEnd_5069628] using wordTrace_append hprefix tailTrace_5069628
  have hstable : (prefixWord ++ tailWord_5069628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069628).length < 2 ^ (prefixWord ++ tailWord_5069628).sum := by decide
  have hdescent : baseEnd_5069628 < baseStart_5069628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069648 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_5069648 : Nat := 118140960795 + 5069648 * 2 ^ 59
def prefixEnd_5069648 : Nat := 4983230072969 + 3 ^ 40 * 5069648 * 2
def baseEnd_5069648 : Nat := 867722057701628737528373

theorem tailTrace_5069648 : CollatzResearch.WordTrace tailWord_5069648 prefixEnd_5069648 867722057701628737528373 := by
  unfold tailWord_5069648
  simp only [CollatzResearch.WordTrace]
  refine ⟨92452626568769298895752799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123270168758359065194337065 92452626568769298895752799)
  ·
    refine ⟨138678939853153948343629199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92452626568769298895752799 138678939853153948343629199)
    ·
      refine ⟨208018409779730922515443799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138678939853153948343629199 208018409779730922515443799)
      ·
        refine ⟨312027614669596383773165699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208018409779730922515443799 312027614669596383773165699)
        ·
          refine ⟨468041422004394575659748549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312027614669596383773165699 468041422004394575659748549)
          ·
            refine ⟨87757766625823982936202853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468041422004394575659748549 87757766625823982936202853)
            ·
              refine ⟨16454581242341996800538035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87757766625823982936202853 16454581242341996800538035)
              ·
                refine ⟨24681871863512995200807053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16454581242341996800538035 24681871863512995200807053)
                ·
                  refine ⟨9255701948817373200302645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24681871863512995200807053 9255701948817373200302645)
                  ·
                    refine ⟨867722057701628737528373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9255701948817373200302645 867722057701628737528373)
                    ·
                      rfl

theorem cell23_5069648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_5069648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069648 prefixEnd_5069648 := by exact prefixLift 5069648
  have htrace : WordTrace (prefixWord ++ tailWord_5069648) baseStart_5069648 baseEnd_5069648 := by
    simpa [prefixWord, tailWord_5069648, baseEnd_5069648] using wordTrace_append hprefix tailTrace_5069648
  have hstable : (prefixWord ++ tailWord_5069648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069648).length < 2 ^ (prefixWord ++ tailWord_5069648).sum := by decide
  have hdescent : baseEnd_5069648 < baseStart_5069648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069649 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_5069649 : Nat := 118140960795 + 5069649 * 2 ^ 59
def prefixEnd_5069649 : Nat := 4983230072969 + 3 ^ 40 * 5069649 * 2
def baseEnd_5069649 : Nat := 2603166686585540708672615

theorem tailTrace_5069649 : CollatzResearch.WordTrace tailWord_5069649 prefixEnd_5069649 2603166686585540708672615 := by
  unfold tailWord_5069649
  simp only [CollatzResearch.WordTrace]
  refine ⟨184905289610534974962292001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123270193073689983308194667 184905289610534974962292001)
  ·
    refine ⟨138678967207901231221719001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184905289610534974962292001 138678967207901231221719001)
    ·
      refine ⟨104009225405925923416289251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138678967207901231221719001 104009225405925923416289251)
      ·
        refine ⟨156013838108888885124433877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104009225405925923416289251 156013838108888885124433877)
        ·
          refine ⟨3656574330677083245103919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156013838108888885124433877 3656574330677083245103919)
          ·
            refine ⟨5484861496015624867655879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656574330677083245103919 5484861496015624867655879)
            ·
              refine ⟨8227292244023437301483819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484861496015624867655879 8227292244023437301483819)
              ·
                refine ⟨12340938366035155952225729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227292244023437301483819 12340938366035155952225729)
                ·
                  refine ⟨9255703774526366964169297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12340938366035155952225729 9255703774526366964169297)
                  ·
                    refine ⟨6941777830894775223126973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9255703774526366964169297 6941777830894775223126973)
                    ·
                      refine ⟨2603166686585540708672615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941777830894775223126973 2603166686585540708672615)
                      ·
                        rfl

theorem cell23_5069649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_5069649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069649 prefixEnd_5069649 := by exact prefixLift 5069649
  have htrace : WordTrace (prefixWord ++ tailWord_5069649) baseStart_5069649 baseEnd_5069649 := by
    simpa [prefixWord, tailWord_5069649, baseEnd_5069649] using wordTrace_append hprefix tailTrace_5069649
  have hstable : (prefixWord ++ tailWord_5069649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069649).length < 2 ^ (prefixWord ++ tailWord_5069649).sum := by decide
  have hdescent : baseEnd_5069649 < baseStart_5069649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069688 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_5069688 : Nat := 118140960795 + 5069688 * 2 ^ 59
def prefixEnd_5069688 : Nat := 4983230072969 + 3 ^ 40 * 5069688 * 2
def baseEnd_5069688 : Nat := 2603186712331066056084935

theorem tailTrace_5069688 : CollatzResearch.WordTrace tailWord_5069688 prefixEnd_5069688 2603186712331066056084935 := by
  unfold tailWord_5069688
  simp only [CollatzResearch.WordTrace]
  refine ⟨92453356028696842311480859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123271141371595789748641145 92453356028696842311480859)
  ·
    refine ⟨138680034043045263467221289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92453356028696842311480859 138680034043045263467221289)
    ·
      refine ⟨104010025532283947600415967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138680034043045263467221289 104010025532283947600415967)
      ·
        refine ⟨156015038298425921400623951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104010025532283947600415967 156015038298425921400623951)
        ·
          refine ⟨234022557447638882100935927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156015038298425921400623951 234022557447638882100935927)
          ·
            refine ⟨351033836171458323151403891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234022557447638882100935927 351033836171458323151403891)
            ·
              refine ⟨526550754257187484727105837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351033836171458323151403891 526550754257187484727105837)
              ·
                refine ⟨197456532846445306772664689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526550754257187484727105837 197456532846445306772664689)
                ·
                  refine ⟨148092399634833980079498517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197456532846445306772664689 148092399634833980079498517)
                  ·
                    refine ⟨6941831232882842816226493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148092399634833980079498517 6941831232882842816226493)
                    ·
                      refine ⟨2603186712331066056084935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941831232882842816226493 2603186712331066056084935)
                      ·
                        rfl

theorem cell23_5069688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_5069688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069688 prefixEnd_5069688 := by exact prefixLift 5069688
  have htrace : WordTrace (prefixWord ++ tailWord_5069688) baseStart_5069688 baseEnd_5069688 := by
    simpa [prefixWord, tailWord_5069688, baseEnd_5069688] using wordTrace_append hprefix tailTrace_5069688
  have hstable : (prefixWord ++ tailWord_5069688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069688).length < 2 ^ (prefixWord ++ tailWord_5069688).sum := by decide
  have hdescent : baseEnd_5069688 < baseStart_5069688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069695 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 2, 4]
def baseStart_5069695 : Nat := 118140960795 + 5069695 * 2 ^ 59
def prefixEnd_5069695 : Nat := 4983230072969 + 3 ^ 40 * 5069695 * 2
def baseEnd_5069695 : Nat := 867730102231882509565801

theorem tailTrace_5069695 : CollatzResearch.WordTrace tailWord_5069695 prefixEnd_5069695 867730102231882509565801 := by
  unfold tailWord_5069695
  simp only [CollatzResearch.WordTrace]
  refine ⟨184906967368368324818466539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123271311578912216545644359 184906967368368324818466539)
  ·
    refine ⟨277360451052552487227699809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184906967368368324818466539 277360451052552487227699809)
    ·
      refine ⟨208020338289414365420774857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277360451052552487227699809 208020338289414365420774857)
      ·
        refine ⟨156015253717060774065581143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208020338289414365420774857 156015253717060774065581143)
        ·
          refine ⟨234022880575591161098371715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156015253717060774065581143 234022880575591161098371715)
          ·
            refine ⟨351034320863386741647557573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234022880575591161098371715 351034320863386741647557573)
            ·
              refine ⟨65818935161885014058917045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351034320863386741647557573 65818935161885014058917045)
              ·
                refine ⟨6170525171426720068023473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65818935161885014058917045 6170525171426720068023473)
                ·
                  refine ⟨4627893878570040051017605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6170525171426720068023473 4627893878570040051017605)
                  ·
                    refine ⟨867730102231882509565801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627893878570040051017605 867730102231882509565801)
                    ·
                      rfl

theorem cell23_5069695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_5069695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069695 prefixEnd_5069695 := by exact prefixLift 5069695
  have htrace : WordTrace (prefixWord ++ tailWord_5069695) baseStart_5069695 baseEnd_5069695 := by
    simpa [prefixWord, tailWord_5069695, baseEnd_5069695] using wordTrace_append hprefix tailTrace_5069695
  have hstable : (prefixWord ++ tailWord_5069695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069695).length < 2 ^ (prefixWord ++ tailWord_5069695).sum := by decide
  have hdescent : baseEnd_5069695 < baseStart_5069695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069722 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5069722 : Nat := 118140960795 + 5069722 * 2 ^ 59
def prefixEnd_5069722 : Nat := 4983230072969 + 3 ^ 40 * 5069722 * 2
def baseEnd_5069722 : Nat := 2603204170673318923059779

theorem tailTrace_5069722 : CollatzResearch.WordTrace tailWord_5069722 prefixEnd_5069722 2603204170673318923059779 := by
  unfold tailWord_5069722
  simp only [CollatzResearch.WordTrace]
  refine ⟨46226988034817627107424855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123271968092847005619799613 46226988034817627107424855)
  ·
    refine ⟨69340482052226440661137283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46226988034817627107424855 69340482052226440661137283)
    ·
      refine ⟨104010723078339660991705925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69340482052226440661137283 104010723078339660991705925)
      ·
        refine ⟨19502010577188686435944861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104010723078339660991705925 19502010577188686435944861)
        ·
          refine ⟨7313253966445757413479323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19502010577188686435944861 7313253966445757413479323)
          ·
            refine ⟨10969880949668636120218985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7313253966445757413479323 10969880949668636120218985)
            ·
              refine ⟨8227410712251477090164239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10969880949668636120218985 8227410712251477090164239)
              ·
                refine ⟨12341116068377215635246359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227410712251477090164239 12341116068377215635246359)
                ·
                  refine ⟨18511674102565823452869539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12341116068377215635246359 18511674102565823452869539)
                  ·
                    refine ⟨27767511153848735179304309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18511674102565823452869539 27767511153848735179304309)
                    ·
                      refine ⟨2603204170673318923059779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27767511153848735179304309 2603204170673318923059779)
                      ·
                        rfl

theorem cell23_5069722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5069722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069722 prefixEnd_5069722 := by exact prefixLift 5069722
  have htrace : WordTrace (prefixWord ++ tailWord_5069722) baseStart_5069722 baseEnd_5069722 := by
    simpa [prefixWord, tailWord_5069722, baseEnd_5069722] using wordTrace_append hprefix tailTrace_5069722
  have hstable : (prefixWord ++ tailWord_5069722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069722).length < 2 ^ (prefixWord ++ tailWord_5069722).sum := by decide
  have hdescent : baseEnd_5069722 < baseStart_5069722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069750 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5069750 : Nat := 118140960795 + 5069750 * 2 ^ 59
def prefixEnd_5069750 : Nat := 4983230072969 + 3 ^ 40 * 5069750 * 2
def baseEnd_5069750 : Nat := 867739516043881604503217

theorem tailTrace_5069750 : CollatzResearch.WordTrace tailWord_5069750 prefixEnd_5069750 867739516043881604503217 := by
  unfold tailWord_5069750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556810836448066825732419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123272648922112712807812469 11556810836448066825732419)
  ·
    refine ⟨17335216254672100238598629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11556810836448066825732419 17335216254672100238598629)
    ·
      refine ⟨3250353047751018794737243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17335216254672100238598629 3250353047751018794737243)
      ·
        refine ⟨4875529571626528192105865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250353047751018794737243 4875529571626528192105865)
        ·
          refine ⟨3656647178719896144079399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4875529571626528192105865 3656647178719896144079399)
          ·
            refine ⟨5484970768079844216119099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656647178719896144079399 5484970768079844216119099)
            ·
              refine ⟨8227456152119766324178649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484970768079844216119099 8227456152119766324178649)
              ·
                refine ⟨6170592114089824743133987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8227456152119766324178649 6170592114089824743133987)
                ·
                  refine ⟨9255888171134737114700981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6170592114089824743133987 9255888171134737114700981)
                  ·
                    refine ⟨867739516043881604503217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9255888171134737114700981 867739516043881604503217)
                    ·
                      rfl

theorem cell23_5069750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5069750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069750 prefixEnd_5069750 := by exact prefixLift 5069750
  have htrace : WordTrace (prefixWord ++ tailWord_5069750) baseStart_5069750 baseEnd_5069750 := by
    simpa [prefixWord, tailWord_5069750, baseEnd_5069750] using wordTrace_append hprefix tailTrace_5069750
  have hstable : (prefixWord ++ tailWord_5069750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069750).length < 2 ^ (prefixWord ++ tailWord_5069750).sum := by decide
  have hdescent : baseEnd_5069750 < baseStart_5069750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069773 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5069773 : Nat := 118140960795 + 5069773 * 2 ^ 59
def prefixEnd_5069773 : Nat := 4983230072969 + 3 ^ 40 * 5069773 * 2
def baseEnd_5069773 : Nat := 2603230358186698223522045

theorem tailTrace_5069773 : CollatzResearch.WordTrace tailWord_5069773 prefixEnd_5069773 2603230358186698223522045 := by
  unfold tailWord_5069773
  simp only [CollatzResearch.WordTrace]
  refine ⟨184909812262085744139805973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123273208174723829426537315 184909812262085744139805973)
  ·
    refine ⟨8667647449785269256553405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 184909812262085744139805973 8667647449785269256553405)
    ·
      refine ⟨3250367793669475971207527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8667647449785269256553405 3250367793669475971207527)
      ·
        refine ⟨4875551690504213956811291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250367793669475971207527 4875551690504213956811291)
        ·
          refine ⟨7313327535756320935216937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875551690504213956811291 7313327535756320935216937)
          ·
            refine ⟨5484995651817240701412703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7313327535756320935216937 5484995651817240701412703)
            ·
              refine ⟨8227493477725861052119055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484995651817240701412703 8227493477725861052119055)
              ·
                refine ⟨12341240216588791578178583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227493477725861052119055 12341240216588791578178583)
                ·
                  refine ⟨18511860324883187367267875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12341240216588791578178583 18511860324883187367267875)
                  ·
                    refine ⟨27767790487324781050901813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18511860324883187367267875 27767790487324781050901813)
                    ·
                      refine ⟨2603230358186698223522045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27767790487324781050901813 2603230358186698223522045)
                      ·
                        rfl

theorem cell23_5069773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5069773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069773 prefixEnd_5069773 := by exact prefixLift 5069773
  have htrace : WordTrace (prefixWord ++ tailWord_5069773) baseStart_5069773 baseEnd_5069773 := by
    simpa [prefixWord, tailWord_5069773, baseEnd_5069773] using wordTrace_append hprefix tailTrace_5069773
  have hstable : (prefixWord ++ tailWord_5069773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069773).length < 2 ^ (prefixWord ++ tailWord_5069773).sum := by decide
  have hdescent : baseEnd_5069773 < baseStart_5069773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069795 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3]
def baseStart_5069795 : Nat := 118140960795 + 5069795 * 2 ^ 59
def prefixEnd_5069795 : Nat := 4983230072969 + 3 ^ 40 * 5069795 * 2
def baseEnd_5069795 : Nat := 2603241654761097137446943

theorem tailTrace_5069795 : CollatzResearch.WordTrace tailWord_5069795 prefixEnd_5069795 2603241654761097137446943 := by
  unfold tailWord_5069795
  simp only [CollatzResearch.WordTrace]
  refine ⟨184910614668006041897106839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123273743112004027931404559 184910614668006041897106839)
  ·
    refine ⟨277365922002009062845660259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184910614668006041897106839 277365922002009062845660259)
    ·
      refine ⟨416048883003013594268490389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277365922002009062845660259 416048883003013594268490389)
      ·
        refine ⟨19502291390766262231335487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 416048883003013594268490389 19502291390766262231335487)
        ·
          refine ⟨29253437086149393347003231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19502291390766262231335487 29253437086149393347003231)
          ·
            refine ⟨43880155629224090020504847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29253437086149393347003231 43880155629224090020504847)
            ·
              refine ⟨65820233443836135030757271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43880155629224090020504847 65820233443836135030757271)
              ·
                refine ⟨98730350165754202546135907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65820233443836135030757271 98730350165754202546135907)
                ·
                  refine ⟨148095525248631303819203861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98730350165754202546135907 148095525248631303819203861)
                  ·
                    refine ⟨6941977746029592366525181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148095525248631303819203861 6941977746029592366525181)
                    ·
                      refine ⟨2603241654761097137446943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6941977746029592366525181 2603241654761097137446943)
                      ·
                        rfl

theorem cell23_5069795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_5069795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069795 prefixEnd_5069795 := by exact prefixLift 5069795
  have htrace : WordTrace (prefixWord ++ tailWord_5069795) baseStart_5069795 baseEnd_5069795 := by
    simpa [prefixWord, tailWord_5069795, baseEnd_5069795] using wordTrace_append hprefix tailTrace_5069795
  have hstable : (prefixWord ++ tailWord_5069795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069795).length < 2 ^ (prefixWord ++ tailWord_5069795).sum := by decide
  have hdescent : baseEnd_5069795 < baseStart_5069795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069809 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_5069809 : Nat := 118140960795 + 5069809 * 2 ^ 59
def prefixEnd_5069809 : Nat := 4983230072969 + 3 ^ 40 * 5069809 * 2
def baseEnd_5069809 : Nat := 2603248843490260082671879

theorem tailTrace_5069809 : CollatzResearch.WordTrace tailWord_5069809 prefixEnd_5069809 2603248843490260082671879 := by
  unfold tailWord_5069809
  simp only [CollatzResearch.WordTrace]
  refine ⟨184911125289955322288116481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123274083526636881525410987 184911125289955322288116481)
  ·
    refine ⟨138683343967466491716087361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184911125289955322288116481 138683343967466491716087361)
    ·
      refine ⟨104012507975599868787065521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138683343967466491716087361 104012507975599868787065521)
      ·
        refine ⟨78009380981699901590299141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104012507975599868787065521 78009380981699901590299141)
        ·
          refine ⟨14626758934068731548181089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78009380981699901590299141 14626758934068731548181089)
          ·
            refine ⟨10970069200551548661135817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14626758934068731548181089 10970069200551548661135817)
            ·
              refine ⟨8227551900413661495851863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10970069200551548661135817 8227551900413661495851863)
              ·
                refine ⟨12341327850620492243777795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227551900413661495851863 12341327850620492243777795)
                ·
                  refine ⟨18511991775930738365666693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12341327850620492243777795 18511991775930738365666693)
                  ·
                    refine ⟨3470998457987013443562505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18511991775930738365666693 3470998457987013443562505)
                    ·
                      refine ⟨2603248843490260082671879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3470998457987013443562505 2603248843490260082671879)
                      ·
                        rfl

theorem cell23_5069809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_5069809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069809 prefixEnd_5069809 := by exact prefixLift 5069809
  have htrace : WordTrace (prefixWord ++ tailWord_5069809) baseStart_5069809 baseEnd_5069809 := by
    simpa [prefixWord, tailWord_5069809, baseEnd_5069809] using wordTrace_append hprefix tailTrace_5069809
  have hstable : (prefixWord ++ tailWord_5069809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069809).length < 2 ^ (prefixWord ++ tailWord_5069809).sum := by decide
  have hdescent : baseEnd_5069809 < baseStart_5069809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069832 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 5]
def baseStart_5069832 : Nat := 118140960795 + 5069832 * 2 ^ 59
def prefixEnd_5069832 : Nat := 4983230072969 + 3 ^ 40 * 5069832 * 2
def baseEnd_5069832 : Nat := 289251183727257054742697

theorem tailTrace_5069832 : CollatzResearch.WordTrace tailWord_5069832 prefixEnd_5069832 289251183727257054742697 := by
  unfold tailWord_5069832
  simp only [CollatzResearch.WordTrace]
  refine ⟨92455982084435998608101875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123274642779247998144135833 92455982084435998608101875)
  ·
    refine ⟨138683973126653997912152813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92455982084435998608101875 138683973126653997912152813)
    ·
      refine ⟨52006489922495249217057305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138683973126653997912152813 52006489922495249217057305)
      ·
        refine ⟨39004867441871436912792979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52006489922495249217057305 39004867441871436912792979)
        ·
          refine ⟨58507301162807155369189469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39004867441871436912792979 58507301162807155369189469)
          ·
            refine ⟨21940237936052683263446051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58507301162807155369189469 21940237936052683263446051)
            ·
              refine ⟨32910356904079024895169077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21940237936052683263446051 32910356904079024895169077)
              ·
                refine ⟨3085345959757408583922101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32910356904079024895169077 3085345959757408583922101)
                ·
                  refine ⟨289251183727257054742697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085345959757408583922101 289251183727257054742697)
                  ·
                    rfl

theorem cell23_5069832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 5].length) (baseStart_5069832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069832 prefixEnd_5069832 := by exact prefixLift 5069832
  have htrace : WordTrace (prefixWord ++ tailWord_5069832) baseStart_5069832 baseEnd_5069832 := by
    simpa [prefixWord, tailWord_5069832, baseEnd_5069832] using wordTrace_append hprefix tailTrace_5069832
  have hstable : (prefixWord ++ tailWord_5069832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069832).length < 2 ^ (prefixWord ++ tailWord_5069832).sum := by decide
  have hdescent : baseEnd_5069832 < baseStart_5069832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069882 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_5069882 : Nat := 118140960795 + 5069882 * 2 ^ 59
def prefixEnd_5069882 : Nat := 4983230072969 + 3 ^ 40 * 5069882 * 2
def baseEnd_5069882 : Nat := 2603286327578038297059043

theorem tailTrace_5069882 : CollatzResearch.WordTrace tailWord_5069882 prefixEnd_5069882 2603286327578038297059043 := by
  unfold tailWord_5069882
  simp only [CollatzResearch.WordTrace]
  refine ⟨46228446954672713938880975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123275858545793903837015933 46228446954672713938880975)
  ·
    refine ⟨69342670432009070908321463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46228446954672713938880975 69342670432009070908321463)
    ·
      refine ⟨104014005648013606362482195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69342670432009070908321463 104014005648013606362482195)
      ·
        refine ⟨156021008472020409543723293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104014005648013606362482195 156021008472020409543723293)
        ·
          refine ⟨58507878177007653578896235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156021008472020409543723293 58507878177007653578896235)
          ·
            refine ⟨87761817265511480368344353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58507878177007653578896235 87761817265511480368344353)
            ·
              refine ⟨65821362949133610276258265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87761817265511480368344353 65821362949133610276258265)
              ·
                refine ⟨49366022211850207707193699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65821362949133610276258265 49366022211850207707193699)
                ·
                  refine ⟨74049033317775311560790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49366022211850207707193699 74049033317775311560790549)
                  ·
                    refine ⟨3471048436770717729412057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74049033317775311560790549 3471048436770717729412057)
                    ·
                      refine ⟨2603286327578038297059043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471048436770717729412057 2603286327578038297059043)
                      ·
                        rfl

theorem cell23_5069882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_5069882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069882 prefixEnd_5069882 := by exact prefixLift 5069882
  have htrace : WordTrace (prefixWord ++ tailWord_5069882) baseStart_5069882 baseEnd_5069882 := by
    simpa [prefixWord, tailWord_5069882, baseEnd_5069882] using wordTrace_append hprefix tailTrace_5069882
  have hstable : (prefixWord ++ tailWord_5069882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069882).length < 2 ^ (prefixWord ++ tailWord_5069882).sum := by decide
  have hdescent : baseEnd_5069882 < baseStart_5069882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069905 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 8]
def baseStart_5069905 : Nat := 118140960795 + 5069905 * 2 ^ 59
def prefixEnd_5069905 : Nat := 4983230072969 + 3 ^ 40 * 5069905 * 2
def baseEnd_5069905 : Nat := 289255348625899078563493

theorem tailTrace_5069905 : CollatzResearch.WordTrace tailWord_5069905 prefixEnd_5069905 289255348625899078563493 := by
  unfold tailWord_5069905
  simp only [CollatzResearch.WordTrace]
  refine ⟨184914626697607530683611169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123276417798405020455740779 184914626697607530683611169)
  ·
    refine ⟨138685970023205648012708377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184914626697607530683611169 138685970023205648012708377)
    ·
      refine ⟨104014477517404236009531283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138685970023205648012708377 104014477517404236009531283)
      ·
        refine ⟨156021716276106354014296925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104014477517404236009531283 156021716276106354014296925)
        ·
          refine ⟨58508143603539882755361347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156021716276106354014296925 58508143603539882755361347)
          ·
            refine ⟨87762215405309824133042021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58508143603539882755361347 87762215405309824133042021)
            ·
              refine ⟨16455415388495592024945379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87762215405309824133042021 16455415388495592024945379)
              ·
                refine ⟨24683123082743388037418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16455415388495592024945379 24683123082743388037418069)
                ·
                  refine ⟨289255348625899078563493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24683123082743388037418069 289255348625899078563493)
                  ·
                    rfl

theorem cell23_5069905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_5069905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069905 prefixEnd_5069905 := by exact prefixLift 5069905
  have htrace : WordTrace (prefixWord ++ tailWord_5069905) baseStart_5069905 baseEnd_5069905 := by
    simpa [prefixWord, tailWord_5069905, baseEnd_5069905] using wordTrace_append hprefix tailTrace_5069905
  have hstable : (prefixWord ++ tailWord_5069905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069905).length < 2 ^ (prefixWord ++ tailWord_5069905).sum := by decide
  have hdescent : baseEnd_5069905 < baseStart_5069905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069952 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_5069952 : Nat := 118140960795 + 5069952 * 2 ^ 59
def prefixEnd_5069952 : Nat := 4983230072969 + 3 ^ 40 * 5069952 * 2
def baseEnd_5069952 : Nat := 867774090407951007727907

theorem tailTrace_5069952 : CollatzResearch.WordTrace tailWord_5069952 prefixEnd_5069952 867774090407951007727907 := by
  unfold tailWord_5069952
  simp only [CollatzResearch.WordTrace]
  refine ⟨92458170464218628855286055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123277560618958171807048073 92458170464218628855286055)
  ·
    refine ⟨138687255696327943282929083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92458170464218628855286055 138687255696327943282929083)
    ·
      refine ⟨208030883544491914924393625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138687255696327943282929083 208030883544491914924393625)
      ·
        refine ⟨156023162658368936193295219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208030883544491914924393625 156023162658368936193295219)
        ·
          refine ⟨234034743987553404289942829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156023162658368936193295219 234034743987553404289942829)
          ·
            refine ⟨87763028995332526608728561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234034743987553404289942829 87763028995332526608728561)
            ·
              refine ⟨65822271746499394956546421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87763028995332526608728561 65822271746499394956546421)
              ·
                refine ⟨6170837976234318277176227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65822271746499394956546421 6170837976234318277176227)
                ·
                  refine ⟨9256256964351477415764341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6170837976234318277176227 9256256964351477415764341)
                  ·
                    refine ⟨867774090407951007727907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9256256964351477415764341 867774090407951007727907)
                    ·
                      rfl

theorem cell23_5069952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_5069952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069952 prefixEnd_5069952 := by exact prefixLift 5069952
  have htrace : WordTrace (prefixWord ++ tailWord_5069952) baseStart_5069952 baseEnd_5069952 := by
    simpa [prefixWord, tailWord_5069952, baseEnd_5069952] using wordTrace_append hprefix tailTrace_5069952
  have hstable : (prefixWord ++ tailWord_5069952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069952).length < 2 ^ (prefixWord ++ tailWord_5069952).sum := by decide
  have hdescent : baseEnd_5069952 < baseStart_5069952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5069960 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 1, 4]
def baseStart_5069960 : Nat := 118140960795 + 5069960 * 2 ^ 59
def prefixEnd_5069960 : Nat := 4983230072969 + 3 ^ 40 * 5069960 * 2
def baseEnd_5069960 : Nat := 867775459689696330627895

theorem tailTrace_5069960 : CollatzResearch.WordTrace tailWord_5069960 prefixEnd_5069960 867775459689696330627895 := by
  unfold tailWord_5069960
  simp only [CollatzResearch.WordTrace]
  refine ⟨92458316356204137538431667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123277755141605516717908889 92458316356204137538431667)
  ·
    refine ⟨138687474534306206307647501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92458316356204137538431667 138687474534306206307647501)
    ·
      refine ⟨52007802950364827365367813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138687474534306206307647501 52007802950364827365367813)
      ·
        refine ⟨9751463053193405131006465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52007802950364827365367813 9751463053193405131006465)
        ·
          refine ⟨7313597289895053848254849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9751463053193405131006465 7313597289895053848254849)
          ·
            refine ⟨5485197967421290386191137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7313597289895053848254849 5485197967421290386191137)
            ·
              refine ⟨4113898475565967789643353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485197967421290386191137 4113898475565967789643353)
              ·
                refine ⟨3085423856674475842232515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4113898475565967789643353 3085423856674475842232515)
                ·
                  refine ⟨4628135785011713763348773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085423856674475842232515 4628135785011713763348773)
                  ·
                    refine ⟨867775459689696330627895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628135785011713763348773 867775459689696330627895)
                    ·
                      rfl

theorem cell23_5069960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_5069960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5069960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5069960 prefixEnd_5069960 := by exact prefixLift 5069960
  have htrace : WordTrace (prefixWord ++ tailWord_5069960) baseStart_5069960 baseEnd_5069960 := by
    simpa [prefixWord, tailWord_5069960, baseEnd_5069960] using wordTrace_append hprefix tailTrace_5069960
  have hstable : (prefixWord ++ tailWord_5069960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5069960).length < 2 ^ (prefixWord ++ tailWord_5069960).sum := by decide
  have hdescent : baseEnd_5069960 < baseStart_5069960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5069960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070012 : List Nat := [2, 2, 2, 3, 2, 2, 10]
def baseStart_5070012 : Nat := 118140960795 + 5070012 * 2 ^ 59
def prefixEnd_5070012 : Nat := 4983230072969 + 3 ^ 40 * 5070012 * 2
def baseEnd_5070012 : Nat := 32140161482260775165845

theorem tailTrace_5070012 : CollatzResearch.WordTrace tailWord_5070012 prefixEnd_5070012 32140161482260775165845 := by
  unfold tailWord_5070012
  simp only [CollatzResearch.WordTrace]
  refine ⟨92459264654109943978878145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123279019538813258638504193 92459264654109943978878145)
  ·
    refine ⟨69344448490582457984158609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92459264654109943978878145 69344448490582457984158609)
    ·
      refine ⟨52008336367936843488118957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69344448490582457984158609 52008336367936843488118957)
      ·
        refine ⟨19503126137976316308044609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52008336367936843488118957 19503126137976316308044609)
        ·
          refine ⟨14627344603482237231033457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19503126137976316308044609 14627344603482237231033457)
          ·
            refine ⟨10970508452611677923275093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14627344603482237231033457 10970508452611677923275093)
            ·
              refine ⟨32140161482260775165845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10970508452611677923275093 32140161482260775165845)
              ·
                rfl

theorem cell23_5070012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 10].length) (baseStart_5070012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070012 prefixEnd_5070012 := by exact prefixLift 5070012
  have htrace : WordTrace (prefixWord ++ tailWord_5070012) baseStart_5070012 baseEnd_5070012 := by
    simpa [prefixWord, tailWord_5070012, baseEnd_5070012] using wordTrace_append hprefix tailTrace_5070012
  have hstable : (prefixWord ++ tailWord_5070012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070012).length < 2 ^ (prefixWord ++ tailWord_5070012).sum := by decide
  have hdescent : baseEnd_5070012 < baseStart_5070012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070036 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5070036 : Nat := 118140960795 + 5070036 * 2 ^ 59
def prefixEnd_5070036 : Nat := 4983230072969 + 3 ^ 40 * 5070036 * 2
def baseEnd_5070036 : Nat := 2603365403598830694533335

theorem tailTrace_5070036 : CollatzResearch.WordTrace tailWord_5070036 prefixEnd_5070036 2603365403598830694533335 := by
  unfold tailWord_5070036
  simp only [CollatzResearch.WordTrace]
  refine ⟨92459702330066470028314981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123279603106755293371086641 92459702330066470028314981)
  ·
    refine ⟨17336194186887463130309059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92459702330066470028314981 17336194186887463130309059)
    ·
      refine ⟨26004291280331194695463589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17336194186887463130309059 26004291280331194695463589)
      ·
        refine ⟨4875804615062099005399423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26004291280331194695463589 4875804615062099005399423)
        ·
          refine ⟨7313706922593148508099135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875804615062099005399423 7313706922593148508099135)
          ·
            refine ⟨10970560383889722762148703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7313706922593148508099135 10970560383889722762148703)
            ·
              refine ⟨16455840575834584143223055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10970560383889722762148703 16455840575834584143223055)
              ·
                refine ⟨24683760863751876214834583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16455840575834584143223055 24683760863751876214834583)
                ·
                  refine ⟨37025641295627814322251875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24683760863751876214834583 37025641295627814322251875)
                  ·
                    refine ⟨55538461943441721483377813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37025641295627814322251875 55538461943441721483377813)
                    ·
                      refine ⟨2603365403598830694533335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55538461943441721483377813 2603365403598830694533335)
                      ·
                        rfl

theorem cell23_5070036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5070036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070036 prefixEnd_5070036 := by exact prefixLift 5070036
  have htrace : WordTrace (prefixWord ++ tailWord_5070036) baseStart_5070036 baseEnd_5070036 := by
    simpa [prefixWord, tailWord_5070036, baseEnd_5070036] using wordTrace_append hprefix tailTrace_5070036
  have hstable : (prefixWord ++ tailWord_5070036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070036).length < 2 ^ (prefixWord ++ tailWord_5070036).sum := by decide
  have hdescent : baseEnd_5070036 < baseStart_5070036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070039 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_5070039 : Nat := 118140960795 + 5070039 * 2 ^ 59
def prefixEnd_5070039 : Nat := 4983230072969 + 3 ^ 40 * 5070039 * 2
def baseEnd_5070039 : Nat := 2603366944040794182795821

theorem tailTrace_5070039 : CollatzResearch.WordTrace tailWord_5070039 prefixEnd_5070039 2603366944040794182795821 := by
  unfold tailWord_5070039
  simp only [CollatzResearch.WordTrace]
  refine ⟨184919514079122071568989171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123279676052748047712659447 184919514079122071568989171)
  ·
    refine ⟨277379271118683107353483757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184919514079122071568989171 277379271118683107353483757)
    ·
      refine ⟨104017226669506165257556409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277379271118683107353483757 104017226669506165257556409)
      ·
        refine ⟨78012920002129623943167307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104017226669506165257556409 78012920002129623943167307)
        ·
          refine ⟨117019380003194435914750961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78012920002129623943167307 117019380003194435914750961)
          ·
            refine ⟨87764535002395826936063221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117019380003194435914750961 87764535002395826936063221)
            ·
              refine ⟨8227925156474608775255927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87764535002395826936063221 8227925156474608775255927)
              ·
                refine ⟨12341887734711913162883891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227925156474608775255927 12341887734711913162883891)
                ·
                  refine ⟨18512831602067869744325837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12341887734711913162883891 18512831602067869744325837)
                  ·
                    refine ⟨6942311850775451154122189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18512831602067869744325837 6942311850775451154122189)
                    ·
                      refine ⟨2603366944040794182795821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6942311850775451154122189 2603366944040794182795821)
                      ·
                        rfl

theorem cell23_5070039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_5070039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070039 prefixEnd_5070039 := by exact prefixLift 5070039
  have htrace : WordTrace (prefixWord ++ tailWord_5070039) baseStart_5070039 baseEnd_5070039 := by
    simpa [prefixWord, tailWord_5070039, baseEnd_5070039] using wordTrace_append hprefix tailTrace_5070039
  have hstable : (prefixWord ++ tailWord_5070039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070039).length < 2 ^ (prefixWord ++ tailWord_5070039).sum := by decide
  have hdescent : baseEnd_5070039 < baseStart_5070039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070052 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_5070052 : Nat := 118140960795 + 5070052 * 2 ^ 59
def prefixEnd_5070052 : Nat := 4983230072969 + 3 ^ 40 * 5070052 * 2
def baseEnd_5070052 : Nat := 2603373619289302631933261

theorem tailTrace_5070052 : CollatzResearch.WordTrace tailWord_5070052 prefixEnd_5070052 2603373619289302631933261 := by
  unfold tailWord_5070052
  simp only [CollatzResearch.WordTrace]
  refine ⟨92459994114037487394606205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123279992152049983192808273 92459994114037487394606205)
  ·
    refine ⟨34672497792764057772977327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92459994114037487394606205 34672497792764057772977327)
    ·
      refine ⟨52008746689146086659465991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34672497792764057772977327 52008746689146086659465991)
      ·
        refine ⟨78013120033719129989198987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52008746689146086659465991 78013120033719129989198987)
        ·
          refine ⟨117019680050578694983798481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78013120033719129989198987 117019680050578694983798481)
          ·
            refine ⟨87764760037934021237848861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117019680050578694983798481 87764760037934021237848861)
            ·
              refine ⟨32911785014225257964193323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87764760037934021237848861 32911785014225257964193323)
              ·
                refine ⟨49367677521337886946289985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32911785014225257964193323 49367677521337886946289985)
                ·
                  refine ⟨37025758141003415209717489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49367677521337886946289985 37025758141003415209717489)
                  ·
                    refine ⟨27769318605752561407288117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37025758141003415209717489 27769318605752561407288117)
                    ·
                      refine ⟨2603373619289302631933261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27769318605752561407288117 2603373619289302631933261)
                      ·
                        rfl

theorem cell23_5070052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_5070052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070052 prefixEnd_5070052 := by exact prefixLift 5070052
  have htrace : WordTrace (prefixWord ++ tailWord_5070052) baseStart_5070052 baseEnd_5070052 := by
    simpa [prefixWord, tailWord_5070052, baseEnd_5070052] using wordTrace_append hprefix tailTrace_5070052
  have hstable : (prefixWord ++ tailWord_5070052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070052).length < 2 ^ (prefixWord ++ tailWord_5070052).sum := by decide
  have hdescent : baseEnd_5070052 < baseStart_5070052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070130 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_5070130 : Nat := 118140960795 + 5070130 * 2 ^ 59
def prefixEnd_5070130 : Nat := 4983230072969 + 3 ^ 40 * 5070130 * 2
def baseEnd_5070130 : Nat := 2603413670780353326757903

theorem tailTrace_5070130 : CollatzResearch.WordTrace tailWord_5070130 prefixEnd_5070130 2603413670780353326757903 := by
  unfold tailWord_5070130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46230708280448098527637961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123281888747861596073701229 46230708280448098527637961)
  ·
    refine ⟨34673031210336073895728471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46230708280448098527637961 34673031210336073895728471)
    ·
      refine ⟨52009546815504110843592707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34673031210336073895728471 52009546815504110843592707)
      ·
        refine ⟨78014320223256166265389061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52009546815504110843592707 78014320223256166265389061)
        ·
          refine ⟨14627685041860531174760449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78014320223256166265389061 14627685041860531174760449)
          ·
            refine ⟨10970763781395398381070337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14627685041860531174760449 10970763781395398381070337)
            ·
              refine ⟨8228072836046548785802753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10970763781395398381070337 8228072836046548785802753)
              ·
                refine ⟨6171054627034911589352065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8228072836046548785802753 6171054627034911589352065)
                ·
                  refine ⟨4628290970276183692014049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171054627034911589352065 4628290970276183692014049)
                  ·
                    refine ⟨3471218227707137769010537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4628290970276183692014049 3471218227707137769010537)
                    ·
                      refine ⟨2603413670780353326757903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471218227707137769010537 2603413670780353326757903)
                      ·
                        rfl

theorem cell23_5070130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_5070130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070130 prefixEnd_5070130 := by exact prefixLift 5070130
  have htrace : WordTrace (prefixWord ++ tailWord_5070130) baseStart_5070130 baseEnd_5070130 := by
    simpa [prefixWord, tailWord_5070130, baseEnd_5070130] using wordTrace_append hprefix tailTrace_5070130
  have hstable : (prefixWord ++ tailWord_5070130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070130).length < 2 ^ (prefixWord ++ tailWord_5070130).sum := by decide
  have hdescent : baseEnd_5070130 < baseStart_5070130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070219 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3]
def baseStart_5070219 : Nat := 118140960795 + 5070219 * 2 ^ 59
def prefixEnd_5070219 : Nat := 4983230072969 + 3 ^ 40 * 5070219 * 2
def baseEnd_5070219 : Nat := 2603459370558603478544993

theorem tailTrace_5070219 : CollatzResearch.WordTrace tailWord_5070219 prefixEnd_5070219 2603459370558603478544993 := by
  unfold tailWord_5070219
  simp only [CollatzResearch.WordTrace]
  refine ⟨184926079218469962310541711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123284052812313308207027807 184926079218469962310541711)
  ·
    refine ⟨277389118827704943465812567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184926079218469962310541711 277389118827704943465812567)
    ·
      refine ⟨416083678241557415198718851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277389118827704943465812567 416083678241557415198718851)
      ·
        refine ⟨624125517362336122798078277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416083678241557415198718851 624125517362336122798078277)
        ·
          refine ⟨117023534505438023024639677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 624125517362336122798078277 117023534505438023024639677)
          ·
            refine ⟨43883825439539258634239879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117023534505438023024639677 43883825439539258634239879)
            ·
              refine ⟨65825738159308887951359819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43883825439539258634239879 65825738159308887951359819)
              ·
                refine ⟨98738607238963331927039729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65825738159308887951359819 98738607238963331927039729)
                ·
                  refine ⟨74053955429222498945279797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98738607238963331927039729 74053955429222498945279797)
                  ·
                    refine ⟨6942558321489609276119981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74053955429222498945279797 6942558321489609276119981)
                    ·
                      refine ⟨2603459370558603478544993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6942558321489609276119981 2603459370558603478544993)
                      ·
                        rfl

theorem cell23_5070219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3].length) (baseStart_5070219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070219 prefixEnd_5070219 := by exact prefixLift 5070219
  have htrace : WordTrace (prefixWord ++ tailWord_5070219) baseStart_5070219 baseEnd_5070219 := by
    simpa [prefixWord, tailWord_5070219, baseEnd_5070219] using wordTrace_append hprefix tailTrace_5070219
  have hstable : (prefixWord ++ tailWord_5070219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070219).length < 2 ^ (prefixWord ++ tailWord_5070219).sum := by decide
  have hdescent : baseEnd_5070219 < baseStart_5070219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070286 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_5070286 : Nat := 118140960795 + 5070286 * 2 ^ 59
def prefixEnd_5070286 : Nat := 4983230072969 + 3 ^ 40 * 5070286 * 2
def baseEnd_5070286 : Nat := 867831257920818238802395

theorem tailTrace_5070286 : CollatzResearch.WordTrace tailWord_5070286 prefixEnd_5070286 867831257920818238802395 := by
  unfold tailWord_5070286
  simp only [CollatzResearch.WordTrace]
  refine ⟨23116065363653404094153839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123285681939484821835487141 23116065363653404094153839)
  ·
    refine ⟨34674098045480106141230759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23116065363653404094153839 34674098045480106141230759)
    ·
      refine ⟨52011147068220159211846139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34674098045480106141230759 52011147068220159211846139)
      ·
        refine ⟨78016720602330238817769209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52011147068220159211846139 78016720602330238817769209)
        ·
          refine ⟨58512540451747679113326907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78016720602330238817769209 58512540451747679113326907)
          ·
            refine ⟨87768810677621518669990361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58512540451747679113326907 87768810677621518669990361)
            ·
              refine ⟨65826608008216139002492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87768810677621518669990361 65826608008216139002492771)
              ·
                refine ⟨98739912012324208503739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65826608008216139002492771 98739912012324208503739157)
                ·
                  refine ⟨4628433375577697273612773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98739912012324208503739157 4628433375577697273612773)
                  ·
                    refine ⟨867831257920818238802395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628433375577697273612773 867831257920818238802395)
                    ·
                      rfl

theorem cell23_5070286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_5070286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070286 prefixEnd_5070286 := by exact prefixLift 5070286
  have htrace : WordTrace (prefixWord ++ tailWord_5070286) baseStart_5070286 baseEnd_5070286 := by
    simpa [prefixWord, tailWord_5070286, baseEnd_5070286] using wordTrace_append hprefix tailTrace_5070286
  have hstable : (prefixWord ++ tailWord_5070286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070286).length < 2 ^ (prefixWord ++ tailWord_5070286).sum := by decide
  have hdescent : baseEnd_5070286 < baseStart_5070286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070296 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_5070296 : Nat := 118140960795 + 5070296 * 2 ^ 59
def prefixEnd_5070296 : Nat := 4983230072969 + 3 ^ 40 * 5070296 * 2
def baseEnd_5070296 : Nat := 2603498908568999677282139

theorem tailTrace_5070296 : CollatzResearch.WordTrace tailWord_5070296 prefixEnd_5070296 2603498908568999677282139 := by
  unfold tailWord_5070296
  simp only [CollatzResearch.WordTrace]
  refine ⟨92464443819595502230547371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123285925092794002974063161 92464443819595502230547371)
  ·
    refine ⟨138696665729393253345821057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92464443819595502230547371 138696665729393253345821057)
    ·
      refine ⟨104022499297044940009365793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138696665729393253345821057 104022499297044940009365793)
      ·
        refine ⟨78016874472783705007024345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104022499297044940009365793 78016874472783705007024345)
        ·
          refine ⟨58512655854587778755268259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78016874472783705007024345 58512655854587778755268259)
          ·
            refine ⟨87768983781881668132902389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58512655854587778755268259 87768983781881668132902389)
            ·
              refine ⟨8228342229551406387459599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87768983781881668132902389 8228342229551406387459599)
              ·
                refine ⟨12342513344327109581189399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8228342229551406387459599 12342513344327109581189399)
                ·
                  refine ⟨18513770016490664371784099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12342513344327109581189399 18513770016490664371784099)
                  ·
                    refine ⟨27770655024735996557676149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18513770016490664371784099 27770655024735996557676149)
                    ·
                      refine ⟨2603498908568999677282139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27770655024735996557676149 2603498908568999677282139)
                      ·
                        rfl

theorem cell23_5070296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_5070296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070296 prefixEnd_5070296 := by exact prefixLift 5070296
  have htrace : WordTrace (prefixWord ++ tailWord_5070296) baseStart_5070296 baseEnd_5070296 := by
    simpa [prefixWord, tailWord_5070296, baseEnd_5070296] using wordTrace_append hprefix tailTrace_5070296
  have hstable : (prefixWord ++ tailWord_5070296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070296).length < 2 ^ (prefixWord ++ tailWord_5070296).sum := by decide
  have hdescent : baseEnd_5070296 < baseStart_5070296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070303 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 2, 4]
def baseStart_5070303 : Nat := 118140960795 + 5070303 * 2 ^ 59
def prefixEnd_5070303 : Nat := 4983230072969 + 3 ^ 40 * 5070303 * 2
def baseEnd_5070303 : Nat := 867834167644527049964869

theorem tailTrace_5070303 : CollatzResearch.WordTrace tailWord_5070303 prefixEnd_5070303 867834167644527049964869 := by
  unfold tailWord_5070303
  simp only [CollatzResearch.WordTrace]
  refine ⟨184929142950165644656599563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123286095300110429771066375 184929142950165644656599563)
  ·
    refine ⟨277393714425248466984899345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184929142950165644656599563 277393714425248466984899345)
    ·
      refine ⟨208045285818936350238674509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277393714425248466984899345 208045285818936350238674509)
      ·
        refine ⟨78016982182101131339502941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208045285818936350238674509 78016982182101131339502941)
        ·
          refine ⟨29256368318287924252313603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78016982182101131339502941 29256368318287924252313603)
          ·
            refine ⟨43884552477431886378470405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29256368318287924252313603 43884552477431886378470405)
            ·
              refine ⟨8228353589518478695963201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43884552477431886378470405 8228353589518478695963201)
              ·
                refine ⟨6171265192138859021972401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8228353589518478695963201 6171265192138859021972401)
                ·
                  refine ⟨4628448894104144266479301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171265192138859021972401 4628448894104144266479301)
                  ·
                    refine ⟨867834167644527049964869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628448894104144266479301 867834167644527049964869)
                    ·
                      rfl

theorem cell23_5070303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_5070303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070303 prefixEnd_5070303 := by exact prefixLift 5070303
  have htrace : WordTrace (prefixWord ++ tailWord_5070303) baseStart_5070303 baseEnd_5070303 := by
    simpa [prefixWord, tailWord_5070303, baseEnd_5070303] using wordTrace_append hprefix tailTrace_5070303
  have hstable : (prefixWord ++ tailWord_5070303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070303).length < 2 ^ (prefixWord ++ tailWord_5070303).sum := by decide
  have hdescent : baseEnd_5070303 < baseStart_5070303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070319 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_5070319 : Nat := 118140960795 + 5070319 * 2 ^ 59
def prefixEnd_5070319 : Nat := 4983230072969 + 3 ^ 40 * 5070319 * 2
def baseEnd_5070319 : Nat := 2603510718624053087294533

theorem tailTrace_5070319 : CollatzResearch.WordTrace tailWord_5070319 prefixEnd_5070319 2603510718624053087294533 := by
  unfold tailWord_5070319
  simp only [CollatzResearch.WordTrace]
  refine ⟨184929726518107679389182011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123286484345405119592788007 184929726518107679389182011)
  ·
    refine ⟨277394589777161519083773017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184929726518107679389182011 277394589777161519083773017)
    ·
      refine ⟨208045942332871139312829763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277394589777161519083773017 208045942332871139312829763)
      ·
        refine ⟨312068913499306708969244645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208045942332871139312829763 312068913499306708969244645)
        ·
          refine ⟨58512921281120007931733371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312068913499306708969244645 58512921281120007931733371)
          ·
            refine ⟨87769381921680011897600057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58512921281120007931733371 87769381921680011897600057)
            ·
              refine ⟨65827036441260008923200043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87769381921680011897600057 65827036441260008923200043)
              ·
                refine ⟨98740554661890013384800065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65827036441260008923200043 98740554661890013384800065)
                ·
                  refine ⟨74055415996417510038600049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98740554661890013384800065 74055415996417510038600049)
                  ·
                    refine ⟨55541561997313132528950037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74055415996417510038600049 55541561997313132528950037)
                    ·
                      refine ⟨2603510718624053087294533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55541561997313132528950037 2603510718624053087294533)
                      ·
                        rfl

theorem cell23_5070319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_5070319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070319 prefixEnd_5070319 := by exact prefixLift 5070319
  have htrace : WordTrace (prefixWord ++ tailWord_5070319) baseStart_5070319 baseEnd_5070319 := by
    simpa [prefixWord, tailWord_5070319, baseEnd_5070319] using wordTrace_append hprefix tailTrace_5070319
  have hstable : (prefixWord ++ tailWord_5070319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070319).length < 2 ^ (prefixWord ++ tailWord_5070319).sum := by decide
  have hdescent : baseEnd_5070319 < baseStart_5070319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070329 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_5070329 : Nat := 118140960795 + 5070329 * 2 ^ 59
def prefixEnd_5070329 : Nat := 4983230072969 + 3 ^ 40 * 5070329 * 2
def baseEnd_5070329 : Nat := 867838617810199349389829

theorem tailTrace_5070329 : CollatzResearch.WordTrace tailWord_5070329 prefixEnd_5070329 867838617810199349389829 := by
  unfold tailWord_5070329
  simp only [CollatzResearch.WordTrace]
  refine ⟨184930091248071451097046041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123286727498714300731364027 184930091248071451097046041)
  ·
    refine ⟨138697568436053588322784531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184930091248071451097046041 138697568436053588322784531)
    ·
      refine ⟨208046352654080382484176797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138697568436053588322784531 208046352654080382484176797)
      ·
        refine ⟨78017382245280143431566299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208046352654080382484176797 78017382245280143431566299)
        ·
          refine ⟨117026073367920215147349449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78017382245280143431566299 117026073367920215147349449)
          ·
            refine ⟨87769555025940161360512087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117026073367920215147349449 87769555025940161360512087)
            ·
              refine ⟨131654332538910242040768131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87769555025940161360512087 131654332538910242040768131)
              ·
                refine ⟨197481498808365363061152197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131654332538910242040768131 197481498808365363061152197)
                ·
                  refine ⟨37027781026568505573966037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197481498808365363061152197 37027781026568505573966037)
                  ·
                    refine ⟨867838617810199349389829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37027781026568505573966037 867838617810199349389829)
                    ·
                      rfl

theorem cell23_5070329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_5070329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070329 prefixEnd_5070329 := by exact prefixLift 5070329
  have htrace : WordTrace (prefixWord ++ tailWord_5070329) baseStart_5070329 baseEnd_5070329 := by
    simpa [prefixWord, tailWord_5070329, baseEnd_5070329] using wordTrace_append hprefix tailTrace_5070329
  have hstable : (prefixWord ++ tailWord_5070329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070329).length < 2 ^ (prefixWord ++ tailWord_5070329).sum := by decide
  have hdescent : baseEnd_5070329 < baseStart_5070329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070343 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_5070343 : Nat := 118140960795 + 5070343 * 2 ^ 59
def prefixEnd_5070343 : Nat := 4983230072969 + 3 ^ 40 * 5070343 * 2
def baseEnd_5070343 : Nat := 2603523042159760993394423

theorem tailTrace_5070343 : CollatzResearch.WordTrace tailWord_5070343 prefixEnd_5070343 2603523042159760993394423 := by
  unfold tailWord_5070343
  simp only [CollatzResearch.WordTrace]
  refine ⟨184930601870020731488055683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123287067913347154325370455 184930601870020731488055683)
  ·
    refine ⟨277395902805031097232083525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184930601870020731488055683 277395902805031097232083525)
    ·
      refine ⟨52011731775943330731015661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277395902805031097232083525 52011731775943330731015661)
      ·
        refine ⟨19504399415978749024130873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52011731775943330731015661 19504399415978749024130873)
        ·
          refine ⟨14628299561984061768098155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19504399415978749024130873 14628299561984061768098155)
          ·
            refine ⟨21942449342976092652147233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14628299561984061768098155 21942449342976092652147233)
            ·
              refine ⟨16456837007232069489110425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21942449342976092652147233 16456837007232069489110425)
              ·
                refine ⟨12342627755424052116832819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16456837007232069489110425 12342627755424052116832819)
                ·
                  refine ⟨18513941633136078175249229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12342627755424052116832819 18513941633136078175249229)
                  ·
                    refine ⟨6942728112426029315718461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18513941633136078175249229 6942728112426029315718461)
                    ·
                      refine ⟨2603523042159760993394423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6942728112426029315718461 2603523042159760993394423)
                      ·
                        rfl

theorem cell23_5070343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_5070343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070343 prefixEnd_5070343 := by exact prefixLift 5070343
  have htrace : WordTrace (prefixWord ++ tailWord_5070343) baseStart_5070343 baseEnd_5070343 := by
    simpa [prefixWord, tailWord_5070343, baseEnd_5070343] using wordTrace_append hprefix tailTrace_5070343
  have hstable : (prefixWord ++ tailWord_5070343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070343).length < 2 ^ (prefixWord ++ tailWord_5070343).sum := by decide
  have hdescent : baseEnd_5070343 < baseStart_5070343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070347 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 1, 2, 3]
def baseStart_5070347 : Nat := 118140960795 + 5070347 * 2 ^ 59
def prefixEnd_5070347 : Nat := 4983230072969 + 3 ^ 40 * 5070347 * 2
def baseEnd_5070347 : Nat := 2603525096082378977744405

theorem tailTrace_5070347 : CollatzResearch.WordTrace tailWord_5070347 prefixEnd_5070347 2603525096082378977744405 := by
  unfold tailWord_5070347
  simp only [CollatzResearch.WordTrace]
  refine ⟨184930747762006240171201295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123287165174670826780800863 184930747762006240171201295)
  ·
    refine ⟨277396121643009360256801943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184930747762006240171201295 277396121643009360256801943)
    ·
      refine ⟨416094182464514040385202915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277396121643009360256801943 416094182464514040385202915)
      ·
        refine ⟨624141273696771060577804373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416094182464514040385202915 624141273696771060577804373)
        ·
          refine ⟨7314155551134035866146145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 624141273696771060577804373 7314155551134035866146145)
          ·
            refine ⟨5485616663350526899609609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314155551134035866146145 5485616663350526899609609)
            ·
              refine ⟨4114212497512895174707207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485616663350526899609609 4114212497512895174707207)
              ·
                refine ⟨6171318746269342762060811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114212497512895174707207 6171318746269342762060811)
                ·
                  refine ⟨9256978119404014143091217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6171318746269342762060811 9256978119404014143091217)
                  ·
                    refine ⟨6942733589553010607318413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9256978119404014143091217 6942733589553010607318413)
                    ·
                      refine ⟨2603525096082378977744405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6942733589553010607318413 2603525096082378977744405)
                      ·
                        rfl

theorem cell23_5070347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 2, 3].length) (baseStart_5070347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070347 prefixEnd_5070347 := by exact prefixLift 5070347
  have htrace : WordTrace (prefixWord ++ tailWord_5070347) baseStart_5070347 baseEnd_5070347 := by
    simpa [prefixWord, tailWord_5070347, baseEnd_5070347] using wordTrace_append hprefix tailTrace_5070347
  have hstable : (prefixWord ++ tailWord_5070347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070347).length < 2 ^ (prefixWord ++ tailWord_5070347).sum := by decide
  have hdescent : baseEnd_5070347 < baseStart_5070347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070360 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5070360 : Nat := 118140960795 + 5070360 * 2 ^ 59
def prefixEnd_5070360 : Nat := 4983230072969 + 3 ^ 40 * 5070360 * 2
def baseEnd_5070360 : Nat := 2603531771330887426881845

theorem tailTrace_5070360 : CollatzResearch.WordTrace tailWord_5070360 prefixEnd_5070360 2603531771330887426881845 := by
  unfold tailWord_5070360
  simp only [CollatzResearch.WordTrace]
  refine ⟨92465610955479571695712267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123287481273972762260949689 92465610955479571695712267)
  ·
    refine ⟨138698416433219357543568401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92465610955479571695712267 138698416433219357543568401)
    ·
      refine ⟨104023812324914518157676301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138698416433219357543568401 104023812324914518157676301)
      ·
        refine ⟨39008929621842944309128613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104023812324914518157676301 39008929621842944309128613)
        ·
          refine ⟨7314174304095552057961615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39008929621842944309128613 7314174304095552057961615)
          ·
            refine ⟨10971261456143328086942423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7314174304095552057961615 10971261456143328086942423)
            ·
              refine ⟨16456892184214992130413635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10971261456143328086942423 16456892184214992130413635)
              ·
                refine ⟨24685338276322488195620453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16456892184214992130413635 24685338276322488195620453)
                ·
                  refine ⟨4628500926810466536678835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24685338276322488195620453 4628500926810466536678835)
                  ·
                    refine ⟨6942751390215699805018253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4628500926810466536678835 6942751390215699805018253)
                    ·
                      refine ⟨2603531771330887426881845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6942751390215699805018253 2603531771330887426881845)
                      ·
                        rfl

theorem cell23_5070360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5070360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070360 prefixEnd_5070360 := by exact prefixLift 5070360
  have htrace : WordTrace (prefixWord ++ tailWord_5070360) baseStart_5070360 baseEnd_5070360 := by
    simpa [prefixWord, tailWord_5070360, baseEnd_5070360] using wordTrace_append hprefix tailTrace_5070360
  have hstable : (prefixWord ++ tailWord_5070360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070360).length < 2 ^ (prefixWord ++ tailWord_5070360).sum := by decide
  have hdescent : baseEnd_5070360 < baseStart_5070360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070386 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_5070386 : Nat := 118140960795 + 5070386 * 2 ^ 59
def prefixEnd_5070386 : Nat := 4983230072969 + 3 ^ 40 * 5070386 * 2
def baseEnd_5070386 : Nat := 2603545121827904325156725

theorem tailTrace_5070386 : CollatzResearch.WordTrace tailWord_5070386 prefixEnd_5070386 2603545121827904325156725 := by
  unfold tailWord_5070386
  simp only [CollatzResearch.WordTrace]
  refine ⟨46233042552216237457967753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123288113472576633221247341 46233042552216237457967753)
  ·
    refine ⟨34674781914162178093475815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46233042552216237457967753 34674781914162178093475815)
    ·
      refine ⟨52012172871243267140213723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34674781914162178093475815 52012172871243267140213723)
      ·
        refine ⟨78018259306864900710320585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52012172871243267140213723 78018259306864900710320585)
        ·
          refine ⟨58513694480148675532740439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78018259306864900710320585 58513694480148675532740439)
          ·
            refine ⟨87770541720223013299110659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58513694480148675532740439 87770541720223013299110659)
            ·
              refine ⟨131655812580334519948665989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87770541720223013299110659 131655812580334519948665989)
              ·
                refine ⟨24685464858812722490374873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131655812580334519948665989 24685464858812722490374873)
                ·
                  refine ⟨18514098644109541867781155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24685464858812722490374873 18514098644109541867781155)
                  ·
                    refine ⟨27771147966164312801671733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18514098644109541867781155 27771147966164312801671733)
                    ·
                      refine ⟨2603545121827904325156725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27771147966164312801671733 2603545121827904325156725)
                      ·
                        rfl

theorem cell23_5070386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_5070386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070386 prefixEnd_5070386 := by exact prefixLift 5070386
  have htrace : WordTrace (prefixWord ++ tailWord_5070386) baseStart_5070386 baseEnd_5070386 := by
    simpa [prefixWord, tailWord_5070386, baseEnd_5070386] using wordTrace_append hprefix tailTrace_5070386
  have hstable : (prefixWord ++ tailWord_5070386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070386).length < 2 ^ (prefixWord ++ tailWord_5070386).sum := by decide
  have hdescent : baseEnd_5070386 < baseStart_5070386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070423 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 7]
def baseStart_5070423 : Nat := 118140960795 + 5070423 * 2 ^ 59
def prefixEnd_5070423 : Nat := 4983230072969 + 3 ^ 40 * 5070423 * 2
def baseEnd_5070423 : Nat := 289284902290235631154895

theorem tailTrace_5070423 : CollatzResearch.WordTrace tailWord_5070423 prefixEnd_5070423 289284902290235631154895 := by
  unfold tailWord_5070423
  simp only [CollatzResearch.WordTrace]
  refine ⟨184933519709730905150967923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123289013139820603433978615 184933519709730905150967923)
  ·
    refine ⟨277400279564596357726451885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184933519709730905150967923 277400279564596357726451885)
    ·
      refine ⟨104025104836723634147419457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277400279564596357726451885 104025104836723634147419457)
      ·
        refine ⟨78018828627542725610564593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104025104836723634147419457 78018828627542725610564593)
        ·
          refine ⟨58514121470657044207923445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78018828627542725610564593 58514121470657044207923445)
          ·
            refine ⟨5485698887874097894492823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58514121470657044207923445 5485698887874097894492823)
            ·
              refine ⟨8228548331811146841739235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485698887874097894492823 8228548331811146841739235)
              ·
                refine ⟨12342822497716720262608853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8228548331811146841739235 12342822497716720262608853)
                ·
                  refine ⟨289284902290235631154895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12342822497716720262608853 289284902290235631154895)
                  ·
                    rfl

theorem cell23_5070423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 7].length) (baseStart_5070423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070423 prefixEnd_5070423 := by exact prefixLift 5070423
  have htrace : WordTrace (prefixWord ++ tailWord_5070423) baseStart_5070423 baseEnd_5070423 := by
    simpa [prefixWord, tailWord_5070423, baseEnd_5070423] using wordTrace_append hprefix tailTrace_5070423
  have hstable : (prefixWord ++ tailWord_5070423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070423).length < 2 ^ (prefixWord ++ tailWord_5070423).sum := by decide
  have hdescent : baseEnd_5070423 < baseStart_5070423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070473 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_5070473 : Nat := 118140960795 + 5070473 * 2 ^ 59
def prefixEnd_5070473 : Nat := 4983230072969 + 3 ^ 40 * 5070473 * 2
def baseEnd_5070473 : Nat := 2603589794644845484768825

theorem tailTrace_5070473 : CollatzResearch.WordTrace tailWord_5070473 prefixEnd_5070473 2603589794644845484768825 := by
  unfold tailWord_5070473
  simp only [CollatzResearch.WordTrace]
  refine ⟨184935343359549763690288073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123290228906366509126858715 184935343359549763690288073)
  ·
    refine ⟨138701507519662322767716055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184935343359549763690288073 138701507519662322767716055)
    ·
      refine ⟨208052261279493484151574083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138701507519662322767716055 208052261279493484151574083)
      ·
        refine ⟨312078391919240226227361125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208052261279493484151574083 312078391919240226227361125)
        ·
          refine ⟨58514698484857542417630211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312078391919240226227361125 58514698484857542417630211)
          ·
            refine ⟨87772047727286313626445317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58514698484857542417630211 87772047727286313626445317)
            ·
              refine ⟨16457258948866183804958497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87772047727286313626445317 16457258948866183804958497)
              ·
                refine ⟨12342944211649637853718873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16457258948866183804958497 12342944211649637853718873)
                ·
                  refine ⟨9257208158737228390289155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12342944211649637853718873 9257208158737228390289155)
                  ·
                    refine ⟨13885812238105842585433733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9257208158737228390289155 13885812238105842585433733)
                    ·
                      refine ⟨2603589794644845484768825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13885812238105842585433733 2603589794644845484768825)
                      ·
                        rfl

theorem cell23_5070473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_5070473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070473 prefixEnd_5070473 := by exact prefixLift 5070473
  have htrace : WordTrace (prefixWord ++ tailWord_5070473) baseStart_5070473 baseEnd_5070473 := by
    simpa [prefixWord, tailWord_5070473, baseEnd_5070473] using wordTrace_append hprefix tailTrace_5070473
  have hstable : (prefixWord ++ tailWord_5070473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070473).length < 2 ^ (prefixWord ++ tailWord_5070473).sum := by decide
  have hdescent : baseEnd_5070473 < baseStart_5070473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070476 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5070476 : Nat := 118140960795 + 5070476 * 2 ^ 59
def prefixEnd_5070476 : Nat := 4983230072969 + 3 ^ 40 * 5070476 * 2
def baseEnd_5070476 : Nat := 2603591335086808973031311

theorem tailTrace_5070476 : CollatzResearch.WordTrace tailWord_5070476 prefixEnd_5070476 2603591335086808973031311 := by
  unfold tailWord_5070476
  simp only [CollatzResearch.WordTrace]
  refine ⟨92467726389269447601323641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123290301852359263468431521 92467726389269447601323641)
  ·
    refine ⟨69350794791952085700992731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92467726389269447601323641 69350794791952085700992731)
    ·
      refine ⟨104026192187928128551489097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69350794791952085700992731 104026192187928128551489097)
      ·
        refine ⟨78019644140946096413616823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104026192187928128551489097 78019644140946096413616823)
        ·
          refine ⟨117029466211419144620425235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78019644140946096413616823 117029466211419144620425235)
          ·
            refine ⟨175544199317128716930637853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117029466211419144620425235 175544199317128716930637853)
            ·
              refine ⟨65829074743923268848989195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175544199317128716930637853 65829074743923268848989195)
              ·
                refine ⟨98743612115884903273483793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65829074743923268848989195 98743612115884903273483793)
                ·
                  refine ⟨74057709086913677455112845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98743612115884903273483793 74057709086913677455112845)
                  ·
                    refine ⟨27771640907592629045667317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74057709086913677455112845 27771640907592629045667317)
                    ·
                      refine ⟨2603591335086808973031311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27771640907592629045667317 2603591335086808973031311)
                      ·
                        rfl

theorem cell23_5070476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5070476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070476 prefixEnd_5070476 := by exact prefixLift 5070476
  have htrace : WordTrace (prefixWord ++ tailWord_5070476) baseStart_5070476 baseEnd_5070476 := by
    simpa [prefixWord, tailWord_5070476, baseEnd_5070476] using wordTrace_append hprefix tailTrace_5070476
  have hstable : (prefixWord ++ tailWord_5070476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070476).length < 2 ^ (prefixWord ++ tailWord_5070476).sum := by decide
  have hdescent : baseEnd_5070476 < baseStart_5070476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070493 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_5070493 : Nat := 118140960795 + 5070493 * 2 ^ 59
def prefixEnd_5070493 : Nat := 4983230072969 + 3 ^ 40 * 5070493 * 2
def baseEnd_5070493 : Nat := 2603600064257935406518733

theorem tailTrace_5070493 : CollatzResearch.WordTrace tailWord_5070493 prefixEnd_5070493 2603600064257935406518733 := by
  unfold tailWord_5070493
  simp only [CollatzResearch.WordTrace]
  refine ⟨184936072819477307106016133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123290715212984871404010755 184936072819477307106016133)
  ·
    refine ⟨34675513653651995082378025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184936072819477307106016133 34675513653651995082378025)
    ·
      refine ⟨26006635240238996311783519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34675513653651995082378025 26006635240238996311783519)
      ·
        refine ⟨39009952860358494467675279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26006635240238996311783519 39009952860358494467675279)
        ·
          refine ⟨58514929290537741701512919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39009952860358494467675279 58514929290537741701512919)
          ·
            refine ⟨87772393935806612552269379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58514929290537741701512919 87772393935806612552269379)
            ·
              refine ⟨131658590903709918828404069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87772393935806612552269379 131658590903709918828404069)
              ·
                refine ⟨24685985794445609780325763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131658590903709918828404069 24685985794445609780325763)
                ·
                  refine ⟨37028978691668414670488645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24685985794445609780325763 37028978691668414670488645)
                  ·
                    refine ⟨6942933504687827750716621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37028978691668414670488645 6942933504687827750716621)
                    ·
                      refine ⟨2603600064257935406518733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6942933504687827750716621 2603600064257935406518733)
                      ·
                        rfl

theorem cell23_5070493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_5070493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070493 prefixEnd_5070493 := by exact prefixLift 5070493
  have htrace : WordTrace (prefixWord ++ tailWord_5070493) baseStart_5070493 baseEnd_5070493 := by
    simpa [prefixWord, tailWord_5070493, baseEnd_5070493] using wordTrace_append hprefix tailTrace_5070493
  have hstable : (prefixWord ++ tailWord_5070493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070493).length < 2 ^ (prefixWord ++ tailWord_5070493).sum := by decide
  have hdescent : baseEnd_5070493 < baseStart_5070493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070500 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_5070500 : Nat := 118140960795 + 5070500 * 2 ^ 59
def prefixEnd_5070500 : Nat := 4983230072969 + 3 ^ 40 * 5070500 * 2
def baseEnd_5070500 : Nat := 867867886207505626377067

theorem tailTrace_5070500 : CollatzResearch.WordTrace tailWord_5070500 prefixEnd_5070500 867867886207505626377067 := by
  unfold tailWord_5070500
  simp only [CollatzResearch.WordTrace]
  refine ⟨92468164065225973650760477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123290885420301298201013969 92468164065225973650760477)
  ·
    refine ⟨34675561524459740119035179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92468164065225973650760477 34675561524459740119035179)
    ·
      refine ⟨52013342286689610178552769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34675561524459740119035179 52013342286689610178552769)
      ·
        refine ⟨39010006715017207633914577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52013342286689610178552769 39010006715017207633914577)
        ·
          refine ⟨29257505036262905725435933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39010006715017207633914577 29257505036262905725435933)
          ·
            refine ⟨10971564388598589647038475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29257505036262905725435933 10971564388598589647038475)
            ·
              refine ⟨16457346582897884470557713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10971564388598589647038475 16457346582897884470557713)
              ·
                refine ⟨12343009937173413352918285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16457346582897884470557713 12343009937173413352918285)
                ·
                  refine ⟨4628628726440030007344357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12343009937173413352918285 4628628726440030007344357)
                  ·
                    refine ⟨867867886207505626377067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628628726440030007344357 867867886207505626377067)
                    ·
                      rfl

theorem cell23_5070500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_5070500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070500 prefixEnd_5070500 := by exact prefixLift 5070500
  have htrace : WordTrace (prefixWord ++ tailWord_5070500) baseStart_5070500 baseEnd_5070500 := by
    simpa [prefixWord, tailWord_5070500, baseEnd_5070500] using wordTrace_append hprefix tailTrace_5070500
  have hstable : (prefixWord ++ tailWord_5070500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070500).length < 2 ^ (prefixWord ++ tailWord_5070500).sum := by decide
  have hdescent : baseEnd_5070500 < baseStart_5070500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070534 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5070534 : Nat := 118140960795 + 5070534 * 2 ^ 59
def prefixEnd_5070534 : Nat := 4983230072969 + 3 ^ 40 * 5070534 * 2
def baseEnd_5070534 : Nat := 867873705654923248702015

theorem tailTrace_5070534 : CollatzResearch.WordTrace tailWord_5070534 prefixEnd_5070534 867873705654923248702015 := by
  unfold tailWord_5070534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779299006635274097133083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123291712141552514072172437 5779299006635274097133083)
  ·
    refine ⟨8668948509952911145699625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779299006635274097133083 8668948509952911145699625)
    ·
      refine ⟨6501711382464683359274719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8668948509952911145699625 6501711382464683359274719)
      ·
        refine ⟨9752567073697025038912079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501711382464683359274719 9752567073697025038912079)
        ·
          refine ⟨14628850610545537558368119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9752567073697025038912079 14628850610545537558368119)
          ·
            refine ⟨21943275915818306337552179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14628850610545537558368119 21943275915818306337552179)
            ·
              refine ⟨32914913873727459506328269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21943275915818306337552179 32914913873727459506328269)
              ·
                refine ⟨12343092702647797314873101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32914913873727459506328269 12343092702647797314873101)
                ·
                  refine ⟨4628659763492923993077413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12343092702647797314873101 4628659763492923993077413)
                  ·
                    refine ⟨867873705654923248702015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628659763492923993077413 867873705654923248702015)
                    ·
                      rfl

theorem cell23_5070534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5070534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070534 prefixEnd_5070534 := by exact prefixLift 5070534
  have htrace : WordTrace (prefixWord ++ tailWord_5070534) baseStart_5070534 baseEnd_5070534 := by
    simpa [prefixWord, tailWord_5070534, baseEnd_5070534] using wordTrace_append hprefix tailTrace_5070534
  have hstable : (prefixWord ++ tailWord_5070534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070534).length < 2 ^ (prefixWord ++ tailWord_5070534).sum := by decide
  have hdescent : baseEnd_5070534 < baseStart_5070534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070583 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_5070583 : Nat := 118140960795 + 5070583 * 2 ^ 59
def prefixEnd_5070583 : Nat := 4983230072969 + 3 ^ 40 * 5070583 * 2
def baseEnd_5070583 : Nat := 2603646277516840054393319

theorem tailTrace_5070583 : CollatzResearch.WordTrace tailWord_5070583 prefixEnd_5070583 2603646277516840054393319 := by
  unfold tailWord_5070583
  simp only [CollatzResearch.WordTrace]
  refine ⟨184939355389151252476792403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123292903592767501651194935 184939355389151252476792403)
  ·
    refine ⟨277409033083726878715188605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184939355389151252476792403 277409033083726878715188605)
    ·
      refine ⟨104028387406397579518195727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277409033083726878715188605 104028387406397579518195727)
      ·
        refine ⟨156042581109596369277293591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104028387406397579518195727 156042581109596369277293591)
        ·
          refine ⟨234063871664394553915940387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156042581109596369277293591 234063871664394553915940387)
          ·
            refine ⟨351095807496591830873910581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234063871664394553915940387 351095807496591830873910581)
            ·
              refine ⟨32915231952805484144429117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 351095807496591830873910581 32915231952805484144429117)
              ·
                refine ⟨12343211982302056554160919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32915231952805484144429117 12343211982302056554160919)
                ·
                  refine ⟨18514817973453084831241379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12343211982302056554160919 18514817973453084831241379)
                  ·
                    refine ⟨27772226960179627246862069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18514817973453084831241379 27772226960179627246862069)
                    ·
                      refine ⟨2603646277516840054393319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27772226960179627246862069 2603646277516840054393319)
                      ·
                        rfl

theorem cell23_5070583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_5070583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070583 prefixEnd_5070583 := by exact prefixLift 5070583
  have htrace : WordTrace (prefixWord ++ tailWord_5070583) baseStart_5070583 baseEnd_5070583 := by
    simpa [prefixWord, tailWord_5070583, baseEnd_5070583] using wordTrace_append hprefix tailTrace_5070583
  have hstable : (prefixWord ++ tailWord_5070583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070583).length < 2 ^ (prefixWord ++ tailWord_5070583).sum := by decide
  have hdescent : baseEnd_5070583 < baseStart_5070583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070593 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_5070593 : Nat := 118140960795 + 5070593 * 2 ^ 59
def prefixEnd_5070593 : Nat := 4983230072969 + 3 ^ 40 * 5070593 * 2
def baseEnd_5070593 : Nat := 2603651412323385015268273

theorem tailTrace_5070593 : CollatzResearch.WordTrace tailWord_5070593 prefixEnd_5070593 2603651412323385015268273 := by
  unfold tailWord_5070593
  simp only [CollatzResearch.WordTrace]
  refine ⟨184939720119115024184656433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123293146746076682789770955 184939720119115024184656433)
  ·
    refine ⟨138704790089336268138492325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184939720119115024184656433 138704790089336268138492325)
    ·
      refine ⟨26007148141750550275967311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138704790089336268138492325 26007148141750550275967311)
      ·
        refine ⟨39010722212625825413950967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26007148141750550275967311 39010722212625825413950967)
        ·
          refine ⟨58516083318938738120926451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39010722212625825413950967 58516083318938738120926451)
          ·
            refine ⟨87774124978408107181389677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58516083318938738120926451 87774124978408107181389677)
            ·
              refine ⟨32915296866903040193021129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87774124978408107181389677 32915296866903040193021129)
              ·
                refine ⟨24686472650177280144765847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32915296866903040193021129 24686472650177280144765847)
                ·
                  refine ⟨37029708975265920217148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24686472650177280144765847 37029708975265920217148771)
                  ·
                    refine ⟨55544563462898880325723157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37029708975265920217148771 55544563462898880325723157)
                    ·
                      refine ⟨2603651412323385015268273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55544563462898880325723157 2603651412323385015268273)
                      ·
                        rfl

theorem cell23_5070593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_5070593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070593 prefixEnd_5070593 := by exact prefixLift 5070593
  have htrace : WordTrace (prefixWord ++ tailWord_5070593) baseStart_5070593 baseEnd_5070593 := by
    simpa [prefixWord, tailWord_5070593, baseEnd_5070593] using wordTrace_append hprefix tailTrace_5070593
  have hstable : (prefixWord ++ tailWord_5070593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070593).length < 2 ^ (prefixWord ++ tailWord_5070593).sum := by decide
  have hdescent : baseEnd_5070593 < baseStart_5070593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070598 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5070598 : Nat := 118140960795 + 5070598 * 2 ^ 59
def prefixEnd_5070598 : Nat := 4983230072969 + 3 ^ 40 * 5070598 * 2
def baseEnd_5070598 : Nat := 289294886636295277300639

theorem tailTrace_5070598 : CollatzResearch.WordTrace tailWord_5070598 prefixEnd_5070598 289294886636295277300639 := by
  unfold tailWord_5070598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779371952628028438705889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123293268322731273359058965 5779371952628028438705889)
  ·
    refine ⟨4334528964471021329029417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5779371952628028438705889 4334528964471021329029417)
    ·
      refine ⟨3250896723353265996772063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334528964471021329029417 3250896723353265996772063)
      ·
        refine ⟨4876345085029898995158095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250896723353265996772063 4876345085029898995158095)
        ·
          refine ⟨7314517627544848492737143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876345085029898995158095 7314517627544848492737143)
          ·
            refine ⟨10971776441317272739105715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7314517627544848492737143 10971776441317272739105715)
            ·
              refine ⟨16457664661975909108658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10971776441317272739105715 16457664661975909108658573)
              ·
                refine ⟨6171624248240965915746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16457664661975909108658573 6171624248240965915746965)
                ·
                  refine ⟨289294886636295277300639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6171624248240965915746965 289294886636295277300639)
                  ·
                    rfl

theorem cell23_5070598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5070598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070598 prefixEnd_5070598 := by exact prefixLift 5070598
  have htrace : WordTrace (prefixWord ++ tailWord_5070598) baseStart_5070598 baseEnd_5070598 := by
    simpa [prefixWord, tailWord_5070598, baseEnd_5070598] using wordTrace_append hprefix tailTrace_5070598
  have hstable : (prefixWord ++ tailWord_5070598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070598).length < 2 ^ (prefixWord ++ tailWord_5070598).sum := by decide
  have hdescent : baseEnd_5070598 < baseStart_5070598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070600 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_5070600 : Nat := 118140960795 + 5070600 * 2 ^ 59
def prefixEnd_5070600 : Nat := 4983230072969 + 3 ^ 40 * 5070600 * 2
def baseEnd_5070600 : Nat := 2603655006687966487880741

theorem tailTrace_5070600 : CollatzResearch.WordTrace tailWord_5070600 prefixEnd_5070600 2603655006687966487880741 := by
  unfold tailWord_5070600
  simp only [CollatzResearch.WordTrace]
  refine ⟨92469987715044832190080627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123293316953393109586774169 92469987715044832190080627)
  ·
    refine ⟨138704981572567248285120941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92469987715044832190080627 138704981572567248285120941)
    ·
      refine ⟨52014368089712718106920353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138704981572567248285120941 52014368089712718106920353)
      ·
        refine ⟨39010776067284538580190265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52014368089712718106920353 39010776067284538580190265)
        ·
          refine ⟨29258082050463403935142699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39010776067284538580190265 29258082050463403935142699)
          ·
            refine ⟨43887123075695105902714049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29258082050463403935142699 43887123075695105902714049)
            ·
              refine ⟨32915342306771329427035537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43887123075695105902714049 32915342306771329427035537)
              ·
                refine ⟨24686506730078497070276653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32915342306771329427035537 24686506730078497070276653)
                ·
                  refine ⟨9257440023779436401353745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24686506730078497070276653 9257440023779436401353745)
                  ·
                    refine ⟨6943080017834577301015309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9257440023779436401353745 6943080017834577301015309)
                    ·
                      refine ⟨2603655006687966487880741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943080017834577301015309 2603655006687966487880741)
                      ·
                        rfl

theorem cell23_5070600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_5070600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070600 prefixEnd_5070600 := by exact prefixLift 5070600
  have htrace : WordTrace (prefixWord ++ tailWord_5070600) baseStart_5070600 baseEnd_5070600 := by
    simpa [prefixWord, tailWord_5070600, baseEnd_5070600] using wordTrace_append hprefix tailTrace_5070600
  have hstable : (prefixWord ++ tailWord_5070600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070600).length < 2 ^ (prefixWord ++ tailWord_5070600).sum := by decide
  have hdescent : baseEnd_5070600 < baseStart_5070600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070648 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 1, 2, 2]
def baseStart_5070648 : Nat := 118140960795 + 5070648 * 2 ^ 59
def prefixEnd_5070648 : Nat := 4983230072969 + 3 ^ 40 * 5070648 * 2
def baseEnd_5070648 : Nat := 2603679653759382300080521

theorem tailTrace_5070648 : CollatzResearch.WordTrace tailWord_5070648 prefixEnd_5070648 2603679653759382300080521 := by
  unfold tailWord_5070648
  simp only [CollatzResearch.WordTrace]
  refine ⟨92470863066957884288954299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123294484089277179051939065 92470863066957884288954299)
  ·
    refine ⟨138706294600436826433431449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92470863066957884288954299 138706294600436826433431449)
    ·
      refine ⟨104029720950327619825073587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138706294600436826433431449 104029720950327619825073587)
      ·
        refine ⟨156044581425491429737610381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104029720950327619825073587 156044581425491429737610381)
        ·
          refine ⟨58516718034559286151603893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156044581425491429737610381 58516718034559286151603893)
          ·
            refine ⟨5485942315739933076712865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58516718034559286151603893 5485942315739933076712865)
            ·
              refine ⟨4114456736804949807534649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485942315739933076712865 4114456736804949807534649)
              ·
                refine ⟨3085842552603712355650987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114456736804949807534649 3085842552603712355650987)
                ·
                  refine ⟨4628763828905568533476481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085842552603712355650987 4628763828905568533476481)
                  ·
                    refine ⟨3471572871679176400107361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4628763828905568533476481 3471572871679176400107361)
                    ·
                      refine ⟨2603679653759382300080521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471572871679176400107361 2603679653759382300080521)
                      ·
                        rfl

theorem cell23_5070648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_5070648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070648 prefixEnd_5070648 := by exact prefixLift 5070648
  have htrace : WordTrace (prefixWord ++ tailWord_5070648) baseStart_5070648 baseEnd_5070648 := by
    simpa [prefixWord, tailWord_5070648, baseEnd_5070648] using wordTrace_append hprefix tailTrace_5070648
  have hstable : (prefixWord ++ tailWord_5070648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070648).length < 2 ^ (prefixWord ++ tailWord_5070648).sum := by decide
  have hdescent : baseEnd_5070648 < baseStart_5070648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070663 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 8]
def baseStart_5070663 : Nat := 118140960795 + 5070663 * 2 ^ 59
def prefixEnd_5070663 : Nat := 4983230072969 + 3 ^ 40 * 5070663 * 2
def baseEnd_5070663 : Nat := 867895785323066580464317

theorem tailTrace_5070663 : CollatzResearch.WordTrace tailWord_5070663 prefixEnd_5070663 867895785323066580464317 := by
  unfold tailWord_5070663
  simp only [CollatzResearch.WordTrace]
  refine ⟨184942273228861426139704643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123294848819240950759803095 184942273228861426139704643)
  ·
    refine ⟨277413409843292139209556965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184942273228861426139704643 277413409843292139209556965)
    ·
      refine ⟨52015014345617276101791931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277413409843292139209556965 52015014345617276101791931)
      ·
        refine ⟨78022521518425914152687897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52015014345617276101791931 78022521518425914152687897)
        ·
          refine ⟨58516891138819435614515923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78022521518425914152687897 58516891138819435614515923)
          ·
            refine ⟨87775336708229153421773885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58516891138819435614515923 87775336708229153421773885)
            ·
              refine ⟨32915751265585932533165207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87775336708229153421773885 32915751265585932533165207)
              ·
                refine ⟨49373626898378898799747811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32915751265585932533165207 49373626898378898799747811)
                ·
                  refine ⟨74060440347568348199621717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49373626898378898799747811 74060440347568348199621717)
                  ·
                    refine ⟨867895785323066580464317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74060440347568348199621717 867895785323066580464317)
                    ·
                      rfl

theorem cell23_5070663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_5070663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070663 prefixEnd_5070663 := by exact prefixLift 5070663
  have htrace : WordTrace (prefixWord ++ tailWord_5070663) baseStart_5070663 baseEnd_5070663 := by
    simpa [prefixWord, tailWord_5070663, baseEnd_5070663] using wordTrace_append hprefix tailTrace_5070663
  have hstable : (prefixWord ++ tailWord_5070663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070663).length < 2 ^ (prefixWord ++ tailWord_5070663).sum := by decide
  have hdescent : baseEnd_5070663 < baseStart_5070663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070687 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 1, 4, 2]
def baseStart_5070687 : Nat := 118140960795 + 5070687 * 2 ^ 59
def prefixEnd_5070687 : Nat := 4983230072969 + 3 ^ 40 * 5070687 * 2
def baseEnd_5070687 : Nat := 2603699679504907647492841

theorem tailTrace_5070687 : CollatzResearch.WordTrace tailWord_5070687 prefixEnd_5070687 2603699679504907647492841 := by
  unfold tailWord_5070687
  simp only [CollatzResearch.WordTrace]
  refine ⟨184943148580774478238578315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123295432387182985492385543 184943148580774478238578315)
  ·
    refine ⟨277414722871161717357867473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184943148580774478238578315 277414722871161717357867473)
    ·
      refine ⟨208061042153371288018400605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277414722871161717357867473 208061042153371288018400605)
      ·
        refine ⟨78022890807514233006900227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208061042153371288018400605 78022890807514233006900227)
        ·
          refine ⟨117034336211271349510350341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78022890807514233006900227 117034336211271349510350341)
          ·
            refine ⟨21943938039613378033190689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117034336211271349510350341 21943938039613378033190689)
            ·
              refine ⟨16457953529710033524893017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21943938039613378033190689 16457953529710033524893017)
              ·
                refine ⟨12343465147282525143669763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16457953529710033524893017 12343465147282525143669763)
                ·
                  refine ⟨18515197720923787715504645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12343465147282525143669763 18515197720923787715504645)
                  ·
                    refine ⟨3471599572673210196657121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18515197720923787715504645 3471599572673210196657121)
                    ·
                      refine ⟨2603699679504907647492841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471599572673210196657121 2603699679504907647492841)
                      ·
                        rfl

theorem cell23_5070687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_5070687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070687 prefixEnd_5070687 := by exact prefixLift 5070687
  have htrace : WordTrace (prefixWord ++ tailWord_5070687) baseStart_5070687 baseEnd_5070687 := by
    simpa [prefixWord, tailWord_5070687, baseEnd_5070687] using wordTrace_append hprefix tailTrace_5070687
  have hstable : (prefixWord ++ tailWord_5070687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070687).length < 2 ^ (prefixWord ++ tailWord_5070687).sum := by decide
  have hdescent : baseEnd_5070687 < baseStart_5070687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070693 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 11]
def baseStart_5070693 : Nat := 118140960795 + 5070693 * 2 ^ 59
def prefixEnd_5070693 : Nat := 4983230072969 + 3 ^ 40 * 5070693 * 2
def baseEnd_5070693 : Nat := 289300306709870513779757

theorem tailTrace_5070693 : CollatzResearch.WordTrace tailWord_5070693 prefixEnd_5070693 289300306709870513779757 := by
  unfold tailWord_5070693
  simp only [CollatzResearch.WordTrace]
  refine ⟨184943367418752741263296733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123295578279168494175531155 184943367418752741263296733)
  ·
    refine ⟨69353762782032277973736275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184943367418752741263296733 69353762782032277973736275)
    ·
      refine ⟨104030644173048416960604413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69353762782032277973736275 104030644173048416960604413)
      ·
        refine ⟨39011491564893156360226655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104030644173048416960604413 39011491564893156360226655)
        ·
          refine ⟨58517237347339734540339983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39011491564893156360226655 58517237347339734540339983)
          ·
            refine ⟨87775856021009601810509975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58517237347339734540339983 87775856021009601810509975)
            ·
              refine ⟨131663784031514402715764963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87775856021009601810509975 131663784031514402715764963)
              ·
                refine ⟨197495676047271604073647445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131663784031514402715764963 197495676047271604073647445)
                ·
                  refine ⟨289300306709870513779757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 197495676047271604073647445 289300306709870513779757)
                  ·
                    rfl

theorem cell23_5070693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_5070693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070693 prefixEnd_5070693 := by exact prefixLift 5070693
  have htrace : WordTrace (prefixWord ++ tailWord_5070693) baseStart_5070693 baseEnd_5070693 := by
    simpa [prefixWord, tailWord_5070693, baseEnd_5070693] using wordTrace_append hprefix tailTrace_5070693
  have hstable : (prefixWord ++ tailWord_5070693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070693).length < 2 ^ (prefixWord ++ tailWord_5070693).sum := by decide
  have hdescent : baseEnd_5070693 < baseStart_5070693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070698 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5070698 : Nat := 118140960795 + 5070698 * 2 ^ 59
def prefixEnd_5070698 : Nat := 4983230072969 + 3 ^ 40 * 5070698 * 2
def baseEnd_5070698 : Nat := 2603705327792107104455291

theorem tailTrace_5070698 : CollatzResearch.WordTrace tailWord_5070698 prefixEnd_5070698 2603705327792107104455291 := by
  unfold tailWord_5070698
  simp only [CollatzResearch.WordTrace]
  refine ⟨46235887445933656779307187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123295699855823084744819165 46235887445933656779307187)
  ·
    refine ⟨69353831168900485168960781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46235887445933656779307187 69353831168900485168960781)
    ·
      refine ⟨26007686688337681938360293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69353831168900485168960781 26007686688337681938360293)
      ·
        refine ⟨4876441254063315363442555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26007686688337681938360293 4876441254063315363442555)
        ·
          refine ⟨7314661881094973045163833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876441254063315363442555 7314661881094973045163833)
          ·
            refine ⟨5485996410821229783872875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314661881094973045163833 5485996410821229783872875)
            ·
              refine ⟨8228994616231844675809313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485996410821229783872875 8228994616231844675809313)
              ·
                refine ⟨6171745962173883506856985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8228994616231844675809313 6171745962173883506856985)
                ·
                  refine ⟨4628809471630412630142739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171745962173883506856985 4628809471630412630142739)
                  ·
                    refine ⟨6943214207445618945214109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4628809471630412630142739 6943214207445618945214109)
                    ·
                      refine ⟨2603705327792107104455291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943214207445618945214109 2603705327792107104455291)
                      ·
                        rfl

theorem cell23_5070698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5070698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070698 prefixEnd_5070698 := by exact prefixLift 5070698
  have htrace : WordTrace (prefixWord ++ tailWord_5070698) baseStart_5070698 baseEnd_5070698 := by
    simpa [prefixWord, tailWord_5070698, baseEnd_5070698] using wordTrace_append hprefix tailTrace_5070698
  have hstable : (prefixWord ++ tailWord_5070698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070698).length < 2 ^ (prefixWord ++ tailWord_5070698).sum := by decide
  have hdescent : baseEnd_5070698 < baseStart_5070698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070700 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_5070700 : Nat := 118140960795 + 5070700 * 2 ^ 59
def prefixEnd_5070700 : Nat := 4983230072969 + 3 ^ 40 * 5070700 * 2
def baseEnd_5070700 : Nat := 2603706354753416096630281

theorem tailTrace_5070700 : CollatzResearch.WordTrace tailWord_5070700 prefixEnd_5070700 2603706354753416096630281 := by
  unfold tailWord_5070700
  simp only [CollatzResearch.WordTrace]
  refine ⟨92471811364863690729400777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123295748486484920972534369 92471811364863690729400777)
  ·
    refine ⟨69353858523647768047050583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92471811364863690729400777 69353858523647768047050583)
    ·
      refine ⟨104030787785471652070575875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69353858523647768047050583 104030787785471652070575875)
      ·
        refine ⟨156046181678207478105863813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104030787785471652070575875 156046181678207478105863813)
        ·
          refine ⟨29258659064663902144849465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156046181678207478105863813 29258659064663902144849465)
          ·
            refine ⟨21943994298497926608637099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29258659064663902144849465 21943994298497926608637099)
            ·
              refine ⟨32915991447746889912955649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21943994298497926608637099 32915991447746889912955649)
              ·
                refine ⟨24686993585810167434716737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32915991447746889912955649 24686993585810167434716737)
                ·
                  refine ⟨18515245189357625576037553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24686993585810167434716737 18515245189357625576037553)
                  ·
                    refine ⟨13886433892018219182028165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18515245189357625576037553 13886433892018219182028165)
                    ·
                      refine ⟨2603706354753416096630281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13886433892018219182028165 2603706354753416096630281)
                      ·
                        rfl

theorem cell23_5070700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_5070700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070700 prefixEnd_5070700 := by exact prefixLift 5070700
  have htrace : WordTrace (prefixWord ++ tailWord_5070700) baseStart_5070700 baseEnd_5070700 := by
    simpa [prefixWord, tailWord_5070700, baseEnd_5070700] using wordTrace_append hprefix tailTrace_5070700
  have hstable : (prefixWord ++ tailWord_5070700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070700).length < 2 ^ (prefixWord ++ tailWord_5070700).sum := by decide
  have hdescent : baseEnd_5070700 < baseStart_5070700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070720 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_5070720 : Nat := 118140960795 + 5070720 * 2 ^ 59
def prefixEnd_5070720 : Nat := 4983230072969 + 3 ^ 40 * 5070720 * 2
def baseEnd_5070720 : Nat := 2603716624366506018380189

theorem tailTrace_5070720 : CollatzResearch.WordTrace tailWord_5070720 prefixEnd_5070720 2603716624366506018380189 := by
  unfold tailWord_5070720
  simp only [CollatzResearch.WordTrace]
  refine ⟨92472176094827462437264807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123296234793103283249686409 92472176094827462437264807)
  ·
    refine ⟨138708264142241193655897211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92472176094827462437264807 138708264142241193655897211)
    ·
      refine ⟨208062396213361790483845817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138708264142241193655897211 208062396213361790483845817)
      ·
        refine ⟨156046797160021342862884363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208062396213361790483845817 156046797160021342862884363)
        ·
          refine ⟨234070195740032014294326545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156046797160021342862884363 234070195740032014294326545)
          ·
            refine ⟨175552646805024010720744909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234070195740032014294326545 175552646805024010720744909)
            ·
              refine ⟨65832242551884004020279341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175552646805024010720744909 65832242551884004020279341)
              ·
                refine ⟨24687090956956501507604753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65832242551884004020279341 24687090956956501507604753)
                ·
                  refine ⟨18515318217717376130703565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24687090956956501507604753 18515318217717376130703565)
                  ·
                    refine ⟨6943244331644016049013837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18515318217717376130703565 6943244331644016049013837)
                    ·
                      refine ⟨2603716624366506018380189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943244331644016049013837 2603716624366506018380189)
                      ·
                        rfl

theorem cell23_5070720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_5070720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070720 prefixEnd_5070720 := by exact prefixLift 5070720
  have htrace : WordTrace (prefixWord ++ tailWord_5070720) baseStart_5070720 baseEnd_5070720 := by
    simpa [prefixWord, tailWord_5070720, baseEnd_5070720] using wordTrace_append hprefix tailTrace_5070720
  have hstable : (prefixWord ++ tailWord_5070720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070720).length < 2 ^ (prefixWord ++ tailWord_5070720).sum := by decide
  have hdescent : baseEnd_5070720 < baseStart_5070720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070772 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5070772 : Nat := 118140960795 + 5070772 * 2 ^ 59
def prefixEnd_5070772 : Nat := 4983230072969 + 3 ^ 40 * 5070772 * 2
def baseEnd_5070772 : Nat := 2603743325360539814929951

theorem tailTrace_5070772 : CollatzResearch.WordTrace tailWord_5070772 prefixEnd_5070772 2603743325360539814929951 := by
  unfold tailWord_5070772
  simp only [CollatzResearch.WordTrace]
  refine ⟨92473124392733268877711285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123297499190311025170281713 92473124392733268877711285)
  ·
    refine ⟨8669355411818743957285433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92473124392733268877711285 8669355411818743957285433)
    ·
      refine ⟨6502016558864057967964075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8669355411818743957285433 6502016558864057967964075)
      ·
        refine ⟨9753024838296086951946113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6502016558864057967964075 9753024838296086951946113)
        ·
          refine ⟨7314768628722065213959585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9753024838296086951946113 7314768628722065213959585)
          ·
            refine ⟨5486076471541548910469689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314768628722065213959585 5486076471541548910469689)
            ·
              refine ⟨4114557353656161682852267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486076471541548910469689 4114557353656161682852267)
              ·
                refine ⟨6171836030484242524278401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114557353656161682852267 6171836030484242524278401)
                ·
                  refine ⟨4628877022863181893208801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171836030484242524278401 4628877022863181893208801)
                  ·
                    refine ⟨3471657767147386419906601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4628877022863181893208801 3471657767147386419906601)
                    ·
                      refine ⟨2603743325360539814929951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471657767147386419906601 2603743325360539814929951)
                      ·
                        rfl

theorem cell23_5070772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5070772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070772 prefixEnd_5070772 := by exact prefixLift 5070772
  have htrace : WordTrace (prefixWord ++ tailWord_5070772) baseStart_5070772 baseEnd_5070772 := by
    simpa [prefixWord, tailWord_5070772, baseEnd_5070772] using wordTrace_append hprefix tailTrace_5070772
  have hstable : (prefixWord ++ tailWord_5070772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070772).length < 2 ^ (prefixWord ++ tailWord_5070772).sum := by decide
  have hdescent : baseEnd_5070772 < baseStart_5070772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070777 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 6, 2]
def baseStart_5070777 : Nat := 118140960795 + 5070777 * 2 ^ 59
def prefixEnd_5070777 : Nat := 4983230072969 + 3 ^ 40 * 5070777 * 2
def baseEnd_5070777 : Nat := 2603745892763812295367427

theorem tailTrace_5070777 : CollatzResearch.WordTrace tailWord_5070777 prefixEnd_5070777 2603745892763812295367427 := by
  unfold tailWord_5070777
  simp only [CollatzResearch.WordTrace]
  refine ⟨184946431150448423609354585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123297620766965615739569723 184946431150448423609354585)
  ·
    refine ⟨138709823362836317707015939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184946431150448423609354585 138709823362836317707015939)
    ·
      refine ⟨208064735044254476560523909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138709823362836317707015939 208064735044254476560523909)
      ·
        refine ⟨39012137820797714355098233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208064735044254476560523909 39012137820797714355098233)
        ·
          refine ⟨29259103365598285766323675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39012137820797714355098233 29259103365598285766323675)
          ·
            refine ⟨43888655048397428649485513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29259103365598285766323675 43888655048397428649485513)
            ·
              refine ⟨32916491286298071487114135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43888655048397428649485513 32916491286298071487114135)
              ·
                refine ⟨49374736929447107230671203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32916491286298071487114135 49374736929447107230671203)
                ·
                  refine ⟨74062105394170660846006805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49374736929447107230671203 74062105394170660846006805)
                  ·
                    refine ⟨3471661190351749727156569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74062105394170660846006805 3471661190351749727156569)
                    ·
                      refine ⟨2603745892763812295367427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471661190351749727156569 2603745892763812295367427)
                      ·
                        rfl

theorem cell23_5070777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_5070777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070777 prefixEnd_5070777 := by exact prefixLift 5070777
  have htrace : WordTrace (prefixWord ++ tailWord_5070777) baseStart_5070777 baseEnd_5070777 := by
    simpa [prefixWord, tailWord_5070777, baseEnd_5070777] using wordTrace_append hprefix tailTrace_5070777
  have hstable : (prefixWord ++ tailWord_5070777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070777).length < 2 ^ (prefixWord ++ tailWord_5070777).sum := by decide
  have hdescent : baseEnd_5070777 < baseStart_5070777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070812 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 5]
def baseStart_5070812 : Nat := 118140960795 + 5070812 * 2 ^ 59
def prefixEnd_5070812 : Nat := 4983230072969 + 3 ^ 40 * 5070812 * 2
def baseEnd_5070812 : Nat := 289307096065191073158863

theorem tailTrace_5070812 : CollatzResearch.WordTrace tailWord_5070812 prefixEnd_5070812 289307096065191073158863 := by
  unfold tailWord_5070812
  simp only [CollatzResearch.WordTrace]
  refine ⟨92473853852660812293439345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123298471803547749724585793 92473853852660812293439345)
  ·
    refine ⟨69355390389495609220079509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92473853852660812293439345 69355390389495609220079509)
    ·
      refine ⟨3251033924507606682191227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69355390389495609220079509 3251033924507606682191227)
      ·
        refine ⟨4876550886761410023286841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251033924507606682191227 4876550886761410023286841)
        ·
          refine ⟨3657413165071057517465131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876550886761410023286841 3657413165071057517465131)
          ·
            refine ⟨5486119747606586276197697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657413165071057517465131 5486119747606586276197697)
            ·
              refine ⟨4114589810704939707148273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486119747606586276197697 4114589810704939707148273)
              ·
                refine ⟨3085942358028704780361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114589810704939707148273 3085942358028704780361205)
                ·
                  refine ⟨289307096065191073158863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3085942358028704780361205 289307096065191073158863)
                  ·
                    rfl

theorem cell23_5070812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_5070812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070812 prefixEnd_5070812 := by exact prefixLift 5070812
  have htrace : WordTrace (prefixWord ++ tailWord_5070812) baseStart_5070812 baseEnd_5070812 := by
    simpa [prefixWord, tailWord_5070812, baseEnd_5070812] using wordTrace_append hprefix tailTrace_5070812
  have hstable : (prefixWord ++ tailWord_5070812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070812).length < 2 ^ (prefixWord ++ tailWord_5070812).sum := by decide
  have hdescent : baseEnd_5070812 < baseStart_5070812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070820 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_5070820 : Nat := 118140960795 + 5070820 * 2 ^ 59
def prefixEnd_5070820 : Nat := 4983230072969 + 3 ^ 40 * 5070820 * 2
def baseEnd_5070820 : Nat := 2603767972431955627129729

theorem tailTrace_5070820 : CollatzResearch.WordTrace tailWord_5070820 prefixEnd_5070820 2603767972431955627129729 := by
  unfold tailWord_5070820
  simp only [CollatzResearch.WordTrace]
  refine ⟨92473999744646320976584957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123298666326195094635446609 92473999744646320976584957)
  ·
    refine ⟨34677749904242370366219359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92473999744646320976584957 34677749904242370366219359)
    ·
      refine ⟨52016624856363555549329039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34677749904242370366219359 52016624856363555549329039)
      ·
        refine ⟨78024937284545333323993559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52016624856363555549329039 78024937284545333323993559)
        ·
          refine ⟨117037405926817999985990339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78024937284545333323993559 117037405926817999985990339)
          ·
            refine ⟨175556108890226999978985509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117037405926817999985990339 175556108890226999978985509)
            ·
              refine ⟨32916770416917562496059783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175556108890226999978985509 32916770416917562496059783)
              ·
                refine ⟨49375155625376343744089675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32916770416917562496059783 49375155625376343744089675)
                ·
                  refine ⟨74062733438064515616134513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49375155625376343744089675 74062733438064515616134513)
                  ·
                    refine ⟨55547050078548386712100885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74062733438064515616134513 55547050078548386712100885)
                    ·
                      refine ⟨2603767972431955627129729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55547050078548386712100885 2603767972431955627129729)
                      ·
                        rfl

theorem cell23_5070820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_5070820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070820 prefixEnd_5070820 := by exact prefixLift 5070820
  have htrace : WordTrace (prefixWord ++ tailWord_5070820) baseStart_5070820 baseEnd_5070820 := by
    simpa [prefixWord, tailWord_5070820, baseEnd_5070820] using wordTrace_append hprefix tailTrace_5070820
  have hstable : (prefixWord ++ tailWord_5070820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070820).length < 2 ^ (prefixWord ++ tailWord_5070820).sum := by decide
  have hdescent : baseEnd_5070820 < baseStart_5070820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070827 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 3]
def baseStart_5070827 : Nat := 118140960795 + 5070827 * 2 ^ 59
def prefixEnd_5070827 : Nat := 4983230072969 + 3 ^ 40 * 5070827 * 2
def baseEnd_5070827 : Nat := 2603771566796537099742197

theorem tailTrace_5070827 : CollatzResearch.WordTrace tailWord_5070827 prefixEnd_5070827 2603771566796537099742197 := by
  unfold tailWord_5070827
  simp only [CollatzResearch.WordTrace]
  refine ⟨184948254800267282148674735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123298836533511521432449823 184948254800267282148674735)
  ·
    refine ⟨277422382200400923223012103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184948254800267282148674735 277422382200400923223012103)
    ·
      refine ⟨416133573300601384834518155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277422382200400923223012103 416133573300601384834518155)
      ·
        refine ⟨624200359950902077251777233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416133573300601384834518155 624200359950902077251777233)
        ·
          refine ⟨468150269963176557938832925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624200359950902077251777233 468150269963176557938832925)
          ·
            refine ⟨175556351236191209227062347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468150269963176557938832925 175556351236191209227062347)
            ·
              refine ⟨263334526854286813840593521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175556351236191209227062347 263334526854286813840593521)
              ·
                refine ⟨197500895140715110380445141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263334526854286813840593521 197500895140715110380445141)
                ·
                  refine ⟨4628927229860510399541683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197500895140715110380445141 4628927229860510399541683)
                  ·
                    refine ⟨6943390844790765599312525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4628927229860510399541683 6943390844790765599312525)
                    ·
                      refine ⟨2603771566796537099742197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943390844790765599312525 2603771566796537099742197)
                      ·
                        rfl

theorem cell23_5070827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 3].length) (baseStart_5070827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070827 prefixEnd_5070827 := by exact prefixLift 5070827
  have htrace : WordTrace (prefixWord ++ tailWord_5070827) baseStart_5070827 baseEnd_5070827 := by
    simpa [prefixWord, tailWord_5070827, baseEnd_5070827] using wordTrace_append hprefix tailTrace_5070827
  have hstable : (prefixWord ++ tailWord_5070827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070827).length < 2 ^ (prefixWord ++ tailWord_5070827).sum := by decide
  have hdescent : baseEnd_5070827 < baseStart_5070827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070844 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_5070844 : Nat := 118140960795 + 5070844 * 2 ^ 59
def prefixEnd_5070844 : Nat := 4983230072969 + 3 ^ 40 * 5070844 * 2
def baseEnd_5070844 : Nat := 2603780295967663533229619

theorem tailTrace_5070844 : CollatzResearch.WordTrace tailWord_5070844 prefixEnd_5070844 2603780295967663533229619 := by
  unfold tailWord_5070844
  simp only [CollatzResearch.WordTrace]
  refine ⟨92474437420602847026021793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123299249894137129368029057 92474437420602847026021793)
  ·
    refine ⟨69355828065452135269516345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92474437420602847026021793 69355828065452135269516345)
    ·
      refine ⟨52016871049089101452137259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69355828065452135269516345 52016871049089101452137259)
      ·
        refine ⟨78025306573633652178205889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52016871049089101452137259 78025306573633652178205889)
        ·
          refine ⟨58518979930225239133654417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78025306573633652178205889 58518979930225239133654417)
          ·
            refine ⟨43889234947668929350240813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58518979930225239133654417 43889234947668929350240813)
            ·
              refine ⟨16458463105375848506340305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43889234947668929350240813 16458463105375848506340305)
              ·
                refine ⟨12343847329031886379755229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16458463105375848506340305 12343847329031886379755229)
                ·
                  refine ⟨4628942748386957392408211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12343847329031886379755229 4628942748386957392408211)
                  ·
                    refine ⟨6943414122580436088612317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4628942748386957392408211 6943414122580436088612317)
                    ·
                      refine ⟨2603780295967663533229619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943414122580436088612317 2603780295967663533229619)
                      ·
                        rfl

theorem cell23_5070844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_5070844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070844 prefixEnd_5070844 := by exact prefixLift 5070844
  have htrace : WordTrace (prefixWord ++ tailWord_5070844) baseStart_5070844 baseEnd_5070844 := by
    simpa [prefixWord, tailWord_5070844, baseEnd_5070844] using wordTrace_append hprefix tailTrace_5070844
  have hstable : (prefixWord ++ tailWord_5070844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070844).length < 2 ^ (prefixWord ++ tailWord_5070844).sum := by decide
  have hdescent : baseEnd_5070844 < baseStart_5070844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070868 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 6]
def baseStart_5070868 : Nat := 118140960795 + 5070868 * 2 ^ 59
def prefixEnd_5070868 : Nat := 4983230072969 + 3 ^ 40 * 5070868 * 2
def baseEnd_5070868 : Nat := 289310291055930159925501

theorem tailTrace_5070868 : CollatzResearch.WordTrace tailWord_5070868 prefixEnd_5070868 289310291055930159925501 := by
  unfold tailWord_5070868
  simp only [CollatzResearch.WordTrace]
  refine ⟨92474875096559373075458629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123299833462079164100611505 92474875096559373075458629)
  ·
    refine ⟨17339039080604882451648493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92474875096559373075458629 17339039080604882451648493)
    ·
      refine ⟨6502139655226830919368185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17339039080604882451648493 6502139655226830919368185)
      ·
        refine ⟨4876604741420123189526139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6502139655226830919368185 4876604741420123189526139)
        ·
          refine ⟨7314907112130184784289209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876604741420123189526139 7314907112130184784289209)
          ·
            refine ⟨5486180334097638588216907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314907112130184784289209 5486180334097638588216907)
            ·
              refine ⟨8229270501146457882325361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486180334097638588216907 8229270501146457882325361)
              ·
                refine ⟨6171952875859843411744021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8229270501146457882325361 6171952875859843411744021)
                ·
                  refine ⟨289310291055930159925501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6171952875859843411744021 289310291055930159925501)
                  ·
                    rfl

theorem cell23_5070868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_5070868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070868 prefixEnd_5070868 := by exact prefixLift 5070868
  have htrace : WordTrace (prefixWord ++ tailWord_5070868) baseStart_5070868 baseEnd_5070868 := by
    simpa [prefixWord, tailWord_5070868, baseEnd_5070868] using wordTrace_append hprefix tailTrace_5070868
  have hstable : (prefixWord ++ tailWord_5070868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070868).length < 2 ^ (prefixWord ++ tailWord_5070868).sum := by decide
  have hdescent : baseEnd_5070868 < baseStart_5070868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070894 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5070894 : Nat := 118140960795 + 5070894 * 2 ^ 59
def prefixEnd_5070894 : Nat := 4983230072969 + 3 ^ 40 * 5070894 * 2
def baseEnd_5070894 : Nat := 867935323333462779201463

theorem tailTrace_5070894 : CollatzResearch.WordTrace tailWord_5070894 prefixEnd_5070894 867935323333462779201463 := by
  unfold tailWord_5070894
  simp only [CollatzResearch.WordTrace]
  refine ⟨23118837311378069073920467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123300465660683035060909157 23118837311378069073920467)
  ·
    refine ⟨34678255967067103610880701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23118837311378069073920467 34678255967067103610880701)
    ·
      refine ⟨13004345987650163854080263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34678255967067103610880701 13004345987650163854080263)
      ·
        refine ⟨19506518981475245781120395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13004345987650163854080263 19506518981475245781120395)
        ·
          refine ⟨29259778472212868671680593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19506518981475245781120395 29259778472212868671680593)
          ·
            refine ⟨21944833854159651503760445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29259778472212868671680593 21944833854159651503760445)
            ·
              refine ⟨8229312695309869313910167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21944833854159651503760445 8229312695309869313910167)
              ·
                refine ⟨12343969042964803970865251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8229312695309869313910167 12343969042964803970865251)
                ·
                  refine ⟨18515953564447205956297877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12343969042964803970865251 18515953564447205956297877)
                  ·
                    refine ⟨867935323333462779201463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18515953564447205956297877 867935323333462779201463)
                    ·
                      rfl

theorem cell23_5070894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5070894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070894 prefixEnd_5070894 := by exact prefixLift 5070894
  have htrace : WordTrace (prefixWord ++ tailWord_5070894) baseStart_5070894 baseEnd_5070894 := by
    simpa [prefixWord, tailWord_5070894, baseEnd_5070894] using wordTrace_append hprefix tailTrace_5070894
  have hstable : (prefixWord ++ tailWord_5070894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070894).length < 2 ^ (prefixWord ++ tailWord_5070894).sum := by decide
  have hdescent : baseEnd_5070894 < baseStart_5070894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070897 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_5070897 : Nat := 118140960795 + 5070897 * 2 ^ 59
def prefixEnd_5070897 : Nat := 4983230072969 + 3 ^ 40 * 5070897 * 2
def baseEnd_5070897 : Nat := 2603807510442351825866875

theorem tailTrace_5070897 : CollatzResearch.WordTrace tailWord_5070897 prefixEnd_5070897 2603807510442351825866875 := by
  unfold tailWord_5070897
  simp only [CollatzResearch.WordTrace]
  refine ⟨184950807910013684103722945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123300538606675789402481963 184950807910013684103722945)
  ·
    refine ⟨138713105932510263077792209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184950807910013684103722945 138713105932510263077792209)
    ·
      refine ⟨104034829449382697308344157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138713105932510263077792209 104034829449382697308344157)
      ·
        refine ⟨39013061043518511490629059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104034829449382697308344157 39013061043518511490629059)
        ·
          refine ⟨58519591565277767235943589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39013061043518511490629059 58519591565277767235943589)
          ·
            refine ⟨10972423418489581356739423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58519591565277767235943589 10972423418489581356739423)
            ·
              refine ⟨16458635127734372035109135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10972423418489581356739423 16458635127734372035109135)
              ·
                refine ⟨24687952691601558052663703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16458635127734372035109135 24687952691601558052663703)
                ·
                  refine ⟨37031929037402337078995555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24687952691601558052663703 37031929037402337078995555)
                  ·
                    refine ⟨55547893556103505618493333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37031929037402337078995555 55547893556103505618493333)
                    ·
                      refine ⟨2603807510442351825866875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55547893556103505618493333 2603807510442351825866875)
                      ·
                        rfl

theorem cell23_5070897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_5070897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070897 prefixEnd_5070897 := by exact prefixLift 5070897
  have htrace : WordTrace (prefixWord ++ tailWord_5070897) baseStart_5070897 baseEnd_5070897 := by
    simpa [prefixWord, tailWord_5070897, baseEnd_5070897] using wordTrace_append hprefix tailTrace_5070897
  have hstable : (prefixWord ++ tailWord_5070897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070897).length < 2 ^ (prefixWord ++ tailWord_5070897).sum := by decide
  have hdescent : baseEnd_5070897 < baseStart_5070897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070901 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_5070901 : Nat := 118140960795 + 5070901 * 2 ^ 59
def prefixEnd_5070901 : Nat := 4983230072969 + 3 ^ 40 * 5070901 * 2
def baseEnd_5070901 : Nat := 2603809564364969810216857

theorem tailTrace_5070901 : CollatzResearch.WordTrace tailWord_5070901 prefixEnd_5070901 2603809564364969810216857 := by
  unfold tailWord_5070901
  simp only [CollatzResearch.WordTrace]
  refine ⟨184950953801999192786868557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123300635867999461857912371 184950953801999192786868557)
  ·
    refine ⟨69356607675749697295075709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184950953801999192786868557 69356607675749697295075709)
    ·
      refine ⟨26008727878406136485653391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69356607675749697295075709 26008727878406136485653391)
      ·
        refine ⟨39013091817609204728480087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26008727878406136485653391 39013091817609204728480087)
        ·
          refine ⟨58519637726413807092720131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39013091817609204728480087 58519637726413807092720131)
          ·
            refine ⟨87779456589620710639080197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58519637726413807092720131 87779456589620710639080197)
            ·
              refine ⟨16458648110553883244827537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87779456589620710639080197 16458648110553883244827537)
              ·
                refine ⟨12343986082915412433620653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16458648110553883244827537 12343986082915412433620653)
                ·
                  refine ⟨4628994781093279662607745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12343986082915412433620653 4628994781093279662607745)
                  ·
                    refine ⟨3471746085819959746955809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4628994781093279662607745 3471746085819959746955809)
                    ·
                      refine ⟨2603809564364969810216857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471746085819959746955809 2603809564364969810216857)
                      ·
                        rfl

theorem cell23_5070901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_5070901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070901 prefixEnd_5070901 := by exact prefixLift 5070901
  have htrace : WordTrace (prefixWord ++ tailWord_5070901) baseStart_5070901 baseEnd_5070901 := by
    simpa [prefixWord, tailWord_5070901, baseEnd_5070901] using wordTrace_append hprefix tailTrace_5070901
  have hstable : (prefixWord ++ tailWord_5070901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070901).length < 2 ^ (prefixWord ++ tailWord_5070901).sum := by decide
  have hdescent : baseEnd_5070901 < baseStart_5070901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070917 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_5070917 : Nat := 118140960795 + 5070917 * 2 ^ 59
def prefixEnd_5070917 : Nat := 4983230072969 + 3 ^ 40 * 5070917 * 2
def baseEnd_5070917 : Nat := 2603817780055441747616783

theorem tailTrace_5070917 : CollatzResearch.WordTrace tailWord_5070917 prefixEnd_5070917 2603817780055441747616783 := by
  unfold tailWord_5070917
  simp only [CollatzResearch.WordTrace]
  refine ⟨184951537369941227519451005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123301024913294151679634003 184951537369941227519451005)
  ·
    refine ⟨69356826513727960319794127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184951537369941227519451005 69356826513727960319794127)
    ·
      refine ⟨104035239770591940479691191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69356826513727960319794127 104035239770591940479691191)
      ·
        refine ⟨156052859655887910719536787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104035239770591940479691191 156052859655887910719536787)
        ·
          refine ⟨234079289483831866079305181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156052859655887910719536787 234079289483831866079305181)
          ·
            refine ⟨87779733556436949779739443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234079289483831866079305181 87779733556436949779739443)
            ·
              refine ⟨131669600334655424669609165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87779733556436949779739443 131669600334655424669609165)
              ·
                refine ⟨49376100125495784251103437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131669600334655424669609165 49376100125495784251103437)
                ·
                  refine ⟨18516037547060919094163789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49376100125495784251103437 18516037547060919094163789)
                  ·
                    refine ⟨6943514080147844660311421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18516037547060919094163789 6943514080147844660311421)
                    ·
                      refine ⟨2603817780055441747616783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943514080147844660311421 2603817780055441747616783)
                      ·
                        rfl

theorem cell23_5070917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_5070917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070917 prefixEnd_5070917 := by exact prefixLift 5070917
  have htrace : WordTrace (prefixWord ++ tailWord_5070917) baseStart_5070917 baseEnd_5070917 := by
    simpa [prefixWord, tailWord_5070917, baseEnd_5070917] using wordTrace_append hprefix tailTrace_5070917
  have hstable : (prefixWord ++ tailWord_5070917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070917).length < 2 ^ (prefixWord ++ tailWord_5070917).sum := by decide
  have hdescent : baseEnd_5070917 < baseStart_5070917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070951 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_5070951 : Nat := 118140960795 + 5070951 * 2 ^ 59
def prefixEnd_5070951 : Nat := 4983230072969 + 3 ^ 40 * 5070951 * 2
def baseEnd_5070951 : Nat := 2603835238397694614591627

theorem tailTrace_5070951 : CollatzResearch.WordTrace tailWord_5070951 prefixEnd_5070951 2603835238397694614591627 := by
  unfold tailWord_5070951
  simp only [CollatzResearch.WordTrace]
  refine ⟨184952777451818051326188707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123301851634545367550792471 184952777451818051326188707)
  ·
    refine ⟨277429166177727076989283061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184952777451818051326188707 277429166177727076989283061)
    ·
      refine ⟨26008984329161913467745287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277429166177727076989283061 26008984329161913467745287)
      ·
        refine ⟨39013476493742870201617931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26008984329161913467745287 39013476493742870201617931)
        ·
          refine ⟨58520214740614305302426897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39013476493742870201617931 58520214740614305302426897)
          ·
            refine ⟨43890161055460728976820173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58520214740614305302426897 43890161055460728976820173)
            ·
              refine ⟨16458810395797773366307565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43890161055460728976820173 16458810395797773366307565)
              ·
                refine ⟨6172053898424165012365337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16458810395797773366307565 6172053898424165012365337)
                ·
                  refine ⟨4629040423818123759274003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172053898424165012365337 4629040423818123759274003)
                  ·
                    refine ⟨6943560635727185638911005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4629040423818123759274003 6943560635727185638911005)
                    ·
                      refine ⟨2603835238397694614591627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943560635727185638911005 2603835238397694614591627)
                      ·
                        rfl

theorem cell23_5070951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_5070951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070951 prefixEnd_5070951 := by exact prefixLift 5070951
  have htrace : WordTrace (prefixWord ++ tailWord_5070951) baseStart_5070951 baseEnd_5070951 := by
    simpa [prefixWord, tailWord_5070951, baseEnd_5070951] using wordTrace_append hprefix tailTrace_5070951
  have hstable : (prefixWord ++ tailWord_5070951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070951).length < 2 ^ (prefixWord ++ tailWord_5070951).sum := by decide
  have hdescent : baseEnd_5070951 < baseStart_5070951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070994 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_5070994 : Nat := 118140960795 + 5070994 * 2 ^ 59
def prefixEnd_5070994 : Nat := 4983230072969 + 3 ^ 40 * 5070994 * 2
def baseEnd_5070994 : Nat := 2603857318065837946353929

theorem tailTrace_5070994 : CollatzResearch.WordTrace tailWord_5070994 prefixEnd_5070994 2603857318065837946353929 := by
  unfold tailWord_5070994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46238586447665567417501009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123302897193774846446669357 46238586447665567417501009)
  ·
    refine ⟨34678939835749175563125757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46238586447665567417501009 34678939835749175563125757)
    ·
      refine ⟨13004602438405940836172159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34678939835749175563125757 13004602438405940836172159)
      ·
        refine ⟨19506903657608911254258239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13004602438405940836172159 19506903657608911254258239)
        ·
          refine ⟨29260355486413366881387359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19506903657608911254258239 29260355486413366881387359)
          ·
            refine ⟨43890533229620050322081039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29260355486413366881387359 43890533229620050322081039)
            ·
              refine ⟨65835799844430075483121559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43890533229620050322081039 65835799844430075483121559)
              ·
                refine ⟨98753699766645113224682339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65835799844430075483121559 98753699766645113224682339)
                ·
                  refine ⟨148130549649967669837023509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98753699766645113224682339 148130549649967669837023509)
                  ·
                    refine ⟨6943619514842234523610477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148130549649967669837023509 6943619514842234523610477)
                    ·
                      refine ⟨2603857318065837946353929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943619514842234523610477 2603857318065837946353929)
                      ·
                        rfl

theorem cell23_5070994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_5070994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070994 prefixEnd_5070994 := by exact prefixLift 5070994
  have htrace : WordTrace (prefixWord ++ tailWord_5070994) baseStart_5070994 baseEnd_5070994 := by
    simpa [prefixWord, tailWord_5070994, baseEnd_5070994] using wordTrace_append hprefix tailTrace_5070994
  have hstable : (prefixWord ++ tailWord_5070994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070994).length < 2 ^ (prefixWord ++ tailWord_5070994).sum := by decide
  have hdescent : baseEnd_5070994 < baseStart_5070994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5070997 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 7]
def baseStart_5070997 : Nat := 118140960795 + 5070997 * 2 ^ 59
def prefixEnd_5070997 : Nat := 4983230072969 + 3 ^ 40 * 5070997 * 2
def baseEnd_5070997 : Nat := 289317650945311270512935

theorem tailTrace_5070997 : CollatzResearch.WordTrace tailWord_5070997 prefixEnd_5070997 289317650945311270512935 := by
  unfold tailWord_5070997
  simp only [CollatzResearch.WordTrace]
  refine ⟨184954455209651401182363245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123302970139767600788242163 184954455209651401182363245)
  ·
    refine ⟨69357920703619275443386217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184954455209651401182363245 69357920703619275443386217)
    ·
      refine ⟨52018440527714456582539663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69357920703619275443386217 52018440527714456582539663)
      ·
        refine ⟨78027660791571684873809495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52018440527714456582539663 78027660791571684873809495)
        ·
          refine ⟨117041491187357527310714243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78027660791571684873809495 117041491187357527310714243)
          ·
            refine ⟨175562236781036290966071365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117041491187357527310714243 175562236781036290966071365)
            ·
              refine ⟨32917919396444304556138381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175562236781036290966071365 32917919396444304556138381)
              ·
                refine ⟨12344219773666614208551893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32917919396444304556138381 12344219773666614208551893)
                ·
                  refine ⟨289317650945311270512935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12344219773666614208551893 289317650945311270512935)
                  ·
                    rfl

theorem cell23_5070997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_5070997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5070997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5070997 prefixEnd_5070997 := by exact prefixLift 5070997
  have htrace : WordTrace (prefixWord ++ tailWord_5070997) baseStart_5070997 baseEnd_5070997 := by
    simpa [prefixWord, tailWord_5070997, baseEnd_5070997] using wordTrace_append hprefix tailTrace_5070997
  have hstable : (prefixWord ++ tailWord_5070997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5070997).length < 2 ^ (prefixWord ++ tailWord_5070997).sum := by decide
  have hdescent : baseEnd_5070997 < baseStart_5070997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5070997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071004 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5071004 : Nat := 118140960795 + 5071004 * 2 ^ 59
def prefixEnd_5071004 : Nat := 4983230072969 + 3 ^ 40 * 5071004 * 2
def baseEnd_5071004 : Nat := 2603862452872382907228883

theorem tailTrace_5071004 : CollatzResearch.WordTrace tailWord_5071004 prefixEnd_5071004 2603862452872382907228883 := by
  unfold tailWord_5071004
  simp only [CollatzResearch.WordTrace]
  refine ⟨92477355260313020688934033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123303140347084027585245377 92477355260313020688934033)
  ·
    refine ⟨69358016445234765516700525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92477355260313020688934033 69358016445234765516700525)
    ·
      refine ⟨26009256166963037068762697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69358016445234765516700525 26009256166963037068762697)
      ·
        refine ⟨19506942125222277801572023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26009256166963037068762697 19506942125222277801572023)
        ·
          refine ⟨29260413187833416702358035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19506942125222277801572023 29260413187833416702358035)
          ·
            refine ⟨43890619781750125053537053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29260413187833416702358035 43890619781750125053537053)
            ·
              refine ⟨16458982418156296895076395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43890619781750125053537053 16458982418156296895076395)
              ·
                refine ⟨24688473627234445342614593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16458982418156296895076395 24688473627234445342614593)
                ·
                  refine ⟨18516355220425834006960945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24688473627234445342614593 18516355220425834006960945)
                  ·
                    refine ⟨13887266415319375505220709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18516355220425834006960945 13887266415319375505220709)
                    ·
                      refine ⟨2603862452872382907228883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13887266415319375505220709 2603862452872382907228883)
                      ·
                        rfl

theorem cell23_5071004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5071004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071004 prefixEnd_5071004 := by exact prefixLift 5071004
  have htrace : WordTrace (prefixWord ++ tailWord_5071004) baseStart_5071004 baseEnd_5071004 := by
    simpa [prefixWord, tailWord_5071004, baseEnd_5071004] using wordTrace_append hprefix tailTrace_5071004
  have hstable : (prefixWord ++ tailWord_5071004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071004).length < 2 ^ (prefixWord ++ tailWord_5071004).sum := by decide
  have hdescent : baseEnd_5071004 < baseStart_5071004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071008 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2]
def baseStart_5071008 : Nat := 118140960795 + 5071008 * 2 ^ 59
def prefixEnd_5071008 : Nat := 4983230072969 + 3 ^ 40 * 5071008 * 2
def baseEnd_5071008 : Nat := 2603864506795000891578865

theorem tailTrace_5071008 : CollatzResearch.WordTrace tailWord_5071008 prefixEnd_5071008 2603864506795000891578865 := by
  unfold tailWord_5071008
  simp only [CollatzResearch.WordTrace]
  refine ⟨92477428206305775030506839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123303237608407700040675785 92477428206305775030506839)
  ·
    refine ⟨138716142309458662545760259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92477428206305775030506839 138716142309458662545760259)
    ·
      refine ⟨208074213464187993818640389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138716142309458662545760259 208074213464187993818640389)
      ·
        refine ⟨39013915024535248840995073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208074213464187993818640389 39013915024535248840995073)
        ·
          refine ⟨29260436268401436630746305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39013915024535248840995073 29260436268401436630746305)
          ·
            refine ⟨21945327201301077473059729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29260436268401436630746305 21945327201301077473059729)
            ·
              refine ⟨16458995400975808104794797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21945327201301077473059729 16458995400975808104794797)
              ·
                refine ⟨6172123275365928039298049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16458995400975808104794797 6172123275365928039298049)
                ·
                  refine ⟨4629092456524446029473537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172123275365928039298049 4629092456524446029473537)
                  ·
                    refine ⟨3471819342393334522105153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629092456524446029473537 3471819342393334522105153)
                    ·
                      refine ⟨2603864506795000891578865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471819342393334522105153 2603864506795000891578865)
                      ·
                        rfl

theorem cell23_5071008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_5071008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071008 prefixEnd_5071008 := by exact prefixLift 5071008
  have htrace : WordTrace (prefixWord ++ tailWord_5071008) baseStart_5071008 baseEnd_5071008 := by
    simpa [prefixWord, tailWord_5071008, baseEnd_5071008] using wordTrace_append hprefix tailTrace_5071008
  have hstable : (prefixWord ++ tailWord_5071008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071008).length < 2 ^ (prefixWord ++ tailWord_5071008).sum := by decide
  have hdescent : baseEnd_5071008 < baseStart_5071008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071029 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5071029 : Nat := 118140960795 + 5071029 * 2 ^ 59
def prefixEnd_5071029 : Nat := 4983230072969 + 3 ^ 40 * 5071029 * 2
def baseEnd_5071029 : Nat := 2603875289888745309416269

theorem tailTrace_5071029 : CollatzResearch.WordTrace tailWord_5071029 prefixEnd_5071029 2603875289888745309416269 := by
  unfold tailWord_5071029
  simp only [CollatzResearch.WordTrace]
  refine ⟨184955622345535470647528141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123303748230356980431685427 184955622345535470647528141)
  ·
    refine ⟨69358358379575801492823053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184955622345535470647528141 69358358379575801492823053)
    ·
      refine ⟨26009384392340925559808645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69358358379575801492823053 26009384392340925559808645)
      ·
        refine ⟨4876759573563923542464121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26009384392340925559808645 4876759573563923542464121)
        ·
          refine ⟨3657569680172942656848091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876759573563923542464121 3657569680172942656848091)
          ·
            refine ⟨5486354520259413985272137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657569680172942656848091 5486354520259413985272137)
            ·
              refine ⟨4114765890194560488954103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486354520259413985272137 4114765890194560488954103)
              ·
                refine ⟨6172148835291840733431155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114765890194560488954103 6172148835291840733431155)
                ·
                  refine ⟨9258223252937761100146733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6172148835291840733431155 9258223252937761100146733)
                  ·
                    refine ⟨3471833719851660412555025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9258223252937761100146733 3471833719851660412555025)
                    ·
                      refine ⟨2603875289888745309416269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471833719851660412555025 2603875289888745309416269)
                      ·
                        rfl

theorem cell23_5071029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5071029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071029 prefixEnd_5071029 := by exact prefixLift 5071029
  have htrace : WordTrace (prefixWord ++ tailWord_5071029) baseStart_5071029 baseEnd_5071029 := by
    simpa [prefixWord, tailWord_5071029, baseEnd_5071029] using wordTrace_append hprefix tailTrace_5071029
  have hstable : (prefixWord ++ tailWord_5071029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071029).length < 2 ^ (prefixWord ++ tailWord_5071029).sum := by decide
  have hdescent : baseEnd_5071029 < baseStart_5071029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071031 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 5]
def baseStart_5071031 : Nat := 118140960795 + 5071031 * 2 ^ 59
def prefixEnd_5071031 : Nat := 4983230072969 + 3 ^ 40 * 5071031 * 2
def baseEnd_5071031 : Nat := 289319590761117144621251

theorem tailTrace_5071031 : CollatzResearch.WordTrace tailWord_5071031 prefixEnd_5071031 289319590761117144621251 := by
  unfold tailWord_5071031
  simp only [CollatzResearch.WordTrace]
  refine ⟨184955695291528224989100947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123303796861018816659400631 184955695291528224989100947)
  ·
    refine ⟨277433542937292337483651421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184955695291528224989100947 277433542937292337483651421)
    ·
      refine ⟨104037578601484626556369283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277433542937292337483651421 104037578601484626556369283)
      ·
        refine ⟨156056367902226939834553925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104037578601484626556369283 156056367902226939834553925)
        ·
          refine ⟨29260568981667551218978861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156056367902226939834553925 29260568981667551218978861)
          ·
            refine ⟨10972713368125331707117073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29260568981667551218978861 10972713368125331707117073)
            ·
              refine ⟨8229535026093998780337805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10972713368125331707117073 8229535026093998780337805)
              ·
                refine ⟨3086075634785249542626677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8229535026093998780337805 3086075634785249542626677)
                ·
                  refine ⟨289319590761117144621251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3086075634785249542626677 289319590761117144621251)
                  ·
                    rfl

theorem cell23_5071031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 5].length) (baseStart_5071031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071031 prefixEnd_5071031 := by exact prefixLift 5071031
  have htrace : WordTrace (prefixWord ++ tailWord_5071031) baseStart_5071031 baseEnd_5071031 := by
    simpa [prefixWord, tailWord_5071031, baseEnd_5071031] using wordTrace_append hprefix tailTrace_5071031
  have hstable : (prefixWord ++ tailWord_5071031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071031).length < 2 ^ (prefixWord ++ tailWord_5071031).sum := by decide
  have hdescent : baseEnd_5071031 < baseStart_5071031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071042 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5071042 : Nat := 118140960795 + 5071042 * 2 ^ 59
def prefixEnd_5071042 : Nat := 4983230072969 + 3 ^ 40 * 5071042 * 2
def baseEnd_5071042 : Nat := 2603881965137253758553709

theorem tailTrace_5071042 : CollatzResearch.WordTrace tailWord_5071042 prefixEnd_5071042 2603881965137253758553709 := by
  unfold tailWord_5071042
  simp only [CollatzResearch.WordTrace]
  refine ⟨46239024123622093466937845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123304064329658915911834253 46239024123622093466937845)
  ·
    refine ⟨4334908511589571262525423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46239024123622093466937845 4334908511589571262525423)
    ·
      refine ⟨6502362767384356893788135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4334908511589571262525423 6502362767384356893788135)
      ·
        refine ⟨9753544151076535340682203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6502362767384356893788135 9753544151076535340682203)
        ·
          refine ⟨14630316226614803011023305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9753544151076535340682203 14630316226614803011023305)
          ·
            refine ⟨10972737169961102258267479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14630316226614803011023305 10972737169961102258267479)
            ·
              refine ⟨16459105754941653387401219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10972737169961102258267479 16459105754941653387401219)
              ·
                refine ⟨24688658632412480081101829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16459105754941653387401219 24688658632412480081101829)
                ·
                  refine ⟨4629123493577340015206593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24688658632412480081101829 4629123493577340015206593)
                  ·
                    refine ⟨3471842620183005011404945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629123493577340015206593 3471842620183005011404945)
                    ·
                      refine ⟨2603881965137253758553709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3471842620183005011404945 2603881965137253758553709)
                      ·
                        rfl

theorem cell23_5071042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5071042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071042 prefixEnd_5071042 := by exact prefixLift 5071042
  have htrace : WordTrace (prefixWord ++ tailWord_5071042) baseStart_5071042 baseEnd_5071042 := by
    simpa [prefixWord, tailWord_5071042, baseEnd_5071042] using wordTrace_append hprefix tailTrace_5071042
  have hstable : (prefixWord ++ tailWord_5071042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071042).length < 2 ^ (prefixWord ++ tailWord_5071042).sum := by decide
  have hdescent : baseEnd_5071042 < baseStart_5071042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071064 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5071064 : Nat := 118140960795 + 5071064 * 2 ^ 59
def prefixEnd_5071064 : Nat := 4983230072969 + 3 ^ 40 * 5071064 * 2
def baseEnd_5071064 : Nat := 2603893261711652672478607

theorem tailTrace_5071064 : CollatzResearch.WordTrace tailWord_5071064 prefixEnd_5071064 2603893261711652672478607 := by
  unfold tailWord_5071064
  simp only [CollatzResearch.WordTrace]
  refine ⟨92478449450204335812526123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123304599266939114416701497 92478449450204335812526123)
  ·
    refine ⟨138717674175306503718789185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92478449450204335812526123 138717674175306503718789185)
    ·
      refine ⟨104038255631479877789091889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138717674175306503718789185 104038255631479877789091889)
      ·
        refine ⟨78028691723609908341818917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104038255631479877789091889 78028691723609908341818917)
        ·
          refine ⟨14630379698176857814091047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78028691723609908341818917 14630379698176857814091047)
          ·
            refine ⟨21945569547265286721136571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14630379698176857814091047 21945569547265286721136571)
            ·
              refine ⟨32918354320897930081704857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21945569547265286721136571 32918354320897930081704857)
              ·
                refine ⟨24688765740673447561278643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32918354320897930081704857 24688765740673447561278643)
                ·
                  refine ⟨37033148611010171341917965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24688765740673447561278643 37033148611010171341917965)
                  ·
                    refine ⟨13887430729128814253219237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37033148611010171341917965 13887430729128814253219237)
                    ·
                      refine ⟨2603893261711652672478607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13887430729128814253219237 2603893261711652672478607)
                      ·
                        rfl

theorem cell23_5071064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5071064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071064 prefixEnd_5071064 := by exact prefixLift 5071064
  have htrace : WordTrace (prefixWord ++ tailWord_5071064) baseStart_5071064 baseEnd_5071064 := by
    simpa [prefixWord, tailWord_5071064, baseEnd_5071064] using wordTrace_append hprefix tailTrace_5071064
  have hstable : (prefixWord ++ tailWord_5071064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071064).length < 2 ^ (prefixWord ++ tailWord_5071064).sum := by decide
  have hdescent : baseEnd_5071064 < baseStart_5071064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071084 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_5071084 : Nat := 118140960795 + 5071084 * 2 ^ 59
def prefixEnd_5071084 : Nat := 4983230072969 + 3 ^ 40 * 5071084 * 2
def baseEnd_5071084 : Nat := 2603903531324742594228515

theorem tailTrace_5071084 : CollatzResearch.WordTrace tailWord_5071084 prefixEnd_5071084 2603903531324742594228515 := by
  unfold tailWord_5071084
  simp only [CollatzResearch.WordTrace]
  refine ⟨92478814180168107520390153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123305085573557476693853537 92478814180168107520390153)
  ·
    refine ⟨69359110635126080640292615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92478814180168107520390153 69359110635126080640292615)
    ·
      refine ⟨104038665952689120960438923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69359110635126080640292615 104038665952689120960438923)
      ·
        refine ⟨156057998929033681440658385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104038665952689120960438923 156057998929033681440658385)
        ·
          refine ⟨117043499196775261080493789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156057998929033681440658385 117043499196775261080493789)
          ·
            refine ⟨43891312198790722905185171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117043499196775261080493789 43891312198790722905185171)
            ·
              refine ⟨65836968298186084357777757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43891312198790722905185171 65836968298186084357777757)
              ·
                refine ⟨24688863111819781634166659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65836968298186084357777757 24688863111819781634166659)
                ·
                  refine ⟨37033294667729672451249989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24688863111819781634166659 37033294667729672451249989)
                  ·
                    refine ⟨6943742750199313584609373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37033294667729672451249989 6943742750199313584609373)
                    ·
                      refine ⟨2603903531324742594228515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943742750199313584609373 2603903531324742594228515)
                      ·
                        rfl

theorem cell23_5071084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_5071084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071084 prefixEnd_5071084 := by exact prefixLift 5071084
  have htrace : WordTrace (prefixWord ++ tailWord_5071084) baseStart_5071084 baseEnd_5071084 := by
    simpa [prefixWord, tailWord_5071084, baseEnd_5071084] using wordTrace_append hprefix tailTrace_5071084
  have hstable : (prefixWord ++ tailWord_5071084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071084).length < 2 ^ (prefixWord ++ tailWord_5071084).sum := by decide
  have hdescent : baseEnd_5071084 < baseStart_5071084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071094 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5071094 : Nat := 118140960795 + 5071094 * 2 ^ 59
def prefixEnd_5071094 : Nat := 4983230072969 + 3 ^ 40 * 5071094 * 2
def baseEnd_5071094 : Nat := 2603908666131287555103469

theorem tailTrace_5071094 : CollatzResearch.WordTrace tailWord_5071094 prefixEnd_5071094 2603908666131287555103469 := by
  unfold tailWord_5071094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11559874568143749171790271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123305328726866657832429557 11559874568143749171790271)
  ·
    refine ⟨17339811852215623757685407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11559874568143749171790271 17339811852215623757685407)
    ·
      refine ⟨26009717778323435636528111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17339811852215623757685407 26009717778323435636528111)
      ·
        refine ⟨39014576667485153454792167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26009717778323435636528111 39014576667485153454792167)
        ·
          refine ⟨58521865001227730182188251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39014576667485153454792167 58521865001227730182188251)
          ·
            refine ⟨87782797501841595273282377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58521865001227730182188251 87782797501841595273282377)
            ·
              refine ⟨65837098126381196454961783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87782797501841595273282377 65837098126381196454961783)
              ·
                refine ⟨98755647189571794682442675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65837098126381196454961783 98755647189571794682442675)
                ·
                  refine ⟨148133470784357692023664013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98755647189571794682442675 148133470784357692023664013)
                  ·
                    refine ⟨55550051544134134508874005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148133470784357692023664013 55550051544134134508874005)
                    ·
                      refine ⟨2603908666131287555103469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55550051544134134508874005 2603908666131287555103469)
                      ·
                        rfl

theorem cell23_5071094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5071094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071094 prefixEnd_5071094 := by exact prefixLift 5071094
  have htrace : WordTrace (prefixWord ++ tailWord_5071094) baseStart_5071094 baseEnd_5071094 := by
    simpa [prefixWord, tailWord_5071094, baseEnd_5071094] using wordTrace_append hprefix tailTrace_5071094
  have hstable : (prefixWord ++ tailWord_5071094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071094).length < 2 ^ (prefixWord ++ tailWord_5071094).sum := by decide
  have hdescent : baseEnd_5071094 < baseStart_5071094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071121 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 6]
def baseStart_5071121 : Nat := 118140960795 + 5071121 * 2 ^ 59
def prefixEnd_5071121 : Nat := 4983230072969 + 3 ^ 40 * 5071121 * 2
def baseEnd_5071121 : Nat := 289324725567662105496205

theorem tailTrace_5071121 : CollatzResearch.WordTrace tailWord_5071121 prefixEnd_5071121 289324725567662105496205 := by
  unfold tailWord_5071121
  simp only [CollatzResearch.WordTrace]
  refine ⟨184958977861202170359877217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123305985240801446906584811 184958977861202170359877217)
  ·
    refine ⟨138719233395901627769907913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184958977861202170359877217 138719233395901627769907913)
    ·
      refine ⟨104039425046926220827430935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138719233395901627769907913 104039425046926220827430935)
      ·
        refine ⟨156059137570389331241146403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104039425046926220827430935 156059137570389331241146403)
        ·
          refine ⟨234088706355583996861719605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156059137570389331241146403 234088706355583996861719605)
          ·
            refine ⟨21945816220835999705786213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234088706355583996861719605 21945816220835999705786213)
            ·
              refine ⟨4114840541406749944834915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21945816220835999705786213 4114840541406749944834915)
              ·
                refine ⟨6172260812110124917252373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114840541406749944834915 6172260812110124917252373)
                ·
                  refine ⟨289324725567662105496205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6172260812110124917252373 289324725567662105496205)
                  ·
                    rfl

theorem cell23_5071121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 6].length) (baseStart_5071121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071121 prefixEnd_5071121 := by exact prefixLift 5071121
  have htrace : WordTrace (prefixWord ++ tailWord_5071121) baseStart_5071121 baseEnd_5071121 := by
    simpa [prefixWord, tailWord_5071121, baseEnd_5071121] using wordTrace_append hprefix tailTrace_5071121
  have hstable : (prefixWord ++ tailWord_5071121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071121).length < 2 ^ (prefixWord ++ tailWord_5071121).sum := by decide
  have hdescent : baseEnd_5071121 < baseStart_5071121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071131 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 3]
def baseStart_5071131 : Nat := 118140960795 + 5071131 * 2 ^ 59
def prefixEnd_5071131 : Nat := 4983230072969 + 3 ^ 40 * 5071131 * 2
def baseEnd_5071131 : Nat := 2603927664915503910340799

theorem tailTrace_5071131 : CollatzResearch.WordTrace tailWord_5071131 prefixEnd_5071131 2603927664915503910340799 := by
  unfold tailWord_5071131
  simp only [CollatzResearch.WordTrace]
  refine ⟨184959342591165942067741247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123306228394110628045160831 184959342591165942067741247)
  ·
    refine ⟨277439013886748913101611871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184959342591165942067741247 277439013886748913101611871)
    ·
      refine ⟨416158520830123369652417807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277439013886748913101611871 416158520830123369652417807)
      ·
        refine ⟨624237781245185054478626711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416158520830123369652417807 624237781245185054478626711)
        ·
          refine ⟨936356671867777581717940067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624237781245185054478626711 936356671867777581717940067)
          ·
            refine ⟨1404535007801666372576910101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936356671867777581717940067 1404535007801666372576910101)
            ·
              refine ⟨65837578490703111214542661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1404535007801666372576910101 65837578490703111214542661)
              ·
                refine ⟨12344545967006833352726749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65837578490703111214542661 12344545967006833352726749)
                ·
                  refine ⟨4629204737627562507272531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12344545967006833352726749 4629204737627562507272531)
                  ·
                    refine ⟨6943807106441343760908797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4629204737627562507272531 6943807106441343760908797)
                    ·
                      refine ⟨2603927664915503910340799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943807106441343760908797 2603927664915503910340799)
                      ·
                        rfl

theorem cell23_5071131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 1, 3].length) (baseStart_5071131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071131 prefixEnd_5071131 := by exact prefixLift 5071131
  have htrace : WordTrace (prefixWord ++ tailWord_5071131) baseStart_5071131 baseEnd_5071131 := by
    simpa [prefixWord, tailWord_5071131, baseEnd_5071131] using wordTrace_append hprefix tailTrace_5071131
  have hstable : (prefixWord ++ tailWord_5071131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071131).length < 2 ^ (prefixWord ++ tailWord_5071131).sum := by decide
  have hdescent : baseEnd_5071131 < baseStart_5071131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071164 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_5071164 : Nat := 118140960795 + 5071164 * 2 ^ 59
def prefixEnd_5071164 : Nat := 4983230072969 + 3 ^ 40 * 5071164 * 2
def baseEnd_5071164 : Nat := 867981536592367427076049

theorem tailTrace_5071164 : CollatzResearch.WordTrace tailWord_5071164 prefixEnd_5071164 867981536592367427076049 := by
  unfold tailWord_5071164
  simp only [CollatzResearch.WordTrace]
  refine ⟨92480273100023194351846273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123307030800030925802461697 92480273100023194351846273)
  ·
    refine ⟨69360204825017395763884705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92480273100023194351846273 69360204825017395763884705)
    ·
      refine ⟨52020153618763046822913529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69360204825017395763884705 52020153618763046822913529)
      ·
        refine ⟨39015115214072285117185147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52020153618763046822913529 39015115214072285117185147)
        ·
          refine ⟨58522672821108427675777721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39015115214072285117185147 58522672821108427675777721)
          ·
            refine ⟨43892004615831320756833291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58522672821108427675777721 43892004615831320756833291)
            ·
              refine ⟨65838006923746981135249937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43892004615831320756833291 65838006923746981135249937)
              ·
                refine ⟨49378505192810235851437453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65838006923746981135249937 49378505192810235851437453)
                ·
                  refine ⟨18516939447303838444289045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49378505192810235851437453 18516939447303838444289045)
                  ·
                    refine ⟨867981536592367427076049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18516939447303838444289045 867981536592367427076049)
                    ·
                      rfl

theorem cell23_5071164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_5071164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071164 prefixEnd_5071164 := by exact prefixLift 5071164
  have htrace : WordTrace (prefixWord ++ tailWord_5071164) baseStart_5071164 baseEnd_5071164 := by
    simpa [prefixWord, tailWord_5071164, baseEnd_5071164] using wordTrace_append hprefix tailTrace_5071164
  have hstable : (prefixWord ++ tailWord_5071164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071164).length < 2 ^ (prefixWord ++ tailWord_5071164).sum := by decide
  have hdescent : baseEnd_5071164 < baseStart_5071164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071191 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_5071191 : Nat := 118140960795 + 5071191 * 2 ^ 59
def prefixEnd_5071191 : Nat := 4983230072969 + 3 ^ 40 * 5071191 * 2
def baseEnd_5071191 : Nat := 2603958473754773675590523

theorem tailTrace_5071191 : CollatzResearch.WordTrace tailWord_5071191 prefixEnd_5071191 2603958473754773675590523 := by
  unfold tailWord_5071191
  simp only [CollatzResearch.WordTrace]
  refine ⟨184961530970948572314925427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123307687313965714876616951 184961530970948572314925427)
  ·
    refine ⟨277442296456422858472388141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184961530970948572314925427 277442296456422858472388141)
    ·
      refine ⟨104040861171158571927145553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 277442296456422858472388141 104040861171158571927145553)
      ·
        refine ⟨78030645878368928945359165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104040861171158571927145553 78030645878368928945359165)
        ·
          refine ⟨29261492204388348354509687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78030645878368928945359165 29261492204388348354509687)
          ·
            refine ⟨43892238306582522531764531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29261492204388348354509687 43892238306582522531764531)
            ·
              refine ⟨65838357459873783797646797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43892238306582522531764531 65838357459873783797646797)
              ·
                refine ⟨24689384047452668924117549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65838357459873783797646797 24689384047452668924117549)
                ·
                  refine ⟨9258519017794750846544081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24689384047452668924117549 9258519017794750846544081)
                  ·
                    refine ⟨6943889263346063134908061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9258519017794750846544081 6943889263346063134908061)
                    ·
                      refine ⟨2603958473754773675590523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943889263346063134908061 2603958473754773675590523)
                      ·
                        rfl

theorem cell23_5071191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_5071191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071191 prefixEnd_5071191 := by exact prefixLift 5071191
  have htrace : WordTrace (prefixWord ++ tailWord_5071191) baseStart_5071191 baseEnd_5071191 := by
    simpa [prefixWord, tailWord_5071191, baseEnd_5071191] using wordTrace_append hprefix tailTrace_5071191
  have hstable : (prefixWord ++ tailWord_5071191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071191).length < 2 ^ (prefixWord ++ tailWord_5071191).sum := by decide
  have hdescent : baseEnd_5071191 < baseStart_5071191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071205 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_5071205 : Nat := 118140960795 + 5071205 * 2 ^ 59
def prefixEnd_5071205 : Nat := 4983230072969 + 3 ^ 40 * 5071205 * 2
def baseEnd_5071205 : Nat := 2603965662483936620815459

theorem tailTrace_5071205 : CollatzResearch.WordTrace tailWord_5071205 prefixEnd_5071205 2603965662483936620815459 := by
  unfold tailWord_5071205
  simp only [CollatzResearch.WordTrace]
  refine ⟨184962041592897852705935069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123308027728598568470623379 184962041592897852705935069)
  ·
    refine ⟨69360765597336694764725651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184962041592897852705935069 69360765597336694764725651)
    ·
      refine ⟨104041148396005042147088477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69360765597336694764725651 104041148396005042147088477)
      ·
        refine ⟨39015430648501890805158179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104041148396005042147088477 39015430648501890805158179)
        ·
          refine ⟨58523145972752836207737269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39015430648501890805158179 58523145972752836207737269)
          ·
            refine ⟨5486544934945578394475369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58523145972752836207737269 5486544934945578394475369)
            ·
              refine ⟨4114908701209183795856527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486544934945578394475369 4114908701209183795856527)
              ·
                refine ⟨6172363051813775693784791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114908701209183795856527 6172363051813775693784791)
                ·
                  refine ⟨9258544577720663540677187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6172363051813775693784791 9258544577720663540677187)
                  ·
                    refine ⟨13887816866580995311015781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9258544577720663540677187 13887816866580995311015781)
                    ·
                      refine ⟨2603965662483936620815459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13887816866580995311015781 2603965662483936620815459)
                      ·
                        rfl

theorem cell23_5071205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_5071205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071205 prefixEnd_5071205 := by exact prefixLift 5071205
  have htrace : WordTrace (prefixWord ++ tailWord_5071205) baseStart_5071205 baseEnd_5071205 := by
    simpa [prefixWord, tailWord_5071205, baseEnd_5071205] using wordTrace_append hprefix tailTrace_5071205
  have hstable : (prefixWord ++ tailWord_5071205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071205).length < 2 ^ (prefixWord ++ tailWord_5071205).sum := by decide
  have hdescent : baseEnd_5071205 < baseStart_5071205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071235 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 1, 2, 4]
def baseStart_5071235 : Nat := 118140960795 + 5071235 * 2 ^ 59
def prefixEnd_5071235 : Nat := 4983230072969 + 3 ^ 40 * 5071235 * 2
def baseEnd_5071235 : Nat := 2603981066903571503440321

theorem tailTrace_5071235 : CollatzResearch.WordTrace tailWord_5071235 prefixEnd_5071235 2603981066903571503440321 := by
  unfold tailWord_5071235
  simp only [CollatzResearch.WordTrace]
  refine ⟨184963135782789167829527159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123308757188526111886351439 184963135782789167829527159)
  ·
    refine ⟨277444703674183751744290739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184963135782789167829527159 277444703674183751744290739)
    ·
      refine ⟨416167055511275627616436109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277444703674183751744290739 416167055511275627616436109)
      ·
        refine ⟨156062645816728360356163541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416167055511275627616436109 156062645816728360356163541)
        ·
          refine ⟨3657718261329570945847583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156062645816728360356163541 3657718261329570945847583)
          ·
            refine ⟨5486577391994356418771375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657718261329570945847583 5486577391994356418771375)
            ·
              refine ⟨8229866087991534628157063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486577391994356418771375 8229866087991534628157063)
              ·
                refine ⟨12344799131987301942235595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8229866087991534628157063 12344799131987301942235595)
                ·
                  refine ⟨18517198697980952913353393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12344799131987301942235595 18517198697980952913353393)
                  ·
                    refine ⟨13887899023485714685015045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18517198697980952913353393 13887899023485714685015045)
                    ·
                      refine ⟨2603981066903571503440321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13887899023485714685015045 2603981066903571503440321)
                      ·
                        rfl

theorem cell23_5071235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_5071235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071235 prefixEnd_5071235 := by exact prefixLift 5071235
  have htrace : WordTrace (prefixWord ++ tailWord_5071235) baseStart_5071235 baseEnd_5071235 := by
    simpa [prefixWord, tailWord_5071235, baseEnd_5071235] using wordTrace_append hprefix tailTrace_5071235
  have hstable : (prefixWord ++ tailWord_5071235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071235).length < 2 ^ (prefixWord ++ tailWord_5071235).sum := by decide
  have hdescent : baseEnd_5071235 < baseStart_5071235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071242 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5071242 : Nat := 118140960795 + 5071242 * 2 ^ 59
def prefixEnd_5071242 : Nat := 4983230072969 + 3 ^ 40 * 5071242 * 2
def baseEnd_5071242 : Nat := 2603984661268152976052789

theorem tailTrace_5071242 : CollatzResearch.WordTrace tailWord_5071242 prefixEnd_5071242 2603984661268152976052789 := by
  unfold tailWord_5071242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46240847773440952006257995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123308927395842538683354653 46240847773440952006257995)
  ·
    refine ⟨69361271660161428009386993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46240847773440952006257995 69361271660161428009386993)
    ·
      refine ⟨52020953745121071007040245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69361271660161428009386993 52020953745121071007040245)
      ·
        refine ⟨4876964413605100406910023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52020953745121071007040245 4876964413605100406910023)
        ·
          refine ⟨7315446620407650610365035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876964413605100406910023 7315446620407650610365035)
          ·
            refine ⟨10973169930611475915547553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315446620407650610365035 10973169930611475915547553)
            ·
              refine ⟨8229877447958606936660665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10973169930611475915547553 8229877447958606936660665)
              ·
                refine ⟨6172408085968955202495499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8229877447958606936660665 6172408085968955202495499)
                ·
                  refine ⟨9258612128953432803743249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6172408085968955202495499 9258612128953432803743249)
                  ·
                    refine ⟨6943959096715074602807437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9258612128953432803743249 6943959096715074602807437)
                    ·
                      refine ⟨2603984661268152976052789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6943959096715074602807437 2603984661268152976052789)
                      ·
                        rfl

theorem cell23_5071242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5071242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071242 prefixEnd_5071242 := by exact prefixLift 5071242
  have htrace : WordTrace (prefixWord ++ tailWord_5071242) baseStart_5071242 baseEnd_5071242 := by
    simpa [prefixWord, tailWord_5071242, baseEnd_5071242] using wordTrace_append hprefix tailTrace_5071242
  have hstable : (prefixWord ++ tailWord_5071242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071242).length < 2 ^ (prefixWord ++ tailWord_5071242).sum := by decide
  have hdescent : baseEnd_5071242 < baseStart_5071242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071311 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_5071311 : Nat := 118140960795 + 5071311 * 2 ^ 59
def prefixEnd_5071311 : Nat := 4983230072969 + 3 ^ 40 * 5071311 * 2
def baseEnd_5071311 : Nat := 2604020091433313206089971

theorem tailTrace_5071311 : CollatzResearch.WordTrace tailWord_5071311 prefixEnd_5071311 2604020091433313206089971 := by
  unfold tailWord_5071311
  simp only [CollatzResearch.WordTrace]
  refine ⟨184965907730513832809293787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123310605153675888539529191 184965907730513832809293787)
  ·
    refine ⟨277448861595770749213940681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184965907730513832809293787 277448861595770749213940681)
    ·
      refine ⟨208086646196828061910455511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277448861595770749213940681 208086646196828061910455511)
      ·
        refine ⟨312129969295242092865683267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208086646196828061910455511 312129969295242092865683267)
        ·
          refine ⟨468194953942863139298524901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312129969295242092865683267 468194953942863139298524901)
          ·
            refine ⟨87786553864286838618473419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468194953942863139298524901 87786553864286838618473419)
            ·
              refine ⟨131679830796430257927710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87786553864286838618473419 131679830796430257927710129)
              ·
                refine ⟨98759873097322693445782597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131679830796430257927710129 98759873097322693445782597)
                ·
                  refine ⟨18517476205748005021084237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98759873097322693445782597 18517476205748005021084237)
                  ·
                    refine ⟨6944053577155501882906589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18517476205748005021084237 6944053577155501882906589)
                    ·
                      refine ⟨2604020091433313206089971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6944053577155501882906589 2604020091433313206089971)
                      ·
                        rfl

theorem cell23_5071311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_5071311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071311 prefixEnd_5071311 := by exact prefixLift 5071311
  have htrace : WordTrace (prefixWord ++ tailWord_5071311) baseStart_5071311 baseEnd_5071311 := by
    simpa [prefixWord, tailWord_5071311, baseEnd_5071311] using wordTrace_append hprefix tailTrace_5071311
  have hstable : (prefixWord ++ tailWord_5071311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071311).length < 2 ^ (prefixWord ++ tailWord_5071311).sum := by decide
  have hdescent : baseEnd_5071311 < baseStart_5071311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071368 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_5071368 : Nat := 118140960795 + 5071368 * 2 ^ 59
def prefixEnd_5071368 : Nat := 4983230072969 + 3 ^ 40 * 5071368 * 2
def baseEnd_5071368 : Nat := 2604049359830619483077209

theorem tailTrace_5071368 : CollatzResearch.WordTrace tailWord_5071368 prefixEnd_5071368 2604049359830619483077209 := by
  unfold tailWord_5071368
  simp only [CollatzResearch.WordTrace]
  refine ⟨92483993345653665772059379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123311991127538221029412505 92483993345653665772059379)
  ·
    refine ⟨138725990018480498658089069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92483993345653665772059379 138725990018480498658089069)
    ·
      refine ⟨52022246256930186996783401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138725990018480498658089069 52022246256930186996783401)
      ·
        refine ⟨39016684692697640247587551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52022246256930186996783401 39016684692697640247587551)
        ·
          refine ⟨58525027039046460371381327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39016684692697640247587551 58525027039046460371381327)
          ·
            refine ⟨87787540558569690557071991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58525027039046460371381327 87787540558569690557071991)
            ·
              refine ⟨131681310837854535835607987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87787540558569690557071991 131681310837854535835607987)
              ·
                refine ⟨197521966256781803753411981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131681310837854535835607987 197521966256781803753411981)
                ·
                  refine ⟨74070737346293176407529493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197521966256781803753411981 74070737346293176407529493)
                  ·
                    refine ⟨3472065813107492644102945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74070737346293176407529493 3472065813107492644102945)
                    ·
                      refine ⟨2604049359830619483077209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472065813107492644102945 2604049359830619483077209)
                      ·
                        rfl

theorem cell23_5071368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_5071368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071368 prefixEnd_5071368 := by exact prefixLift 5071368
  have htrace : WordTrace (prefixWord ++ tailWord_5071368) baseStart_5071368 baseEnd_5071368 := by
    simpa [prefixWord, tailWord_5071368, baseEnd_5071368] using wordTrace_append hprefix tailTrace_5071368
  have hstable : (prefixWord ++ tailWord_5071368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071368).length < 2 ^ (prefixWord ++ tailWord_5071368).sum := by decide
  have hdescent : baseEnd_5071368 < baseStart_5071368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071381 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_5071381 : Nat := 118140960795 + 5071381 * 2 ^ 59
def prefixEnd_5071381 : Nat := 4983230072969 + 3 ^ 40 * 5071381 * 2
def baseEnd_5071381 : Nat := 2604056035079127932214649

theorem tailTrace_5071381 : CollatzResearch.WordTrace tailWord_5071381 prefixEnd_5071381 2604056035079127932214649 := by
  unfold tailWord_5071381
  simp only [CollatzResearch.WordTrace]
  refine ⟨184968460840260234764341997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123312307226840156509561331 184968460840260234764341997)
  ·
    refine ⟨69363172815097588036628249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184968460840260234764341997 69363172815097588036628249)
    ·
      refine ⟨52022379611323191027471187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69363172815097588036628249 52022379611323191027471187)
      ·
        refine ⟨78033569416984786541206781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52022379611323191027471187 78033569416984786541206781)
        ·
          refine ⟨29262588531369294952952543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78033569416984786541206781 29262588531369294952952543)
          ·
            refine ⟨43893882797053942429428815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29262588531369294952952543 43893882797053942429428815)
            ·
              refine ⟨65840824195580913644143223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43893882797053942429428815 65840824195580913644143223)
              ·
                refine ⟨98761236293371370466214835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65840824195580913644143223 98761236293371370466214835)
                ·
                  refine ⟨148141854440057055699322253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98761236293371370466214835 148141854440057055699322253)
                  ·
                    refine ⟨55553195415021395887245845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148141854440057055699322253 55553195415021395887245845)
                    ·
                      refine ⟨2604056035079127932214649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55553195415021395887245845 2604056035079127932214649)
                      ·
                        rfl

theorem cell23_5071381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_5071381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071381 prefixEnd_5071381 := by exact prefixLift 5071381
  have htrace : WordTrace (prefixWord ++ tailWord_5071381) baseStart_5071381 baseEnd_5071381 := by
    simpa [prefixWord, tailWord_5071381, baseEnd_5071381] using wordTrace_append hprefix tailTrace_5071381
  have hstable : (prefixWord ++ tailWord_5071381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071381).length < 2 ^ (prefixWord ++ tailWord_5071381).sum := by decide
  have hdescent : baseEnd_5071381 < baseStart_5071381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071395 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 3, 4]
def baseStart_5071395 : Nat := 118140960795 + 5071395 * 2 ^ 59
def prefixEnd_5071395 : Nat := 4983230072969 + 3 ^ 40 * 5071395 * 2
def baseEnd_5071395 : Nat := 868021074602763625813195

theorem tailTrace_5071395 : CollatzResearch.WordTrace tailWord_5071395 prefixEnd_5071395 868021074602763625813195 := by
  unfold tailWord_5071395
  simp only [CollatzResearch.WordTrace]
  refine ⟨184968971462209515155351639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123312647641473010103567759 184968971462209515155351639)
  ·
    refine ⟨277453457193314272733027459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184968971462209515155351639 277453457193314272733027459)
    ·
      refine ⟨416180185789971409099541189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277453457193314272733027459 416180185789971409099541189)
      ·
        refine ⟨78033784835619639206163973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416180185789971409099541189 78033784835619639206163973)
        ·
          refine ⟨14631334656678682351155745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78033784835619639206163973 14631334656678682351155745)
          ·
            refine ⟨10973500992509011763366809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14631334656678682351155745 10973500992509011763366809)
            ·
              refine ⟨8230125744381758822525107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10973500992509011763366809 8230125744381758822525107)
              ·
                refine ⟨12345188616572638233787661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8230125744381758822525107 12345188616572638233787661)
                ·
                  refine ⟨4629445731214739337670373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12345188616572638233787661 4629445731214739337670373)
                  ·
                    refine ⟨868021074602763625813195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629445731214739337670373 868021074602763625813195)
                    ·
                      rfl

theorem cell23_5071395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 4].length) (baseStart_5071395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071395 prefixEnd_5071395 := by exact prefixLift 5071395
  have htrace : WordTrace (prefixWord ++ tailWord_5071395) baseStart_5071395 baseEnd_5071395 := by
    simpa [prefixWord, tailWord_5071395, baseEnd_5071395] using wordTrace_append hprefix tailTrace_5071395
  have hstable : (prefixWord ++ tailWord_5071395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071395).length < 2 ^ (prefixWord ++ tailWord_5071395).sum := by decide
  have hdescent : baseEnd_5071395 < baseStart_5071395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071411 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_5071411 : Nat := 118140960795 + 5071411 * 2 ^ 59
def prefixEnd_5071411 : Nat := 4983230072969 + 3 ^ 40 * 5071411 * 2
def baseEnd_5071411 : Nat := 2604071439498762814839511

theorem tailTrace_5071411 : CollatzResearch.WordTrace tailWord_5071411 prefixEnd_5071411 2604071439498762814839511 := by
  unfold tailWord_5071411
  simp only [CollatzResearch.WordTrace]
  refine ⟨184969555030151549887934087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123313036686767699925289391 184969555030151549887934087)
  ·
    refine ⟨277454332545227324831901131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184969555030151549887934087 277454332545227324831901131)
    ·
      refine ⟨416181498817840987247851697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277454332545227324831901131 416181498817840987247851697)
      ·
        refine ⟨312136124113380740435888773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416181498817840987247851697 312136124113380740435888773)
        ·
          refine ⟨58525523271258888831729145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312136124113380740435888773 58525523271258888831729145)
          ·
            refine ⟨43894142453444166623796859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58525523271258888831729145 43894142453444166623796859)
            ·
              refine ⟨65841213680166249935695289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43894142453444166623796859 65841213680166249935695289)
              ·
                refine ⟨49380910260124687451771467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65841213680166249935695289 49380910260124687451771467)
                ·
                  refine ⟨74071365390187031177657201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49380910260124687451771467 74071365390187031177657201)
                  ·
                    refine ⟨55553524042640273383242901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74071365390187031177657201 55553524042640273383242901)
                    ·
                      refine ⟨2604071439498762814839511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55553524042640273383242901 2604071439498762814839511)
                      ·
                        rfl

theorem cell23_5071411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_5071411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071411 prefixEnd_5071411 := by exact prefixLift 5071411
  have htrace : WordTrace (prefixWord ++ tailWord_5071411) baseStart_5071411 baseEnd_5071411 := by
    simpa [prefixWord, tailWord_5071411, baseEnd_5071411] using wordTrace_append hprefix tailTrace_5071411
  have hstable : (prefixWord ++ tailWord_5071411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071411).length < 2 ^ (prefixWord ++ tailWord_5071411).sum := by decide
  have hdescent : baseEnd_5071411 < baseStart_5071411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071445 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_5071445 : Nat := 118140960795 + 5071445 * 2 ^ 59
def prefixEnd_5071445 : Nat := 4983230072969 + 3 ^ 40 * 5071445 * 2
def baseEnd_5071445 : Nat := 2604088897841015681814355

theorem tailTrace_5071445 : CollatzResearch.WordTrace tailWord_5071445 prefixEnd_5071445 2604088897841015681814355 := by
  unfold tailWord_5071445
  simp only [CollatzResearch.WordTrace]
  refine ⟨184970795112028373694671789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123313863408018915796447859 184970795112028373694671789)
  ·
    refine ⟨69364048167010640135501921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184970795112028373694671789 69364048167010640135501921)
    ·
      refine ⟨52023036125257980101626441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69364048167010640135501921 52023036125257980101626441)
      ·
        refine ⟨39017277093943485076219831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52023036125257980101626441 39017277093943485076219831)
        ·
          refine ⟨58525915640915227614329747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39017277093943485076219831 58525915640915227614329747)
          ·
            refine ⟨87788873461372841421494621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58525915640915227614329747 87788873461372841421494621)
            ·
              refine ⟨32920827548014815533060483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87788873461372841421494621 32920827548014815533060483)
              ·
                refine ⟨49381241322022223299590725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32920827548014815533060483 49381241322022223299590725)
                ·
                  refine ⟨9258982747879166868673261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49381241322022223299590725 9258982747879166868673261)
                  ·
                    refine ⟨3472118530454687575752473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9258982747879166868673261 3472118530454687575752473)
                    ·
                      refine ⟨2604088897841015681814355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472118530454687575752473 2604088897841015681814355)
                      ·
                        rfl

theorem cell23_5071445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_5071445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071445 prefixEnd_5071445 := by exact prefixLift 5071445
  have htrace : WordTrace (prefixWord ++ tailWord_5071445) baseStart_5071445 baseEnd_5071445 := by
    simpa [prefixWord, tailWord_5071445, baseEnd_5071445] using wordTrace_append hprefix tailTrace_5071445
  have hstable : (prefixWord ++ tailWord_5071445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071445).length < 2 ^ (prefixWord ++ tailWord_5071445).sum := by decide
  have hdescent : baseEnd_5071445 < baseStart_5071445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071472 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_5071472 : Nat := 118140960795 + 5071472 * 2 ^ 59
def prefixEnd_5071472 : Nat := 4983230072969 + 3 ^ 40 * 5071472 * 2
def baseEnd_5071472 : Nat := 868034253939562358725577

theorem tailTrace_5071472 : CollatzResearch.WordTrace tailWord_5071472 prefixEnd_5071472 868034253939562358725577 := by
  unfold tailWord_5071472
  simp only [CollatzResearch.WordTrace]
  refine ⟨92485889941465278652952335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123314519921953704870603113 92485889941465278652952335)
  ·
    refine ⟨138728834912197917979428503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92485889941465278652952335 138728834912197917979428503)
    ·
      refine ⟨208093252368296876969142755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138728834912197917979428503 208093252368296876969142755)
      ·
        refine ⟨312139878552445315453714133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208093252368296876969142755 312139878552445315453714133)
        ·
          refine ⟨7315778403572937080946425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 312139878552445315453714133 7315778403572937080946425)
          ·
            refine ⟨5486833802679702810709819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7315778403572937080946425 5486833802679702810709819)
            ·
              refine ⟨8230250704019554216064729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486833802679702810709819 8230250704019554216064729)
              ·
                refine ⟨6172688028014665662048547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8230250704019554216064729 6172688028014665662048547)
                ·
                  refine ⟨9259032042021998493072821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6172688028014665662048547 9259032042021998493072821)
                  ·
                    refine ⟨868034253939562358725577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9259032042021998493072821 868034253939562358725577)
                    ·
                      rfl

theorem cell23_5071472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_5071472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071472 prefixEnd_5071472 := by exact prefixLift 5071472
  have htrace : WordTrace (prefixWord ++ tailWord_5071472) baseStart_5071472 baseEnd_5071472 := by
    simpa [prefixWord, tailWord_5071472, baseEnd_5071472] using wordTrace_append hprefix tailTrace_5071472
  have hstable : (prefixWord ++ tailWord_5071472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071472).length < 2 ^ (prefixWord ++ tailWord_5071472).sum := by decide
  have hdescent : baseEnd_5071472 < baseStart_5071472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071485 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_5071485 : Nat := 118140960795 + 5071485 * 2 ^ 59
def prefixEnd_5071485 : Nat := 4983230072969 + 3 ^ 40 * 5071485 * 2
def baseEnd_5071485 : Nat := 868036479022398508438057

theorem tailTrace_5071485 : CollatzResearch.WordTrace tailWord_5071485 prefixEnd_5071485 868036479022398508438057 := by
  unfold tailWord_5071485
  simp only [CollatzResearch.WordTrace]
  refine ⟨184972254031883460526127909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123314836021255640350751939 184972254031883460526127909)
  ·
    refine ⟨34682297630978148848648983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 184972254031883460526127909 34682297630978148848648983)
    ·
      refine ⟨52023446446467223272973475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34682297630978148848648983 52023446446467223272973475)
      ·
        refine ⟨78035169669700834909460213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52023446446467223272973475 78035169669700834909460213)
        ·
          refine ⟨7315797156534453272761895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78035169669700834909460213 7315797156534453272761895)
          ·
            refine ⟨10973695734801679909142843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315797156534453272761895 10973695734801679909142843)
            ·
              refine ⟨16460543602202519863714265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10973695734801679909142843 16460543602202519863714265)
              ·
                refine ⟨12345407701651889897785699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16460543602202519863714265 12345407701651889897785699)
                ·
                  refine ⟨18518111552477834846678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12345407701651889897785699 18518111552477834846678549)
                  ·
                    refine ⟨868036479022398508438057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18518111552477834846678549 868036479022398508438057)
                    ·
                      rfl

theorem cell23_5071485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_5071485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071485 prefixEnd_5071485 := by exact prefixLift 5071485
  have htrace : WordTrace (prefixWord ++ tailWord_5071485) baseStart_5071485 baseEnd_5071485 := by
    simpa [prefixWord, tailWord_5071485, baseEnd_5071485] using wordTrace_append hprefix tailTrace_5071485
  have hstable : (prefixWord ++ tailWord_5071485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071485).length < 2 ^ (prefixWord ++ tailWord_5071485).sum := by decide
  have hdescent : baseEnd_5071485 < baseStart_5071485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071488 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_5071488 : Nat := 118140960795 + 5071488 * 2 ^ 59
def prefixEnd_5071488 : Nat := 4983230072969 + 3 ^ 40 * 5071488 * 2
def baseEnd_5071488 : Nat := 2604110977509159013576657

theorem tailTrace_5071488 : CollatzResearch.WordTrace tailWord_5071488 prefixEnd_5071488 2604110977509159013576657 := by
  unfold tailWord_5071488
  simp only [CollatzResearch.WordTrace]
  refine ⟨92486181725436296019243559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123314908967248394692324745 92486181725436296019243559)
  ·
    refine ⟨138729272588154444028865339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92486181725436296019243559 138729272588154444028865339)
    ·
      refine ⟨208093908882231666043298009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138729272588154444028865339 208093908882231666043298009)
      ·
        refine ⟨156070431661673749532473507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208093908882231666043298009 156070431661673749532473507)
        ·
          refine ⟨234105647492510624298710261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156070431661673749532473507 234105647492510624298710261)
          ·
            refine ⟨21947404452422871028004087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234105647492510624298710261 21947404452422871028004087)
            ·
              refine ⟨32921106678634306542006131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21947404452422871028004087 32921106678634306542006131)
              ·
                refine ⟨49381660017951459813009197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32921106678634306542006131 49381660017951459813009197)
                ·
                  refine ⟨18518122506731797429878449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49381660017951459813009197 18518122506731797429878449)
                  ·
                    refine ⟨13888591880048848072408837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18518122506731797429878449 13888591880048848072408837)
                    ·
                      refine ⟨2604110977509159013576657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13888591880048848072408837 2604110977509159013576657)
                      ·
                        rfl

theorem cell23_5071488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_5071488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071488 prefixEnd_5071488 := by exact prefixLift 5071488
  have htrace : WordTrace (prefixWord ++ tailWord_5071488) baseStart_5071488 baseEnd_5071488 := by
    simpa [prefixWord, tailWord_5071488, baseEnd_5071488] using wordTrace_append hprefix tailTrace_5071488
  have hstable : (prefixWord ++ tailWord_5071488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071488).length < 2 ^ (prefixWord ++ tailWord_5071488).sum := by decide
  have hdescent : baseEnd_5071488 < baseStart_5071488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071498 : List Nat := [3, 1, 2, 3, 3, 11]
def baseStart_5071498 : Nat := 118140960795 + 5071498 * 2 ^ 59
def prefixEnd_5071498 : Nat := 4983230072969 + 3 ^ 40 * 5071498 * 2
def baseEnd_5071498 : Nat := 10716527211175736520377

theorem tailTrace_5071498 : CollatzResearch.WordTrace tailWord_5071498 prefixEnd_5071498 10716527211175736520377 := by
  unfold tailWord_5071498
  simp only [CollatzResearch.WordTrace]
  refine ⟨46243182045209090936587787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123315152120557575830900765 46243182045209090936587787)
  ·
    refine ⟨69364773067813636404881681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46243182045209090936587787 69364773067813636404881681)
    ·
      refine ⟨52023579800860227303661261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69364773067813636404881681 52023579800860227303661261)
      ·
        refine ⟨19508842425322585238872973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52023579800860227303661261 19508842425322585238872973)
        ·
          refine ⟨7315815909495969464577365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19508842425322585238872973 7315815909495969464577365)
          ·
            refine ⟨10716527211175736520377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7315815909495969464577365 10716527211175736520377)
            ·
              rfl

theorem cell23_5071498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 11].length) (baseStart_5071498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071498 prefixEnd_5071498 := by exact prefixLift 5071498
  have htrace : WordTrace (prefixWord ++ tailWord_5071498) baseStart_5071498 baseEnd_5071498 := by
    simpa [prefixWord, tailWord_5071498, baseEnd_5071498] using wordTrace_append hprefix tailTrace_5071498
  have hstable : (prefixWord ++ tailWord_5071498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071498).length < 2 ^ (prefixWord ++ tailWord_5071498).sum := by decide
  have hdescent : baseEnd_5071498 < baseStart_5071498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071502 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_5071502 : Nat := 118140960795 + 5071502 * 2 ^ 59
def prefixEnd_5071502 : Nat := 4983230072969 + 3 ^ 40 * 5071502 * 2
def baseEnd_5071502 : Nat := 868039388746107319600531

theorem tailTrace_5071502 : CollatzResearch.WordTrace tailWord_5071502 prefixEnd_5071502 868039388746107319600531 := by
  unfold tailWord_5071502
  simp only [CollatzResearch.WordTrace]
  refine ⟨23121609259102734053687095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123315249381881248286331173 23121609259102734053687095)
  ·
    refine ⟨34682413888654101080530643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23121609259102734053687095 34682413888654101080530643)
    ·
      refine ⟨52023620832981151620795965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34682413888654101080530643 52023620832981151620795965)
      ·
        refine ⟨19508857812367931857798487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52023620832981151620795965 19508857812367931857798487)
        ·
          refine ⟨29263286718551897786697731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19508857812367931857798487 29263286718551897786697731)
          ·
            refine ⟨43894930077827846680046597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29263286718551897786697731 43894930077827846680046597)
            ·
              refine ⟨8230299389592721252508737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43894930077827846680046597 8230299389592721252508737)
              ·
                refine ⟨6172724542194540939381553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8230299389592721252508737 6172724542194540939381553)
                ·
                  refine ⟨4629543406645905704536165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172724542194540939381553 4629543406645905704536165)
                  ·
                    refine ⟨868039388746107319600531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629543406645905704536165 868039388746107319600531)
                    ·
                      rfl

theorem cell23_5071502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_5071502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071502 prefixEnd_5071502 := by exact prefixLift 5071502
  have htrace : WordTrace (prefixWord ++ tailWord_5071502) baseStart_5071502 baseEnd_5071502 := by
    simpa [prefixWord, tailWord_5071502, baseEnd_5071502] using wordTrace_append hprefix tailTrace_5071502
  have hstable : (prefixWord ++ tailWord_5071502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071502).length < 2 ^ (prefixWord ++ tailWord_5071502).sum := by decide
  have hdescent : baseEnd_5071502 < baseStart_5071502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071525 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_5071525 : Nat := 118140960795 + 5071525 * 2 ^ 59
def prefixEnd_5071525 : Nat := 4983230072969 + 3 ^ 40 * 5071525 * 2
def baseEnd_5071525 : Nat := 2604129976293375368813987

theorem tailTrace_5071525 : CollatzResearch.WordTrace tailWord_5071525 prefixEnd_5071525 2604129976293375368813987 := by
  unfold tailWord_5071525
  simp only [CollatzResearch.WordTrace]
  refine ⟨184973712951738547357584029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123315808634492364905056019 184973712951738547357584029)
  ·
    refine ⟨69365142356901955259094011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 184973712951738547357584029 69365142356901955259094011)
    ·
      refine ⟨104047713535352932888641017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69365142356901955259094011 104047713535352932888641017)
      ·
        refine ⟨78035785151514699666480763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104047713535352932888641017 78035785151514699666480763)
        ·
          refine ⟨117053677727272049499721145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78035785151514699666480763 117053677727272049499721145)
          ·
            refine ⟨87790258295454037124790859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117053677727272049499721145 87790258295454037124790859)
            ·
              refine ⟨131685387443181055687186289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87790258295454037124790859 131685387443181055687186289)
              ·
                refine ⟨98764040582385791765389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131685387443181055687186289 98764040582385791765389717)
                ·
                  refine ⟨4629564402299333989002643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98764040582385791765389717 4629564402299333989002643)
                  ·
                    refine ⟨6944346603449000983503965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4629564402299333989002643 6944346603449000983503965)
                    ·
                      refine ⟨2604129976293375368813987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6944346603449000983503965 2604129976293375368813987)
                      ·
                        rfl

theorem cell23_5071525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_5071525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071525 prefixEnd_5071525 := by exact prefixLift 5071525
  have htrace : WordTrace (prefixWord ++ tailWord_5071525) baseStart_5071525 baseEnd_5071525 := by
    simpa [prefixWord, tailWord_5071525, baseEnd_5071525] using wordTrace_append hprefix tailTrace_5071525
  have hstable : (prefixWord ++ tailWord_5071525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071525).length < 2 ^ (prefixWord ++ tailWord_5071525).sum := by decide
  have hdescent : baseEnd_5071525 < baseStart_5071525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071538 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_5071538 : Nat := 118140960795 + 5071538 * 2 ^ 59
def prefixEnd_5071538 : Nat := 4983230072969 + 3 ^ 40 * 5071538 * 2
def baseEnd_5071538 : Nat := 2604136651541883817951427

theorem tailTrace_5071538 : CollatzResearch.WordTrace tailWord_5071538 prefixEnd_5071538 2604136651541883817951427 := by
  unfold tailWord_5071538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46243546775172862644451817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123316124733794300385204845 46243546775172862644451817)
  ·
    refine ⟨34682660081379646983338863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46243546775172862644451817 34682660081379646983338863)
    ·
      refine ⟨52023990122069470475008295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34682660081379646983338863 52023990122069470475008295)
      ·
        refine ⟨78035985183104205712512443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52023990122069470475008295 78035985183104205712512443)
        ·
          refine ⟨117053977774656308568768665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78035985183104205712512443 117053977774656308568768665)
          ·
            refine ⟨87790483330992231426576499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117053977774656308568768665 87790483330992231426576499)
            ·
              refine ⟨131685724996488347139864749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87790483330992231426576499 131685724996488347139864749)
              ·
                refine ⟨49382146873683130177449281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131685724996488347139864749 49382146873683130177449281)
                ·
                  refine ⟨37036610155262347633086961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49382146873683130177449281 37036610155262347633086961)
                  ·
                    refine ⟨27777457616446760724815221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37036610155262347633086961 27777457616446760724815221)
                    ·
                      refine ⟨2604136651541883817951427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27777457616446760724815221 2604136651541883817951427)
                      ·
                        rfl

theorem cell23_5071538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_5071538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071538 prefixEnd_5071538 := by exact prefixLift 5071538
  have htrace : WordTrace (prefixWord ++ tailWord_5071538) baseStart_5071538 baseEnd_5071538 := by
    simpa [prefixWord, tailWord_5071538, baseEnd_5071538] using wordTrace_append hprefix tailTrace_5071538
  have hstable : (prefixWord ++ tailWord_5071538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071538).length < 2 ^ (prefixWord ++ tailWord_5071538).sum := by decide
  have hdescent : baseEnd_5071538 < baseStart_5071538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071553 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5071553 : Nat := 118140960795 + 5071553 * 2 ^ 59
def prefixEnd_5071553 : Nat := 4983230072969 + 3 ^ 40 * 5071553 * 2
def baseEnd_5071553 : Nat := 868048117917233753087953

theorem tailTrace_5071553 : CollatzResearch.WordTrace tailWord_5071553 prefixEnd_5071553 868048117917233753087953 := by
  unfold tailWord_5071553
  simp only [CollatzResearch.WordTrace]
  refine ⟨184974734195637108139603313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123316489463758072093068875 184974734195637108139603313)
  ·
    refine ⟨138731050646727831104702485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184974734195637108139603313 138731050646727831104702485)
    ·
      refine ⟨6503017999065367083032929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138731050646727831104702485 6503017999065367083032929)
      ·
        refine ⟨4877263499299025312274697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6503017999065367083032929 4877263499299025312274697)
        ·
          refine ⟨3657947624474268984206023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4877263499299025312274697 3657947624474268984206023)
          ·
            refine ⟨5486921436711403476309035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657947624474268984206023 5486921436711403476309035)
            ·
              refine ⟨8230382155067105214463553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5486921436711403476309035 8230382155067105214463553)
              ·
                refine ⟨6172786616300328910847665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8230382155067105214463553 6172786616300328910847665)
                ·
                  refine ⟨4629589962225246683135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172786616300328910847665 4629589962225246683135749)
                  ·
                    refine ⟨868048117917233753087953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629589962225246683135749 868048117917233753087953)
                    ·
                      rfl

theorem cell23_5071553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5071553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071553 prefixEnd_5071553 := by exact prefixLift 5071553
  have htrace : WordTrace (prefixWord ++ tailWord_5071553) baseStart_5071553 baseEnd_5071553 := by
    simpa [prefixWord, tailWord_5071553, baseEnd_5071553] using wordTrace_append hprefix tailTrace_5071553
  have hstable : (prefixWord ++ tailWord_5071553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071553).length < 2 ^ (prefixWord ++ tailWord_5071553).sum := by decide
  have hdescent : baseEnd_5071553 < baseStart_5071553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071662 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5071662 : Nat := 118140960795 + 5071662 * 2 ^ 59
def prefixEnd_5071662 : Nat := 4983230072969 + 3 ^ 40 * 5071662 * 2
def baseEnd_5071662 : Nat := 2604200323143041332800857

theorem tailTrace_5071662 : CollatzResearch.WordTrace tailWord_5071662 prefixEnd_5071662 2604200323143041332800857 := by
  unfold tailWord_5071662
  simp only [CollatzResearch.WordTrace]
  refine ⟨23122338719030277469415155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123319139834828146503547493 23122338719030277469415155)
  ·
    refine ⟨34683508078545416204122733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23122338719030277469415155 34683508078545416204122733)
    ·
      refine ⟨13006315529454531076546025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34683508078545416204122733 13006315529454531076546025)
      ·
        refine ⟨9754736647090898307409519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13006315529454531076546025 9754736647090898307409519)
        ·
          refine ⟨14632104970636347461114279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9754736647090898307409519 14632104970636347461114279)
          ·
            refine ⟨21948157455954521191671419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14632104970636347461114279 21948157455954521191671419)
            ·
              refine ⟨32922236183931781787507129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21948157455954521191671419 32922236183931781787507129)
              ·
                refine ⟨24691677137948836340630347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32922236183931781787507129 24691677137948836340630347)
                ·
                  refine ⟨37037515706923254510945521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24691677137948836340630347 37037515706923254510945521)
                  ·
                    refine ⟨27778136780192440883209141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37037515706923254510945521 27778136780192440883209141)
                    ·
                      refine ⟨2604200323143041332800857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27778136780192440883209141 2604200323143041332800857)
                      ·
                        rfl

theorem cell23_5071662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5071662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071662 prefixEnd_5071662 := by exact prefixLift 5071662
  have htrace : WordTrace (prefixWord ++ tailWord_5071662) baseStart_5071662 baseEnd_5071662 := by
    simpa [prefixWord, tailWord_5071662, baseEnd_5071662] using wordTrace_append hprefix tailTrace_5071662
  have hstable : (prefixWord ++ tailWord_5071662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071662).length < 2 ^ (prefixWord ++ tailWord_5071662).sum := by decide
  have hdescent : baseEnd_5071662 < baseStart_5071662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071672 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_5071672 : Nat := 118140960795 + 5071672 * 2 ^ 59
def prefixEnd_5071672 : Nat := 4983230072969 + 3 ^ 40 * 5071672 * 2
def baseEnd_5071672 : Nat := 2604205457949586293675811

theorem tailTrace_5071672 : CollatzResearch.WordTrace tailWord_5071672 prefixEnd_5071672 2604205457949586293675811 := by
  unfold tailWord_5071672
  simp only [CollatzResearch.WordTrace]
  refine ⟨92489537241102995731592635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123319382988137327642123513 92489537241102995731592635)
  ·
    refine ⟨138734305861654493597388953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92489537241102995731592635 138734305861654493597388953)
    ·
      refine ⟨104050729396240870198041715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138734305861654493597388953 104050729396240870198041715)
      ·
        refine ⟨156076094094361305297062573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104050729396240870198041715 156076094094361305297062573)
        ·
          refine ⟨58528535285385489486398465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156076094094361305297062573 58528535285385489486398465)
          ·
            refine ⟨43896401464039117114798849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58528535285385489486398465 43896401464039117114798849)
            ·
              refine ⟨32922301098029337836099137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43896401464039117114798849 32922301098029337836099137)
              ·
                refine ⟨24691725823522003377074353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32922301098029337836099137 24691725823522003377074353)
                ·
                  refine ⟨18518794367641502532805765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24691725823522003377074353 18518794367641502532805765)
                  ·
                    refine ⟨3472273943932781724901081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18518794367641502532805765 3472273943932781724901081)
                    ·
                      refine ⟨2604205457949586293675811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472273943932781724901081 2604205457949586293675811)
                      ·
                        rfl

theorem cell23_5071672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_5071672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071672 prefixEnd_5071672 := by exact prefixLift 5071672
  have htrace : WordTrace (prefixWord ++ tailWord_5071672) baseStart_5071672 baseEnd_5071672 := by
    simpa [prefixWord, tailWord_5071672, baseEnd_5071672] using wordTrace_append hprefix tailTrace_5071672
  have hstable : (prefixWord ++ tailWord_5071672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071672).length < 2 ^ (prefixWord ++ tailWord_5071672).sum := by decide
  have hdescent : baseEnd_5071672 < baseStart_5071672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071716 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_5071716 : Nat := 118140960795 + 5071716 * 2 ^ 59
def prefixEnd_5071716 : Nat := 4983230072969 + 3 ^ 40 * 5071716 * 2
def baseEnd_5071716 : Nat := 868076017032794707175203

theorem tailTrace_5071716 : CollatzResearch.WordTrace tailWord_5071716 prefixEnd_5071716 868076017032794707175203 := by
  unfold tailWord_5071716
  simp only [CollatzResearch.WordTrace]
  refine ⟨92490339647023293488893501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123320452862697724651858001 92490339647023293488893501)
  ·
    refine ⟨34683877367633735058335063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92490339647023293488893501 34683877367633735058335063)
    ·
      refine ⟨52025816051450602587502595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34683877367633735058335063 52025816051450602587502595)
      ·
        refine ⟨78038724077175903881253893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52025816051450602587502595 78038724077175903881253893)
        ·
          refine ⟨14632260764470481977735105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78038724077175903881253893 14632260764470481977735105)
          ·
            refine ⟨10974195573352861483301329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14632260764470481977735105 10974195573352861483301329)
            ·
              refine ⟨8230646680014646112475997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10974195573352861483301329 8230646680014646112475997)
              ·
                refine ⟨3086492505005492292178499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8230646680014646112475997 3086492505005492292178499)
                ·
                  refine ⟨4629738757508238438267749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086492505005492292178499 4629738757508238438267749)
                  ·
                    refine ⟨868076017032794707175203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4629738757508238438267749 868076017032794707175203)
                    ·
                      rfl

theorem cell23_5071716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_5071716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071716 prefixEnd_5071716 := by exact prefixLift 5071716
  have htrace : WordTrace (prefixWord ++ tailWord_5071716) baseStart_5071716 baseEnd_5071716 := by
    simpa [prefixWord, tailWord_5071716, baseEnd_5071716] using wordTrace_append hprefix tailTrace_5071716
  have hstable : (prefixWord ++ tailWord_5071716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071716).length < 2 ^ (prefixWord ++ tailWord_5071716).sum := by decide
  have hdescent : baseEnd_5071716 < baseStart_5071716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071779 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 5, 2, 2]
def baseStart_5071779 : Nat := 118140960795 + 5071779 * 2 ^ 59
def prefixEnd_5071779 : Nat := 4983230072969 + 3 ^ 40 * 5071779 * 2
def baseEnd_5071779 : Nat := 2604260400379617375037819

theorem tailTrace_5071779 : CollatzResearch.WordTrace tailWord_5071779 prefixEnd_5071779 2604260400379617375037819 := by
  unfold tailWord_5071779
  simp only [CollatzResearch.WordTrace]
  refine ⟨184982977092818348737330391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123321984728545565824886927 184982977092818348737330391)
  ·
    refine ⟨277474465639227523105995587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184982977092818348737330391 277474465639227523105995587)
    ·
      refine ⟨416211698458841284658993381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277474465639227523105995587 416211698458841284658993381)
      ·
        refine ⟨78039693461032740873561259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416211698458841284658993381 78039693461032740873561259)
        ·
          refine ⟨117059540191549111310341889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78039693461032740873561259 117059540191549111310341889)
          ·
            refine ⟨87794655143661833482756417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117059540191549111310341889 87794655143661833482756417)
            ·
              refine ⟨65845991357746375112067313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87794655143661833482756417 65845991357746375112067313)
              ·
                refine ⟨49384493518309781334050485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65845991357746375112067313 49384493518309781334050485)
                ·
                  refine ⟨4629796267341542000067233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49384493518309781334050485 4629796267341542000067233)
                  ·
                    refine ⟨3472347200506156500050425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629796267341542000067233 3472347200506156500050425)
                    ·
                      refine ⟨2604260400379617375037819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472347200506156500050425 2604260400379617375037819)
                      ·
                        rfl

theorem cell23_5071779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_5071779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071779 prefixEnd_5071779 := by exact prefixLift 5071779
  have htrace : WordTrace (prefixWord ++ tailWord_5071779) baseStart_5071779 baseEnd_5071779 := by
    simpa [prefixWord, tailWord_5071779, baseEnd_5071779] using wordTrace_append hprefix tailTrace_5071779
  have hstable : (prefixWord ++ tailWord_5071779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071779).length < 2 ^ (prefixWord ++ tailWord_5071779).sum := by decide
  have hdescent : baseEnd_5071779 < baseStart_5071779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5071847 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5071847 : Nat := 118140960795 + 5071847 * 2 ^ 59
def prefixEnd_5071847 : Nat := 4983230072969 + 3 ^ 40 * 5071847 * 2
def baseEnd_5071847 : Nat := 2604295317064123108987507

theorem tailTrace_5071847 : CollatzResearch.WordTrace tailWord_5071847 prefixEnd_5071847 2604295317064123108987507 := by
  unfold tailWord_5071847
  simp only [CollatzResearch.WordTrace]
  refine ⟨184985457256571996350805795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123323638171047997567203863 184985457256571996350805795)
  ·
    refine ⟨277478185884857994526208693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184985457256571996350805795 277478185884857994526208693)
    ·
      refine ⟨26013579926705436986832065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 277478185884857994526208693 26013579926705436986832065)
      ·
        refine ⟨19510184945029077740124049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26013579926705436986832065 19510184945029077740124049)
        ·
          refine ⟨14632638708771808305093037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19510184945029077740124049 14632638708771808305093037)
          ·
            refine ⟨5487239515789428114409889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14632638708771808305093037 5487239515789428114409889)
            ·
              refine ⟨4115429636842071085807417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5487239515789428114409889 4115429636842071085807417)
              ·
                refine ⟨3086572227631553314355563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4115429636842071085807417 3086572227631553314355563)
                ·
                  refine ⟨4629858341447329971533345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086572227631553314355563 4629858341447329971533345)
                  ·
                    refine ⟨3472393756085497478650009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629858341447329971533345 3472393756085497478650009)
                    ·
                      refine ⟨2604295317064123108987507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3472393756085497478650009 2604295317064123108987507)
                      ·
                        rfl

theorem cell23_5071847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5071847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5071847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5071847 prefixEnd_5071847 := by exact prefixLift 5071847
  have htrace : WordTrace (prefixWord ++ tailWord_5071847) baseStart_5071847 baseEnd_5071847 := by
    simpa [prefixWord, tailWord_5071847, baseEnd_5071847] using wordTrace_append hprefix tailTrace_5071847
  have hstable : (prefixWord ++ tailWord_5071847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5071847).length < 2 ^ (prefixWord ++ tailWord_5071847).sum := by decide
  have hdescent : baseEnd_5071847 < baseStart_5071847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5071847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
