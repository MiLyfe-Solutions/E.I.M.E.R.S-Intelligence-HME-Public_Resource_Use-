import V185TrunkScan23Chunk0950

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5630101 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 2, 2, 2]
def baseStart_5630101 : Nat := 118140960795 + 5630101 * 2 ^ 59
def prefixEnd_5630101 : Nat := 4983230072969 + 3 ^ 40 * 5630101 * 2
def baseEnd_5630101 : Nat := 2890947946359181937645143

theorem tailTrace_5630101 : CollatzResearch.WordTrace tailWord_5630101 prefixEnd_5630101 2890947946359181937645143 := by
  unfold tailWord_5630101
  simp only [CollatzResearch.WordTrace]
  refine ⟨205346653376113096543426157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136897768917408731028950771 205346653376113096543426157)
  ·
    refine ⟨77004995016042411203784809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205346653376113096543426157 77004995016042411203784809)
    ·
      refine ⟨57753746262031808402838607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77004995016042411203784809 57753746262031808402838607)
      ·
        refine ⟨86630619393047712604257911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57753746262031808402838607 86630619393047712604257911)
        ·
          refine ⟨129945929089571568906386867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86630619393047712604257911 129945929089571568906386867)
          ·
            refine ⟨194918893634357353359580301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129945929089571568906386867 194918893634357353359580301)
            ·
              refine ⟨73094585112884007509842613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194918893634357353359580301 73094585112884007509842613)
              ·
                refine ⟨6852617354332875704047745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73094585112884007509842613 6852617354332875704047745)
                ·
                  refine ⟨5139463015749656778035809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6852617354332875704047745 5139463015749656778035809)
                  ·
                    refine ⟨3854597261812242583526857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5139463015749656778035809 3854597261812242583526857)
                    ·
                      refine ⟨2890947946359181937645143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854597261812242583526857 2890947946359181937645143)
                      ·
                        rfl

theorem cell23_5630101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_5630101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630101 prefixEnd_5630101 := by exact prefixLift 5630101
  have htrace : WordTrace (prefixWord ++ tailWord_5630101) baseStart_5630101 baseEnd_5630101 := by
    simpa [prefixWord, tailWord_5630101, baseEnd_5630101] using wordTrace_append hprefix tailTrace_5630101
  have hstable : (prefixWord ++ tailWord_5630101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630101).length < 2 ^ (prefixWord ++ tailWord_5630101).sum := by decide
  have hdescent : baseEnd_5630101 < baseStart_5630101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630117 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_5630117 : Nat := 118140960795 + 5630117 * 2 ^ 59
def prefixEnd_5630117 : Nat := 4983230072969 + 3 ^ 40 * 5630117 * 2
def baseEnd_5630117 : Nat := 2890956162049653875045069

theorem tailTrace_5630117 : CollatzResearch.WordTrace tailWord_5630117 prefixEnd_5630117 2890956162049653875045069 := by
  unfold tailWord_5630117
  simp only [CollatzResearch.WordTrace]
  refine ⟨205347236944055131276008605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136898157962703420850672403 205347236944055131276008605)
  ·
    refine ⟨77005213854020674228503227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205347236944055131276008605 77005213854020674228503227)
    ·
      refine ⟨115507820781031011342754841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77005213854020674228503227 115507820781031011342754841)
      ·
        refine ⟨86630865585773258507066131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115507820781031011342754841 86630865585773258507066131)
        ·
          refine ⟨129946298378659887760599197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86630865585773258507066131 129946298378659887760599197)
          ·
            refine ⟨48729861891997457910224699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129946298378659887760599197 48729861891997457910224699)
            ·
              refine ⟨73094792837996186865337049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48729861891997457910224699 73094792837996186865337049)
              ·
                refine ⟨54821094628497140149002787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73094792837996186865337049 54821094628497140149002787)
                ·
                  refine ⟨82231641942745710223504181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54821094628497140149002787 82231641942745710223504181)
                  ·
                    refine ⟨7709216432132410333453517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82231641942745710223504181 7709216432132410333453517)
                    ·
                      refine ⟨2890956162049653875045069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709216432132410333453517 2890956162049653875045069)
                      ·
                        rfl

theorem cell23_5630117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_5630117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630117 prefixEnd_5630117 := by exact prefixLift 5630117
  have htrace : WordTrace (prefixWord ++ tailWord_5630117) baseStart_5630117 baseEnd_5630117 := by
    simpa [prefixWord, tailWord_5630117, baseEnd_5630117] using wordTrace_append hprefix tailTrace_5630117
  have hstable : (prefixWord ++ tailWord_5630117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630117).length < 2 ^ (prefixWord ++ tailWord_5630117).sum := by decide
  have hdescent : baseEnd_5630117 < baseStart_5630117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630122 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5630122 : Nat := 118140960795 + 5630122 * 2 ^ 59
def prefixEnd_5630122 : Nat := 4983230072969 + 3 ^ 40 * 5630122 * 2
def baseEnd_5630122 : Nat := 2890958729452926355482547

theorem tailTrace_5630122 : CollatzResearch.WordTrace tailWord_5630122 prefixEnd_5630122 2890958729452926355482547 := by
  unfold tailWord_5630122
  simp only [CollatzResearch.WordTrace]
  refine ⟨51336854827259254282485155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136898279539358011419960413 51336854827259254282485155)
  ·
    refine ⟨77005282240888881423727733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51336854827259254282485155 77005282240888881423727733)
    ·
      refine ⟨7219245210083332633474475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77005282240888881423727733 7219245210083332633474475)
      ·
        refine ⟨10828867815124998950211713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219245210083332633474475 10828867815124998950211713)
        ·
          refine ⟨8121650861343749212658785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10828867815124998950211713 8121650861343749212658785)
          ·
            refine ⟨6091238146007811909494089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8121650861343749212658785 6091238146007811909494089)
            ·
              refine ⟨4568428609505858932120567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6091238146007811909494089 4568428609505858932120567)
              ·
                refine ⟨6852642914258788398180851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568428609505858932120567 6852642914258788398180851)
                ·
                  refine ⟨10278964371388182597271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852642914258788398180851 10278964371388182597271277)
                  ·
                    refine ⟨3854611639270568473976729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10278964371388182597271277 3854611639270568473976729)
                    ·
                      refine ⟨2890958729452926355482547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854611639270568473976729 2890958729452926355482547)
                      ·
                        rfl

theorem cell23_5630122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5630122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630122 prefixEnd_5630122 := by exact prefixLift 5630122
  have htrace : WordTrace (prefixWord ++ tailWord_5630122) baseStart_5630122 baseEnd_5630122 := by
    simpa [prefixWord, tailWord_5630122, baseEnd_5630122] using wordTrace_append hprefix tailTrace_5630122
  have hstable : (prefixWord ++ tailWord_5630122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630122).length < 2 ^ (prefixWord ++ tailWord_5630122).sum := by decide
  have hdescent : baseEnd_5630122 < baseStart_5630122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630137 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_5630137 : Nat := 118140960795 + 5630137 * 2 ^ 59
def prefixEnd_5630137 : Nat := 4983230072969 + 3 ^ 40 * 5630137 * 2
def baseEnd_5630137 : Nat := 963655477220914598931659

theorem tailTrace_5630137 : CollatzResearch.WordTrace tailWord_5630137 prefixEnd_5630137 963655477220914598931659 := by
  unfold tailWord_5630137
  simp only [CollatzResearch.WordTrace]
  refine ⟨205347966403982674691736665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136898644269321783127824443 205347966403982674691736665)
  ·
    refine ⟨154010974802987006018802499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205347966403982674691736665 154010974802987006018802499)
    ·
      refine ⟨231016462204480509028203749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154010974802987006018802499 231016462204480509028203749)
      ·
        refine ⟨43315586663340095442788203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231016462204480509028203749 43315586663340095442788203)
        ·
          refine ⟨64973379995010143164182305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43315586663340095442788203 64973379995010143164182305)
          ·
            refine ⟨48730034996257607373136729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64973379995010143164182305 48730034996257607373136729)
            ·
              refine ⟨36547526247193205529852547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48730034996257607373136729 36547526247193205529852547)
              ·
                refine ⟨54821289370789808294778821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36547526247193205529852547 54821289370789808294778821)
                ·
                  refine ⟨10278991757023089055271029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54821289370789808294778821 10278991757023089055271029)
                  ·
                    refine ⟨963655477220914598931659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10278991757023089055271029 963655477220914598931659)
                    ·
                      rfl

theorem cell23_5630137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_5630137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630137 prefixEnd_5630137 := by exact prefixLift 5630137
  have htrace : WordTrace (prefixWord ++ tailWord_5630137) baseStart_5630137 baseEnd_5630137 := by
    simpa [prefixWord, tailWord_5630137, baseEnd_5630137] using wordTrace_append hprefix tailTrace_5630137
  have hstable : (prefixWord ++ tailWord_5630137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630137).length < 2 ^ (prefixWord ++ tailWord_5630137).sum := by decide
  have hdescent : baseEnd_5630137 < baseStart_5630137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630264 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_5630264 : Nat := 118140960795 + 5630264 * 2 ^ 59
def prefixEnd_5630264 : Nat := 4983230072969 + 3 ^ 40 * 5630264 * 2
def baseEnd_5630264 : Nat := 2891031643705864799906893

theorem tailTrace_5630264 : CollatzResearch.WordTrace tailWord_5630264 prefixEnd_5630264 2891031643705864799906893 := by
  unfold tailWord_5630264
  simp only [CollatzResearch.WordTrace]
  refine ⟨102676299237261287690804923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136901732316348383587739897 102676299237261287690804923)
  ·
    refine ⟨154014448855891931536207385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102676299237261287690804923 154014448855891931536207385)
    ·
      refine ⟨115510836641918948652155539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154014448855891931536207385 115510836641918948652155539)
      ·
        refine ⟨173266254962878422978233309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115510836641918948652155539 173266254962878422978233309)
        ·
          refine ⟨64974845611079408616837491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173266254962878422978233309 64974845611079408616837491)
          ·
            refine ⟨97462268416619112925256237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64974845611079408616837491 97462268416619112925256237)
            ·
              refine ⟨36548350656232167346971089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97462268416619112925256237 36548350656232167346971089)
              ·
                refine ⟨27411262992174125510228317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36548350656232167346971089 27411262992174125510228317)
                ·
                  refine ⟨10279223622065297066335619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27411262992174125510228317 10279223622065297066335619)
                  ·
                    refine ⟨15418835433097945599503429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10279223622065297066335619 15418835433097945599503429)
                    ·
                      refine ⟨2891031643705864799906893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15418835433097945599503429 2891031643705864799906893)
                      ·
                        rfl

theorem cell23_5630264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_5630264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630264 prefixEnd_5630264 := by exact prefixLift 5630264
  have htrace : WordTrace (prefixWord ++ tailWord_5630264) baseStart_5630264 baseEnd_5630264 := by
    simpa [prefixWord, tailWord_5630264, baseEnd_5630264] using wordTrace_append hprefix tailTrace_5630264
  have hstable : (prefixWord ++ tailWord_5630264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630264).length < 2 ^ (prefixWord ++ tailWord_5630264).sum := by decide
  have hdescent : baseEnd_5630264 < baseStart_5630264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630304 : List Nat := [2, 1, 1, 3, 5, 1, 10]
def baseStart_5630304 : Nat := 118140960795 + 5630304 * 2 ^ 59
def prefixEnd_5630304 : Nat := 4983230072969 + 3 ^ 40 * 5630304 * 2
def baseEnd_5630304 : Nat := 35692002258420304239589

theorem tailTrace_5630304 : CollatzResearch.WordTrace tailWord_5630304 prefixEnd_5630304 35692002258420304239589 := by
  unfold tailWord_5630304
  simp only [CollatzResearch.WordTrace]
  refine ⟨102677028697188831106532983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136902704929585108142043977 102677028697188831106532983)
  ·
    refine ⟨154015543045783246659799475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102677028697188831106532983 154015543045783246659799475)
    ·
      refine ⟨231023314568674869989699213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154015543045783246659799475 231023314568674869989699213)
      ·
        refine ⟨86633742963253076246137205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231023314568674869989699213 86633742963253076246137205)
        ·
          refine ⟨8121913402804975898075363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86633742963253076246137205 8121913402804975898075363)
          ·
            refine ⟨12182870104207463847113045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121913402804975898075363 12182870104207463847113045)
            ·
              refine ⟨35692002258420304239589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12182870104207463847113045 35692002258420304239589)
              ·
                rfl

theorem cell23_5630304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 10].length) (baseStart_5630304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630304 prefixEnd_5630304 := by exact prefixLift 5630304
  have htrace : WordTrace (prefixWord ++ tailWord_5630304) baseStart_5630304 baseEnd_5630304 := by
    simpa [prefixWord, tailWord_5630304, baseEnd_5630304] using wordTrace_append hprefix tailTrace_5630304
  have hstable : (prefixWord ++ tailWord_5630304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630304).length < 2 ^ (prefixWord ++ tailWord_5630304).sum := by decide
  have hdescent : baseEnd_5630304 < baseStart_5630304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630325 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_5630325 : Nat := 118140960795 + 5630325 * 2 ^ 59
def prefixEnd_5630325 : Nat := 4983230072969 + 3 ^ 40 * 5630325 * 2
def baseEnd_5630325 : Nat := 963687655341929687081371

theorem tailTrace_5630325 : CollatzResearch.WordTrace tailWord_5630325 prefixEnd_5630325 963687655341929687081371 := by
  unfold tailWord_5630325
  simp only [CollatzResearch.WordTrace]
  refine ⟨205354823327301582799580429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136903215551534388533053619 205354823327301582799580429)
  ·
    refine ⟨77008058747738093549842661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205354823327301582799580429 77008058747738093549842661)
    ·
      refine ⟨14439011015200892540595499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77008058747738093549842661 14439011015200892540595499)
      ·
        refine ⟨21658516522801338810893249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14439011015200892540595499 21658516522801338810893249)
        ·
          refine ⟨16243887392101004108169937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21658516522801338810893249 16243887392101004108169937)
          ·
            refine ⟨12182915544075753081127453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16243887392101004108169937 12182915544075753081127453)
            ·
              refine ⟨4568593329028407405422795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12182915544075753081127453 4568593329028407405422795)
              ·
                refine ⟨6852889993542611108134193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568593329028407405422795 6852889993542611108134193)
                ·
                  refine ⟨5139667495156958331100645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6852889993542611108134193 5139667495156958331100645)
                  ·
                    refine ⟨963687655341929687081371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139667495156958331100645 963687655341929687081371)
                    ·
                      rfl

theorem cell23_5630325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_5630325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630325 prefixEnd_5630325 := by exact prefixLift 5630325
  have htrace : WordTrace (prefixWord ++ tailWord_5630325) baseStart_5630325 baseEnd_5630325 := by
    simpa [prefixWord, tailWord_5630325, baseEnd_5630325] using wordTrace_append hprefix tailTrace_5630325
  have hstable : (prefixWord ++ tailWord_5630325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630325).length < 2 ^ (prefixWord ++ tailWord_5630325).sum := by decide
  have hdescent : baseEnd_5630325 < baseStart_5630325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630331 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3]
def baseStart_5630331 : Nat := 118140960795 + 5630331 * 2 ^ 59
def prefixEnd_5630331 : Nat := 4983230072969 + 3 ^ 40 * 5630331 * 2
def baseEnd_5630331 : Nat := 2891066046909716037769085

theorem tailTrace_5630331 : CollatzResearch.WordTrace tailWord_5630331 prefixEnd_5630331 2891066046909716037769085 := by
  unfold tailWord_5630331
  simp only [CollatzResearch.WordTrace]
  refine ⟨205355042165279845824298847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136903361443519897216199231 205355042165279845824298847)
  ·
    refine ⟨308032563247919768736448271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205355042165279845824298847 308032563247919768736448271)
    ·
      refine ⟨462048844871879653104672407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308032563247919768736448271 462048844871879653104672407)
      ·
        refine ⟨693073267307819479657008611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462048844871879653104672407 693073267307819479657008611)
        ·
          refine ⟨1039609900961729219485512917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693073267307819479657008611 1039609900961729219485512917)
          ·
            refine ⟨24365857053790528581691709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1039609900961729219485512917 24365857053790528581691709)
            ·
              refine ⟨9137196395171448218134391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24365857053790528581691709 9137196395171448218134391)
              ·
                refine ⟨13705794592757172327201587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137196395171448218134391 13705794592757172327201587)
                ·
                  refine ⟨20558691889135758490802381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13705794592757172327201587 20558691889135758490802381)
                  ·
                    refine ⟨7709509458425909434050893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20558691889135758490802381 7709509458425909434050893)
                    ·
                      refine ⟨2891066046909716037769085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709509458425909434050893 2891066046909716037769085)
                      ·
                        rfl

theorem cell23_5630331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3].length) (baseStart_5630331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630331 prefixEnd_5630331 := by exact prefixLift 5630331
  have htrace : WordTrace (prefixWord ++ tailWord_5630331) baseStart_5630331 baseEnd_5630331 := by
    simpa [prefixWord, tailWord_5630331, baseEnd_5630331] using wordTrace_append hprefix tailTrace_5630331
  have hstable : (prefixWord ++ tailWord_5630331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630331).length < 2 ^ (prefixWord ++ tailWord_5630331).sum := by decide
  have hdescent : baseEnd_5630331 < baseStart_5630331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630338 : List Nat := [3, 4, 2, 1, 2, 1, 1, 9]
def baseStart_5630338 : Nat := 118140960795 + 5630338 * 2 ^ 59
def prefixEnd_5630338 : Nat := 4983230072969 + 3 ^ 40 * 5630338 * 2
def baseEnd_5630338 : Nat := 107076653380529537421539

theorem tailTrace_5630338 : CollatzResearch.WordTrace tailWord_5630338 prefixEnd_5630338 107076653380529537421539 := by
  unfold tailWord_5630338
  simp only [CollatzResearch.WordTrace]
  refine ⟨51338824369063621504950917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136903531650836324013202445 51338824369063621504950917)
  ·
    refine ⟨9626029569199429032178297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51338824369063621504950917 9626029569199429032178297)
    ·
      refine ⟨7219522176899571774133723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9626029569199429032178297 7219522176899571774133723)
      ·
        refine ⟨10829283265349357661200585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219522176899571774133723 10829283265349357661200585)
        ·
          refine ⟨8121962449012018245900439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10829283265349357661200585 8121962449012018245900439)
          ·
            refine ⟨12182943673518027368850659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121962449012018245900439 12182943673518027368850659)
            ·
              refine ⟨18274415510277041053275989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182943673518027368850659 18274415510277041053275989)
              ·
                refine ⟨107076653380529537421539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18274415510277041053275989 107076653380529537421539)
                ·
                  rfl

theorem cell23_5630338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_5630338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630338 prefixEnd_5630338 := by exact prefixLift 5630338
  have htrace : WordTrace (prefixWord ++ tailWord_5630338) baseStart_5630338 baseEnd_5630338 := by
    simpa [prefixWord, tailWord_5630338, baseEnd_5630338] using wordTrace_append hprefix tailTrace_5630338
  have hstable : (prefixWord ++ tailWord_5630338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630338).length < 2 ^ (prefixWord ++ tailWord_5630338).sum := by decide
  have hdescent : baseEnd_5630338 < baseStart_5630338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630344 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5630344 : Nat := 118140960795 + 5630344 * 2 ^ 59
def prefixEnd_5630344 : Nat := 4983230072969 + 3 ^ 40 * 5630344 * 2
def baseEnd_5630344 : Nat := 2891072722158224486906525

theorem tailTrace_5630344 : CollatzResearch.WordTrace tailWord_5630344 prefixEnd_5630344 2891072722158224486906525 := by
  unfold tailWord_5630344
  simp only [CollatzResearch.WordTrace]
  refine ⟨102677758157116374522261043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136903677542821832696348057 102677758157116374522261043)
  ·
    refine ⟨154016637235674561783391565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102677758157116374522261043 154016637235674561783391565)
    ·
      refine ⟨57756238963377960668771837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154016637235674561783391565 57756238963377960668771837)
      ·
        refine ⟨21658589611266735250789439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57756238963377960668771837 21658589611266735250789439)
        ·
          refine ⟨32487884416900102876184159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21658589611266735250789439 32487884416900102876184159)
          ·
            refine ⟨48731826625350154314276239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32487884416900102876184159 48731826625350154314276239)
            ·
              refine ⟨73097739938025231471414359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48731826625350154314276239 73097739938025231471414359)
              ·
                refine ⟨109646609907037847207121539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73097739938025231471414359 109646609907037847207121539)
                ·
                  refine ⟨164469914860556770810682309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109646609907037847207121539 164469914860556770810682309)
                  ·
                    refine ⟨30838109036354394527002933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164469914860556770810682309 30838109036354394527002933)
                    ·
                      refine ⟨2891072722158224486906525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30838109036354394527002933 2891072722158224486906525)
                      ·
                        rfl

theorem cell23_5630344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5630344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630344 prefixEnd_5630344 := by exact prefixLift 5630344
  have htrace : WordTrace (prefixWord ++ tailWord_5630344) baseStart_5630344 baseEnd_5630344 := by
    simpa [prefixWord, tailWord_5630344, baseEnd_5630344] using wordTrace_append hprefix tailTrace_5630344
  have hstable : (prefixWord ++ tailWord_5630344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630344).length < 2 ^ (prefixWord ++ tailWord_5630344).sum := by decide
  have hdescent : baseEnd_5630344 < baseStart_5630344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630366 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5630366 : Nat := 118140960795 + 5630366 * 2 ^ 59
def prefixEnd_5630366 : Nat := 4983230072969 + 3 ^ 40 * 5630366 * 2
def baseEnd_5630366 : Nat := 2891084018732623400831425

theorem tailTrace_5630366 : CollatzResearch.WordTrace tailWord_5630366 prefixEnd_5630366 2891084018732623400831425 := by
  unfold tailWord_5630366
  simp only [CollatzResearch.WordTrace]
  refine ⟨25669539840019130850227869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136904212480102031201215301 25669539840019130850227869)
  ·
    refine ⟨9626077440007174068835451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25669539840019130850227869 9626077440007174068835451)
    ·
      refine ⟨14439116160010761103253177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9626077440007174068835451 14439116160010761103253177)
      ·
        refine ⟨10829337120008070827439883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14439116160010761103253177 10829337120008070827439883)
        ·
          refine ⟨16244005680012106241159825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10829337120008070827439883 16244005680012106241159825)
          ·
            refine ⟨12183004260009079680869869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16244005680012106241159825 12183004260009079680869869)
            ·
              refine ⟨4568626597503404880326201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12183004260009079680869869 4568626597503404880326201)
              ·
                refine ⟨3426469948127553660244651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568626597503404880326201 3426469948127553660244651)
                ·
                  refine ⟨5139704922191330490366977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426469948127553660244651 5139704922191330490366977)
                  ·
                    refine ⟨3854778691643497867775233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5139704922191330490366977 3854778691643497867775233)
                    ·
                      refine ⟨2891084018732623400831425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854778691643497867775233 2891084018732623400831425)
                      ·
                        rfl

theorem cell23_5630366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5630366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630366 prefixEnd_5630366 := by exact prefixLift 5630366
  have htrace : WordTrace (prefixWord ++ tailWord_5630366) baseStart_5630366 baseEnd_5630366 := by
    simpa [prefixWord, tailWord_5630366, baseEnd_5630366] using wordTrace_append hprefix tailTrace_5630366
  have hstable : (prefixWord ++ tailWord_5630366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630366).length < 2 ^ (prefixWord ++ tailWord_5630366).sum := by decide
  have hdescent : baseEnd_5630366 < baseStart_5630366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630384 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_5630384 : Nat := 118140960795 + 5630384 * 2 ^ 59
def prefixEnd_5630384 : Nat := 4983230072969 + 3 ^ 40 * 5630384 * 2
def baseEnd_5630384 : Nat := 2891093261384404330406341

theorem tailTrace_5630384 : CollatzResearch.WordTrace tailWord_5630384 prefixEnd_5630384 2891093261384404330406341 := by
  unfold tailWord_5630384
  simp only [CollatzResearch.WordTrace]
  refine ⟨102678487617043917937989103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136904650156058557250652137 102678487617043917937989103)
  ·
    refine ⟨154017731425565876906983655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102678487617043917937989103 154017731425565876906983655)
    ·
      refine ⟨231026597138348815360475483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154017731425565876906983655 231026597138348815360475483)
      ·
        refine ⟨346539895707523223040713225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231026597138348815360475483 346539895707523223040713225)
        ·
          refine ⟨259904921780642417280534919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346539895707523223040713225 259904921780642417280534919)
          ·
            refine ⟨389857382670963625920802379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259904921780642417280534919 389857382670963625920802379)
            ·
              refine ⟨584786074006445438881203569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389857382670963625920802379 584786074006445438881203569)
              ·
                refine ⟨438589555504834079160902677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584786074006445438881203569 438589555504834079160902677)
                ·
                  refine ⟨20558885414289097460667313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 438589555504834079160902677 20558885414289097460667313)
                  ·
                    refine ⟨15419164060716823095500485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20558885414289097460667313 15419164060716823095500485)
                    ·
                      refine ⟨2891093261384404330406341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15419164060716823095500485 2891093261384404330406341)
                      ·
                        rfl

theorem cell23_5630384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_5630384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630384 prefixEnd_5630384 := by exact prefixLift 5630384
  have htrace : WordTrace (prefixWord ++ tailWord_5630384) baseStart_5630384 baseEnd_5630384 := by
    simpa [prefixWord, tailWord_5630384, baseEnd_5630384] using wordTrace_append hprefix tailTrace_5630384
  have hstable : (prefixWord ++ tailWord_5630384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630384).length < 2 ^ (prefixWord ++ tailWord_5630384).sum := by decide
  have hdescent : baseEnd_5630384 < baseStart_5630384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630394 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_5630394 : Nat := 118140960795 + 5630394 * 2 ^ 59
def prefixEnd_5630394 : Nat := 4983230072969 + 3 ^ 40 * 5630394 * 2
def baseEnd_5630394 : Nat := 321233155132327699031255

theorem tailTrace_5630394 : CollatzResearch.WordTrace tailWord_5630394 prefixEnd_5630394 321233155132327699031255 := by
  unfold tailWord_5630394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51339334991012901895960559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136904893309367738389228157 51339334991012901895960559)
  ·
    refine ⟨77009002486519352843940839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51339334991012901895960559 77009002486519352843940839)
    ·
      refine ⟨115513503729779029265911259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77009002486519352843940839 115513503729779029265911259)
      ·
        refine ⟨173270255594668543898866889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115513503729779029265911259 173270255594668543898866889)
        ·
          refine ⟨129952691696001407924150167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173270255594668543898866889 129952691696001407924150167)
          ·
            refine ⟨194929037544002111886225251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129952691696001407924150167 194929037544002111886225251)
            ·
              refine ⟨292393556316003167829337877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194929037544002111886225251 292393556316003167829337877)
              ·
                refine ⟨13705947952312648492000213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292393556316003167829337877 13705947952312648492000213)
                ·
                  refine ⟨321233155132327699031255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13705947952312648492000213 321233155132327699031255)
                  ·
                    rfl

theorem cell23_5630394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_5630394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630394 prefixEnd_5630394 := by exact prefixLift 5630394
  have htrace : WordTrace (prefixWord ++ tailWord_5630394) baseStart_5630394 baseEnd_5630394 := by
    simpa [prefixWord, tailWord_5630394, baseEnd_5630394] using wordTrace_append hprefix tailTrace_5630394
  have hstable : (prefixWord ++ tailWord_5630394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630394).length < 2 ^ (prefixWord ++ tailWord_5630394).sum := by decide
  have hdescent : baseEnd_5630394 < baseStart_5630394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630411 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 5]
def baseStart_5630411 : Nat := 118140960795 + 5630411 * 2 ^ 59
def prefixEnd_5630411 : Nat := 4983230072969 + 3 ^ 40 * 5630411 * 2
def baseEnd_5630411 : Nat := 321234125040230636085413

theorem tailTrace_5630411 : CollatzResearch.WordTrace tailWord_5630411 prefixEnd_5630411 321234125040230636085413 := by
  unfold tailWord_5630411
  simp only [CollatzResearch.WordTrace]
  refine ⟨205357960004990019487211087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136905306669993346324807391 205357960004990019487211087)
  ·
    refine ⟨308036940007485029230816631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205357960004990019487211087 308036940007485029230816631)
    ·
      refine ⟨462055410011227543846224947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308036940007485029230816631 462055410011227543846224947)
      ·
        refine ⟨693083115016841315769337421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462055410011227543846224947 693083115016841315769337421)
        ·
          refine ⟨259906168131315493413501533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693083115016841315769337421 259906168131315493413501533)
          ·
            refine ⟨97464813049243310030063075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259906168131315493413501533 97464813049243310030063075)
            ·
              refine ⟨146197219573864965045094613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97464813049243310030063075 146197219573864965045094613)
              ·
                refine ⟨3426497333762460118244405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146197219573864965045094613 3426497333762460118244405)
                ·
                  refine ⟨321234125040230636085413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426497333762460118244405 321234125040230636085413)
                  ·
                    rfl

theorem cell23_5630411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 5].length) (baseStart_5630411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630411 prefixEnd_5630411 := by exact prefixLift 5630411
  have htrace : WordTrace (prefixWord ++ tailWord_5630411) baseStart_5630411 baseEnd_5630411 := by
    simpa [prefixWord, tailWord_5630411, baseEnd_5630411] using wordTrace_append hprefix tailTrace_5630411
  have hstable : (prefixWord ++ tailWord_5630411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630411).length < 2 ^ (prefixWord ++ tailWord_5630411).sum := by decide
  have hdescent : baseEnd_5630411 < baseStart_5630411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630424 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_5630424 : Nat := 118140960795 + 5630424 * 2 ^ 59
def prefixEnd_5630424 : Nat := 4983230072969 + 3 ^ 40 * 5630424 * 2
def baseEnd_5630424 : Nat := 963704600203528057968719

theorem tailTrace_5630424 : CollatzResearch.WordTrace tailWord_5630424 prefixEnd_5630424 963704600203528057968719 := by
  unfold tailWord_5630424
  simp only [CollatzResearch.WordTrace]
  refine ⟨102679217076971461353717163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136905622769295281804956217 102679217076971461353717163)
  ·
    refine ⟨154018825615457192030575745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102679217076971461353717163 154018825615457192030575745)
    ·
      refine ⟨115514119211592894022931809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154018825615457192030575745 115514119211592894022931809)
      ·
        refine ⟨86635589408694670517198857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115514119211592894022931809 86635589408694670517198857)
        ·
          refine ⟨64976692056521002887899143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86635589408694670517198857 64976692056521002887899143)
          ·
            refine ⟨97465038084781504331848715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64976692056521002887899143 97465038084781504331848715)
            ·
              refine ⟨146197557127172256497773073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97465038084781504331848715 146197557127172256497773073)
              ·
                refine ⟨109648167845379192373329805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146197557127172256497773073 109648167845379192373329805)
                ·
                  refine ⟨41118062942017197139998677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109648167845379192373329805 41118062942017197139998677)
                  ·
                    refine ⟨963704600203528057968719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41118062942017197139998677 963704600203528057968719)
                    ·
                      rfl

theorem cell23_5630424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_5630424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630424 prefixEnd_5630424 := by exact prefixLift 5630424
  have htrace : WordTrace (prefixWord ++ tailWord_5630424) baseStart_5630424 baseEnd_5630424 := by
    simpa [prefixWord, tailWord_5630424, baseEnd_5630424] using wordTrace_append hprefix tailTrace_5630424
  have hstable : (prefixWord ++ tailWord_5630424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630424).length < 2 ^ (prefixWord ++ tailWord_5630424).sum := by decide
  have hdescent : baseEnd_5630424 < baseStart_5630424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630461 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_5630461 : Nat := 118140960795 + 5630461 * 2 ^ 59
def prefixEnd_5630461 : Nat := 4983230072969 + 3 ^ 40 * 5630461 * 2
def baseEnd_5630461 : Nat := 2891132799394800529143487

theorem tailTrace_5630461 : CollatzResearch.WordTrace tailWord_5630461 prefixEnd_5630461 2891132799394800529143487 := by
  unfold tailWord_5630461
  simp only [CollatzResearch.WordTrace]
  refine ⟨205359783654808878026531237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136906522436539252017687491 205359783654808878026531237)
  ·
    refine ⟨38504959435276664629974607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205359783654808878026531237 38504959435276664629974607)
    ·
      refine ⟨57757439152914996944961911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38504959435276664629974607 57757439152914996944961911)
      ·
        refine ⟨86636158729372495417442867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57757439152914996944961911 86636158729372495417442867)
        ·
          refine ⟨129954238094058743126164301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86636158729372495417442867 129954238094058743126164301)
          ·
            refine ⟨48732839285272028672311613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129954238094058743126164301 48732839285272028672311613)
            ·
              refine ⟨18274814731977010752116855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48732839285272028672311613 18274814731977010752116855)
              ·
                refine ⟨27412222097965516128175283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18274814731977010752116855 27412222097965516128175283)
                ·
                  refine ⟨41118333146948274192262925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27412222097965516128175283 41118333146948274192262925)
                  ·
                    refine ⟨15419374930105602822098597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41118333146948274192262925 15419374930105602822098597)
                    ·
                      refine ⟨2891132799394800529143487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15419374930105602822098597 2891132799394800529143487)
                      ·
                        rfl

theorem cell23_5630461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_5630461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630461 prefixEnd_5630461 := by exact prefixLift 5630461
  have htrace : WordTrace (prefixWord ++ tailWord_5630461) baseStart_5630461 baseEnd_5630461 := by
    simpa [prefixWord, tailWord_5630461, baseEnd_5630461] using wordTrace_append hprefix tailTrace_5630461
  have hstable : (prefixWord ++ tailWord_5630461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630461).length < 2 ^ (prefixWord ++ tailWord_5630461).sum := by decide
  have hdescent : baseEnd_5630461 < baseStart_5630461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630488 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_5630488 : Nat := 118140960795 + 5630488 * 2 ^ 59
def prefixEnd_5630488 : Nat := 4983230072969 + 3 ^ 40 * 5630488 * 2
def baseEnd_5630488 : Nat := 963715554457490641168621

theorem tailTrace_5630488 : CollatzResearch.WordTrace tailWord_5630488 prefixEnd_5630488 963715554457490641168621 := by
  unfold tailWord_5630488
  simp only [CollatzResearch.WordTrace]
  refine ⟨102680384212855530818882059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136907178950474041091842745 102680384212855530818882059)
  ·
    refine ⟨154020576319283296228323089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102680384212855530818882059 154020576319283296228323089)
    ·
      refine ⟨115515432239462472171242317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154020576319283296228323089 115515432239462472171242317)
      ·
        refine ⟨43318287089798427064215869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115515432239462472171242317 43318287089798427064215869)
        ·
          refine ⟨16244357658674410149080951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43318287089798427064215869 16244357658674410149080951)
          ·
            refine ⟨24366536488011615223621427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16244357658674410149080951 24366536488011615223621427)
            ·
              refine ⟨36549804732017422835432141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24366536488011615223621427 36549804732017422835432141)
              ·
                refine ⟨13706176774506533563287053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36549804732017422835432141 13706176774506533563287053)
                ·
                  refine ⟨5139816290439950086232645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13706176774506533563287053 5139816290439950086232645)
                  ·
                    refine ⟨963715554457490641168621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139816290439950086232645 963715554457490641168621)
                    ·
                      rfl

theorem cell23_5630488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_5630488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630488 prefixEnd_5630488 := by exact prefixLift 5630488
  have htrace : WordTrace (prefixWord ++ tailWord_5630488) baseStart_5630488 baseEnd_5630488 := by
    simpa [prefixWord, tailWord_5630488, baseEnd_5630488] using wordTrace_append hprefix tailTrace_5630488
  have hstable : (prefixWord ++ tailWord_5630488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630488).length < 2 ^ (prefixWord ++ tailWord_5630488).sum := by decide
  have hdescent : baseEnd_5630488 < baseStart_5630488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630501 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 6]
def baseStart_5630501 : Nat := 118140960795 + 5630501 * 2 ^ 59
def prefixEnd_5630501 : Nat := 4983230072969 + 3 ^ 40 * 5630501 * 2
def baseEnd_5630501 : Nat := 321239259846775596960367

theorem tailTrace_5630501 : CollatzResearch.WordTrace tailWord_5630501 prefixEnd_5630501 321239259846775596960367 := by
  unfold tailWord_5630501
  simp only [CollatzResearch.WordTrace]
  refine ⟨205361242574663964857987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136907495049775976571991571 205361242574663964857987357)
  ·
    refine ⟨77010465965498986821745259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205361242574663964857987357 77010465965498986821745259)
    ·
      refine ⟨115515698948248480232617889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77010465965498986821745259 115515698948248480232617889)
      ·
        refine ⟨86636774211186360174463417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115515698948248480232617889 86636774211186360174463417)
        ·
          refine ⟨64977580658389770130847563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86636774211186360174463417 64977580658389770130847563)
          ·
            refine ⟨97466370987584655196271345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64977580658389770130847563 97466370987584655196271345)
            ·
              refine ⟨73099778240688491397203509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97466370987584655196271345 73099778240688491397203509)
              ·
                refine ⟨6853104210064546068487829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73099778240688491397203509 6853104210064546068487829)
                ·
                  refine ⟨321239259846775596960367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6853104210064546068487829 321239259846775596960367)
                  ·
                    rfl

theorem cell23_5630501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_5630501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630501 prefixEnd_5630501 := by exact prefixLift 5630501
  have htrace : WordTrace (prefixWord ++ tailWord_5630501) baseStart_5630501 baseEnd_5630501 := by
    simpa [prefixWord, tailWord_5630501, baseEnd_5630501] using wordTrace_append hprefix tailTrace_5630501
  have hstable : (prefixWord ++ tailWord_5630501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630501).length < 2 ^ (prefixWord ++ tailWord_5630501).sum := by decide
  have hdescent : baseEnd_5630501 < baseStart_5630501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630518 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_5630518 : Nat := 118140960795 + 5630518 * 2 ^ 59
def prefixEnd_5630518 : Nat := 4983230072969 + 3 ^ 40 * 5630518 * 2
def baseEnd_5630518 : Nat := 321240229754678534014525

theorem tailTrace_5630518 : CollatzResearch.WordTrace tailWord_5630518 prefixEnd_5630518 321240229754678534014525 := by
  unfold tailWord_5630518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835116413475148547584763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136907908410401584507570805 12835116413475148547584763)
  ·
    refine ⟨19252674620212722821377145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12835116413475148547584763 19252674620212722821377145)
    ·
      refine ⟨14439505965159542116032859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19252674620212722821377145 14439505965159542116032859)
      ·
        refine ⟨21659258947739313174049289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14439505965159542116032859 21659258947739313174049289)
        ·
          refine ⟨16244444210804484880536967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21659258947739313174049289 16244444210804484880536967)
          ·
            refine ⟨24366666316206727320805451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16244444210804484880536967 24366666316206727320805451)
            ·
              refine ⟨36549999474310090981208177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24366666316206727320805451 36549999474310090981208177)
              ·
                refine ⟨27412499605732568235906133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36549999474310090981208177 27412499605732568235906133)
                ·
                  refine ⟨321240229754678534014525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27412499605732568235906133 321240229754678534014525)
                  ·
                    rfl

theorem cell23_5630518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_5630518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630518 prefixEnd_5630518 := by exact prefixLift 5630518
  have htrace : WordTrace (prefixWord ++ tailWord_5630518) baseStart_5630518 baseEnd_5630518 := by
    simpa [prefixWord, tailWord_5630518, baseEnd_5630518] using wordTrace_append hprefix tailTrace_5630518
  have hstable : (prefixWord ++ tailWord_5630518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630518).length < 2 ^ (prefixWord ++ tailWord_5630518).sum := by decide
  have hdescent : baseEnd_5630518 < baseStart_5630518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630522 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_5630522 : Nat := 118140960795 + 5630522 * 2 ^ 59
def prefixEnd_5630522 : Nat := 4983230072969 + 3 ^ 40 * 5630522 * 2
def baseEnd_5630522 : Nat := 963721373904908263493569

theorem tailTrace_5630522 : CollatzResearch.WordTrace tailWord_5630522 prefixEnd_5630522 963721373904908263493569 := by
  unfold tailWord_5630522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51340502126896971361125455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136908005671725256963001213 51340502126896971361125455)
  ·
    refine ⟨77010753190345457041688183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51340502126896971361125455 77010753190345457041688183)
    ·
      refine ⟨115516129785518185562532275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77010753190345457041688183 115516129785518185562532275)
      ·
        refine ⟨173274194678277278343798413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115516129785518185562532275 173274194678277278343798413)
        ·
          refine ⟨64977823004353979378924405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173274194678277278343798413 64977823004353979378924405)
          ·
            refine ⟨6091670906658185566774163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64977823004353979378924405 6091670906658185566774163)
            ·
              refine ⟨9137506359987278350161245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6091670906658185566774163 9137506359987278350161245)
              ·
                refine ⟨3426564884995229381310467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9137506359987278350161245 3426564884995229381310467)
                ·
                  refine ⟨5139847327492844071965701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426564884995229381310467 5139847327492844071965701)
                  ·
                    refine ⟨963721373904908263493569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139847327492844071965701 963721373904908263493569)
                    ·
                      rfl

theorem cell23_5630522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_5630522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630522 prefixEnd_5630522 := by exact prefixLift 5630522
  have htrace : WordTrace (prefixWord ++ tailWord_5630522) baseStart_5630522 baseEnd_5630522 := by
    simpa [prefixWord, tailWord_5630522, baseEnd_5630522] using wordTrace_append hprefix tailTrace_5630522
  have hstable : (prefixWord ++ tailWord_5630522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630522).length < 2 ^ (prefixWord ++ tailWord_5630522).sum := by decide
  have hdescent : baseEnd_5630522 < baseStart_5630522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630528 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3]
def baseStart_5630528 : Nat := 118140960795 + 5630528 * 2 ^ 59
def prefixEnd_5630528 : Nat := 4983230072969 + 3 ^ 40 * 5630528 * 2
def baseEnd_5630528 : Nat := 2891167202598651767005679

theorem tailTrace_5630528 : CollatzResearch.WordTrace tailWord_5630528 prefixEnd_5630528 2891167202598651767005679 := by
  unfold tailWord_5630528
  simp only [CollatzResearch.WordTrace]
  refine ⟨102681113672783074234610119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136908151563710765646146825 102681113672783074234610119)
  ·
    refine ⟨154021670509174611351915179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102681113672783074234610119 154021670509174611351915179)
    ·
      refine ⟨231032505763761917027872769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154021670509174611351915179 231032505763761917027872769)
      ·
        refine ⟨173274379322821437770904577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231032505763761917027872769 173274379322821437770904577)
        ·
          refine ⟨129955784492116078328178433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173274379322821437770904577 129955784492116078328178433)
          ·
            refine ⟨97466838369087058746133825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129955784492116078328178433 97466838369087058746133825)
            ·
              refine ⟨73100128776815294059600369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97466838369087058746133825 73100128776815294059600369)
              ·
                refine ⟨54825096582611470544700277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73100128776815294059600369 54825096582611470544700277)
                ·
                  refine ⟨5139852804619825363565651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54825096582611470544700277 5139852804619825363565651)
                  ·
                    refine ⟨7709779206929738045348477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5139852804619825363565651 7709779206929738045348477)
                    ·
                      refine ⟨2891167202598651767005679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709779206929738045348477 2891167202598651767005679)
                      ·
                        rfl

theorem cell23_5630528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_5630528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630528 prefixEnd_5630528 := by exact prefixLift 5630528
  have htrace : WordTrace (prefixWord ++ tailWord_5630528) baseStart_5630528 baseEnd_5630528 := by
    simpa [prefixWord, tailWord_5630528, baseEnd_5630528] using wordTrace_append hprefix tailTrace_5630528
  have hstable : (prefixWord ++ tailWord_5630528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630528).length < 2 ^ (prefixWord ++ tailWord_5630528).sum := by decide
  have hdescent : baseEnd_5630528 < baseStart_5630528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630545 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_5630545 : Nat := 118140960795 + 5630545 * 2 ^ 59
def prefixEnd_5630545 : Nat := 4983230072969 + 3 ^ 40 * 5630545 * 2
def baseEnd_5630545 : Nat := 2891175931769778200493101

theorem tailTrace_5630545 : CollatzResearch.WordTrace tailWord_5630545 prefixEnd_5630545 2891175931769778200493101 := by
  unfold tailWord_5630545
  simp only [CollatzResearch.WordTrace]
  refine ⟨205362847386504560372589089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136908564924336373581726059 205362847386504560372589089)
  ·
    refine ⟨154022135539878420279441817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205362847386504560372589089 154022135539878420279441817)
    ·
      refine ⟨115516601654908815209581363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154022135539878420279441817 115516601654908815209581363)
      ·
        refine ⟨173274902482363222814372045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115516601654908815209581363 173274902482363222814372045)
        ·
          refine ⟨64978088430886208555389517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173274902482363222814372045 64978088430886208555389517)
          ·
            refine ⟨24366783161582328208271069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64978088430886208555389517 24366783161582328208271069)
            ·
              refine ⟨9137543685593373078101651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24366783161582328208271069 9137543685593373078101651)
              ·
                refine ⟨13706315528390059617152477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137543685593373078101651 13706315528390059617152477)
                ·
                  refine ⟨5139868323146272356432179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13706315528390059617152477 5139868323146272356432179)
                  ·
                    refine ⟨7709802484719408534648269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5139868323146272356432179 7709802484719408534648269)
                    ·
                      refine ⟨2891175931769778200493101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709802484719408534648269 2891175931769778200493101)
                      ·
                        rfl

theorem cell23_5630545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_5630545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630545 prefixEnd_5630545 := by exact prefixLift 5630545
  have htrace : WordTrace (prefixWord ++ tailWord_5630545) baseStart_5630545 baseEnd_5630545 := by
    simpa [prefixWord, tailWord_5630545, baseEnd_5630545] using wordTrace_append hprefix tailTrace_5630545
  have hstable : (prefixWord ++ tailWord_5630545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630545).length < 2 ^ (prefixWord ++ tailWord_5630545).sum := by decide
  have hdescent : baseEnd_5630545 < baseStart_5630545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630588 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_5630588 : Nat := 118140960795 + 5630588 * 2 ^ 59
def prefixEnd_5630588 : Nat := 4983230072969 + 3 ^ 40 * 5630588 * 2
def baseEnd_5630588 : Nat := 2891198011437921532255403

theorem tailTrace_5630588 : CollatzResearch.WordTrace tailWord_5630588 prefixEnd_5630588 2891198011437921532255403 := by
  unfold tailWord_5630588
  simp only [CollatzResearch.WordTrace]
  refine ⟨102682207862674389358202209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136909610483565852477602945 102682207862674389358202209)
  ·
    refine ⟨77011655897005792018651657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102682207862674389358202209 77011655897005792018651657)
    ·
      refine ⟨57758741922754344013988743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77011655897005792018651657 57758741922754344013988743)
      ·
        refine ⟨86638112884131516020983115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57758741922754344013988743 86638112884131516020983115)
        ·
          refine ⟨129957169326197274031474673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86638112884131516020983115 129957169326197274031474673)
          ·
            refine ⟨97467876994647955523606005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129957169326197274031474673 97467876994647955523606005)
            ·
              refine ⟨9137613468248245830338063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97467876994647955523606005 9137613468248245830338063)
              ·
                refine ⟨13706420202372368745507095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137613468248245830338063 13706420202372368745507095)
                ·
                  refine ⟨20559630303558553118260643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13706420202372368745507095 20559630303558553118260643)
                  ·
                    refine ⟨30839445455337829677390965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20559630303558553118260643 30839445455337829677390965)
                    ·
                      refine ⟨2891198011437921532255403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30839445455337829677390965 2891198011437921532255403)
                      ·
                        rfl

theorem cell23_5630588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_5630588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630588 prefixEnd_5630588 := by exact prefixLift 5630588
  have htrace : WordTrace (prefixWord ++ tailWord_5630588) baseStart_5630588 baseEnd_5630588 := by
    simpa [prefixWord, tailWord_5630588, baseEnd_5630588] using wordTrace_append hprefix tailTrace_5630588
  have hstable : (prefixWord ++ tailWord_5630588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630588).length < 2 ^ (prefixWord ++ tailWord_5630588).sum := by decide
  have hdescent : baseEnd_5630588 < baseStart_5630588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630596 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_5630596 : Nat := 118140960795 + 5630596 * 2 ^ 59
def prefixEnd_5630596 : Nat := 4983230072969 + 3 ^ 40 * 5630596 * 2
def baseEnd_5630596 : Nat := 2891202119283157500955367

theorem tailTrace_5630596 : CollatzResearch.WordTrace tailWord_5630596 prefixEnd_5630596 2891202119283157500955367 := by
  unfold tailWord_5630596
  simp only [CollatzResearch.WordTrace]
  refine ⟨102682353754659898041347821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136909805006213197388463761 102682353754659898041347821)
  ·
    refine ⟨38505882657997461765505433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102682353754659898041347821 38505882657997461765505433)
    ·
      refine ⟨28879411993498096324129075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38505882657997461765505433 28879411993498096324129075)
      ·
        refine ⟨43319117990247144486193613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28879411993498096324129075 43319117990247144486193613)
        ·
          refine ⟨16244669246342679182322605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43319117990247144486193613 16244669246342679182322605)
          ·
            refine ⟨6091750967378504693370977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16244669246342679182322605 6091750967378504693370977)
            ·
              refine ⟨4568813225533878520028233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6091750967378504693370977 4568813225533878520028233)
              ·
                refine ⟨3426609919150408890021175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568813225533878520028233 3426609919150408890021175)
                ·
                  refine ⟨5139914878725613335031763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426609919150408890021175 5139914878725613335031763)
                  ·
                    refine ⟨7709872318088420002547645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5139914878725613335031763 7709872318088420002547645)
                    ·
                      refine ⟨2891202119283157500955367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709872318088420002547645 2891202119283157500955367)
                      ·
                        rfl

theorem cell23_5630596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_5630596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630596 prefixEnd_5630596 := by exact prefixLift 5630596
  have htrace : WordTrace (prefixWord ++ tailWord_5630596) baseStart_5630596 baseEnd_5630596 := by
    simpa [prefixWord, tailWord_5630596, baseEnd_5630596] using wordTrace_append hprefix tailTrace_5630596
  have hstable : (prefixWord ++ tailWord_5630596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630596).length < 2 ^ (prefixWord ++ tailWord_5630596).sum := by decide
  have hdescent : baseEnd_5630596 < baseStart_5630596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630612 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_5630612 : Nat := 118140960795 + 5630612 * 2 ^ 59
def prefixEnd_5630612 : Nat := 4983230072969 + 3 ^ 40 * 5630612 * 2
def baseEnd_5630612 : Nat := 963736778324543146118431

theorem tailTrace_5630612 : CollatzResearch.WordTrace tailWord_5630612 prefixEnd_5630612 963736778324543146118431 := by
  unfold tailWord_5630612
  simp only [CollatzResearch.WordTrace]
  refine ⟨102682645538630915407639045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136910194051507887210185393 102682645538630915407639045)
  ·
    refine ⟨19252996038493296638932321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102682645538630915407639045 19252996038493296638932321)
    ·
      refine ⟨14439747028869972479199241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19252996038493296638932321 14439747028869972479199241)
      ·
        refine ⟨10829810271652479359399431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14439747028869972479199241 10829810271652479359399431)
        ·
          refine ⟨16244715407478719039099147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10829810271652479359399431 16244715407478719039099147)
          ·
            refine ⟨24367073111218078558648721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16244715407478719039099147 24367073111218078558648721)
            ·
              refine ⟨18275304833413558918986541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24367073111218078558648721 18275304833413558918986541)
              ·
                refine ⟨6853239312530084594619953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18275304833413558918986541 6853239312530084594619953)
                ·
                  refine ⟨5139929484397563445964965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6853239312530084594619953 5139929484397563445964965)
                  ·
                    refine ⟨963736778324543146118431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139929484397563445964965 963736778324543146118431)
                    ·
                      rfl

theorem cell23_5630612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_5630612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630612 prefixEnd_5630612 := by exact prefixLift 5630612
  have htrace : WordTrace (prefixWord ++ tailWord_5630612) baseStart_5630612 baseEnd_5630612 := by
    simpa [prefixWord, tailWord_5630612, baseEnd_5630612] using wordTrace_append hprefix tailTrace_5630612
  have hstable : (prefixWord ++ tailWord_5630612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630612).length < 2 ^ (prefixWord ++ tailWord_5630612).sum := by decide
  have hdescent : baseEnd_5630612 < baseStart_5630612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630622 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5630622 : Nat := 118140960795 + 5630622 * 2 ^ 59
def prefixEnd_5630622 : Nat := 4983230072969 + 3 ^ 40 * 5630622 * 2
def baseEnd_5630622 : Nat := 2891215469780174399230247

theorem tailTrace_5630622 : CollatzResearch.WordTrace tailWord_5630622 prefixEnd_5630622 2891215469780174399230247 := by
  unfold tailWord_5630622
  simp only [CollatzResearch.WordTrace]
  refine ⟨25670706975903200315392765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136910437204817068348761413 25670706975903200315392765)
  ·
    refine ⟨9626515115963700118272287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25670706975903200315392765 9626515115963700118272287)
    ·
      refine ⟨14439772673945550177408431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9626515115963700118272287 14439772673945550177408431)
      ·
        refine ⟨21659659010918325266112647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14439772673945550177408431 21659659010918325266112647)
        ·
          refine ⟨32489488516377487899168971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21659659010918325266112647 32489488516377487899168971)
          ·
            refine ⟨48734232774566231848753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32489488516377487899168971 48734232774566231848753457)
            ·
              refine ⟨36550674580924673886565093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48734232774566231848753457 36550674580924673886565093)
              ·
                refine ⟨6853251483923376353730955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36550674580924673886565093 6853251483923376353730955)
                ·
                  refine ⟨10279877225885064530596433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6853251483923376353730955 10279877225885064530596433)
                  ·
                    refine ⟨7709907919413798397947325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10279877225885064530596433 7709907919413798397947325)
                    ·
                      refine ⟨2891215469780174399230247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709907919413798397947325 2891215469780174399230247)
                      ·
                        rfl

theorem cell23_5630622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5630622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630622 prefixEnd_5630622 := by exact prefixLift 5630622
  have htrace : WordTrace (prefixWord ++ tailWord_5630622) baseStart_5630622 baseEnd_5630622 := by
    simpa [prefixWord, tailWord_5630622, baseEnd_5630622] using wordTrace_append hprefix tailTrace_5630622
  have hstable : (prefixWord ++ tailWord_5630622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630622).length < 2 ^ (prefixWord ++ tailWord_5630622).sum := by decide
  have hdescent : baseEnd_5630622 < baseStart_5630622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630625 : List Nat := [1, 2, 3, 3, 3, 1, 3, 7]
def baseStart_5630625 : Nat := 118140960795 + 5630625 * 2 ^ 59
def prefixEnd_5630625 : Nat := 4983230072969 + 3 ^ 40 * 5630625 * 2
def baseEnd_5630625 : Nat := 107082111489708810647879

theorem tailTrace_5630625 : CollatzResearch.WordTrace tailWord_5630625 prefixEnd_5630625 107082111489708810647879 := by
  unfold tailWord_5630625
  simp only [CollatzResearch.WordTrace]
  refine ⟨205365765226214734035501329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136910510150809822690334219 205365765226214734035501329)
  ·
    refine ⟨154024323919661050526625997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205365765226214734035501329 154024323919661050526625997)
    ·
      refine ⟨57759121469872893947484749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154024323919661050526625997 57759121469872893947484749)
      ·
        refine ⟨21659670551202335230306781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57759121469872893947484749 21659670551202335230306781)
        ·
          refine ⟨8122376456700875711365043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21659670551202335230306781 8122376456700875711365043)
          ·
            refine ⟨12183564685051313567047565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122376456700875711365043 12183564685051313567047565)
            ·
              refine ⟨4568836756894242587642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12183564685051313567047565 4568836756894242587642837)
              ·
                refine ⟨107082111489708810647879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4568836756894242587642837 107082111489708810647879)
                ·
                  rfl

theorem cell23_5630625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 7].length) (baseStart_5630625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630625 prefixEnd_5630625 := by exact prefixLift 5630625
  have htrace : WordTrace (prefixWord ++ tailWord_5630625) baseStart_5630625 baseEnd_5630625 := by
    simpa [prefixWord, tailWord_5630625, baseEnd_5630625] using wordTrace_append hprefix tailTrace_5630625
  have hstable : (prefixWord ++ tailWord_5630625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630625).length < 2 ^ (prefixWord ++ tailWord_5630625).sum := by decide
  have hdescent : baseEnd_5630625 < baseStart_5630625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630646 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5630646 : Nat := 118140960795 + 5630646 * 2 ^ 59
def prefixEnd_5630646 : Nat := 4983230072969 + 3 ^ 40 * 5630646 * 2
def baseEnd_5630646 : Nat := 963742597771960768443379

theorem tailTrace_5630646 : CollatzResearch.WordTrace tailWord_5630646 prefixEnd_5630646 963742597771960768443379 := by
  unfold tailWord_5630646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835408197446165913875987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136911020772759103081343861 12835408197446165913875987)
  ·
    refine ⟨19253112296169248870813981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12835408197446165913875987 19253112296169248870813981)
    ·
      refine ⟨7219917111063468326555243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19253112296169248870813981 7219917111063468326555243)
      ·
        refine ⟨10829875666595202489832865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219917111063468326555243 10829875666595202489832865)
        ·
          refine ⟨8122406749946401867374649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10829875666595202489832865 8122406749946401867374649)
          ·
            refine ⟨6091805062459801400530987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8122406749946401867374649 6091805062459801400530987)
            ·
              refine ⟨9137707593689702100796481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6091805062459801400530987 9137707593689702100796481)
              ·
                refine ⟨6853280695267276575597361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9137707593689702100796481 6853280695267276575597361)
                ·
                  refine ⟨5139960521450457431698021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6853280695267276575597361 5139960521450457431698021)
                  ·
                    refine ⟨963742597771960768443379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139960521450457431698021 963742597771960768443379)
                    ·
                      rfl

theorem cell23_5630646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5630646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630646 prefixEnd_5630646 := by exact prefixLift 5630646
  have htrace : WordTrace (prefixWord ++ tailWord_5630646) baseStart_5630646 baseEnd_5630646 := by
    simpa [prefixWord, tailWord_5630646, baseEnd_5630646] using wordTrace_append hprefix tailTrace_5630646
  have hstable : (prefixWord ++ tailWord_5630646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630646).length < 2 ^ (prefixWord ++ tailWord_5630646).sum := by decide
  have hdescent : baseEnd_5630646 < baseStart_5630646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630692 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_5630692 : Nat := 118140960795 + 5630692 * 2 ^ 59
def prefixEnd_5630692 : Nat := 4983230072969 + 3 ^ 40 * 5630692 * 2
def baseEnd_5630692 : Nat := 2891251413425989125354925

theorem tailTrace_5630692 : CollatzResearch.WordTrace tailWord_5630692 prefixEnd_5630692 2891251413425989125354925 := by
  unfold tailWord_5630692
  simp only [CollatzResearch.WordTrace]
  refine ⟨102684104458486002239095165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136912139277981336318793553 102684104458486002239095165)
  ·
    refine ⟨38506539171932250839660687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102684104458486002239095165 38506539171932250839660687)
    ·
      refine ⟨57759808757898376259491031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38506539171932250839660687 57759808757898376259491031)
      ·
        refine ⟨86639713136847564389236547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57759808757898376259491031 86639713136847564389236547)
        ·
          refine ⟨129959569705271346583854821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86639713136847564389236547 129959569705271346583854821)
          ·
            refine ⟨24367419319738377484472779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129959569705271346583854821 24367419319738377484472779)
            ·
              refine ⟨36551128979607566226709169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24367419319738377484472779 36551128979607566226709169)
              ·
                refine ⟨27413346734705674670031877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36551128979607566226709169 27413346734705674670031877)
                ·
                  refine ⟨5140002512757314000630977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27413346734705674670031877 5140002512757314000630977)
                  ·
                    refine ⟨3855001884567985500473233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5140002512757314000630977 3855001884567985500473233)
                    ·
                      refine ⟨2891251413425989125354925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855001884567985500473233 2891251413425989125354925)
                      ·
                        rfl

theorem cell23_5630692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_5630692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630692 prefixEnd_5630692 := by exact prefixLift 5630692
  have htrace : WordTrace (prefixWord ++ tailWord_5630692) baseStart_5630692 baseEnd_5630692 := by
    simpa [prefixWord, tailWord_5630692, baseEnd_5630692] using wordTrace_append hprefix tailTrace_5630692
  have hstable : (prefixWord ++ tailWord_5630692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630692).length < 2 ^ (prefixWord ++ tailWord_5630692).sum := by decide
  have hdescent : baseEnd_5630692 < baseStart_5630692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630766 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_5630766 : Nat := 118140960795 + 5630766 * 2 ^ 59
def prefixEnd_5630766 : Nat := 4983230072969 + 3 ^ 40 * 5630766 * 2
def baseEnd_5630766 : Nat := 321254378999380203981065

theorem tailTrace_5630766 : CollatzResearch.WordTrace tailWord_5630766 prefixEnd_5630766 321254378999380203981065 := by
  unfold tailWord_5630766
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671363489837989389548019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136913938612469276744256101 25671363489837989389548019)
  ·
    refine ⟨38507045234756984084322029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25671363489837989389548019 38507045234756984084322029)
    ·
      refine ⟨14440141963033869031620761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38507045234756984084322029 14440141963033869031620761)
      ·
        refine ⟨10830106472275401773715571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14440141963033869031620761 10830106472275401773715571)
        ·
          refine ⟨16245159708413102660573357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830106472275401773715571 16245159708413102660573357)
          ·
            refine ⟨6091934890654913497715009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16245159708413102660573357 6091934890654913497715009)
            ·
              refine ⟨4568951167991185123286257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6091934890654913497715009 4568951167991185123286257)
              ·
                refine ⟨3426713375993388842464693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568951167991185123286257 3426713375993388842464693)
                ·
                  refine ⟨321254378999380203981065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426713375993388842464693 321254378999380203981065)
                  ·
                    rfl

theorem cell23_5630766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_5630766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630766 prefixEnd_5630766 := by exact prefixLift 5630766
  have htrace : WordTrace (prefixWord ++ tailWord_5630766) baseStart_5630766 baseEnd_5630766 := by
    simpa [prefixWord, tailWord_5630766, baseEnd_5630766] using wordTrace_append hprefix tailTrace_5630766
  have hstable : (prefixWord ++ tailWord_5630766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630766).length < 2 ^ (prefixWord ++ tailWord_5630766).sum := by decide
  have hdescent : baseEnd_5630766 < baseStart_5630766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630775 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 3, 4]
def baseStart_5630775 : Nat := 118140960795 + 5630775 * 2 ^ 59
def prefixEnd_5630775 : Nat := 4983230072969 + 3 ^ 40 * 5630775 * 2
def baseEnd_5630775 : Nat := 963764677440104100205681

theorem tailTrace_5630775 : CollatzResearch.WordTrace tailWord_5630775 prefixEnd_5630775 963764677440104100205681 := by
  unfold tailWord_5630775
  simp only [CollatzResearch.WordTrace]
  refine ⟨205371236175671309653461779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136914157450447539768974519 205371236175671309653461779)
  ·
    refine ⟨308056854263506964480192669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205371236175671309653461779 308056854263506964480192669)
    ·
      refine ⟨115521320348815111680072251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308056854263506964480192669 115521320348815111680072251)
      ·
        refine ⟨173281980523222667520108377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115521320348815111680072251 173281980523222667520108377)
        ·
          refine ⟨129961485392417000640081283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173281980523222667520108377 129961485392417000640081283)
          ·
            refine ⟨194942228088625500960121925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129961485392417000640081283 194942228088625500960121925)
            ·
              refine ⟨36551667766617281430022861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194942228088625500960121925 36551667766617281430022861)
              ·
                refine ⟨13706875412481480536258573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36551667766617281430022861 13706875412481480536258573)
                ·
                  refine ⟨5140078279680555201096965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13706875412481480536258573 5140078279680555201096965)
                  ·
                    refine ⟨963764677440104100205681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140078279680555201096965 963764677440104100205681)
                    ·
                      rfl

theorem cell23_5630775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_5630775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630775 prefixEnd_5630775 := by exact prefixLift 5630775
  have htrace : WordTrace (prefixWord ++ tailWord_5630775) baseStart_5630775 baseEnd_5630775 := by
    simpa [prefixWord, tailWord_5630775, baseEnd_5630775] using wordTrace_append hprefix tailTrace_5630775
  have hstable : (prefixWord ++ tailWord_5630775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630775).length < 2 ^ (prefixWord ++ tailWord_5630775).sum := by decide
  have hdescent : baseEnd_5630775 < baseStart_5630775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630808 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5630808 : Nat := 118140960795 + 5630808 * 2 ^ 59
def prefixEnd_5630808 : Nat := 4983230072969 + 3 ^ 40 * 5630808 * 2
def baseEnd_5630808 : Nat := 2891310977181910671504391

theorem tailTrace_5630808 : CollatzResearch.WordTrace tailWord_5630808 prefixEnd_5630808 2891310977181910671504391 := by
  unfold tailWord_5630808
  simp only [CollatzResearch.WordTrace]
  refine ⟨102686219892275878144706539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136914959856367837526275385 102686219892275878144706539)
  ·
    refine ⟨154029329838413817217059809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102686219892275878144706539 154029329838413817217059809)
    ·
      refine ⟨115521997378810362912794857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154029329838413817217059809 115521997378810362912794857)
      ·
        refine ⟨86641498034107772184596143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115521997378810362912794857 86641498034107772184596143)
        ·
          refine ⟨129962247051161658276894215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86641498034107772184596143 129962247051161658276894215)
          ·
            refine ⟨194943370576742487415341323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129962247051161658276894215 194943370576742487415341323)
            ·
              refine ⟨292415055865113731123011985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194943370576742487415341323 292415055865113731123011985)
              ·
                refine ⟨219311291898835298342258989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292415055865113731123011985 219311291898835298342258989)
                ·
                  refine ⟨82241734462063236878347121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219311291898835298342258989 82241734462063236878347121)
                  ·
                    refine ⟨61681300846547427658760341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82241734462063236878347121 61681300846547427658760341)
                    ·
                      refine ⟨2891310977181910671504391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61681300846547427658760341 2891310977181910671504391)
                      ·
                        rfl

theorem cell23_5630808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5630808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630808 prefixEnd_5630808 := by exact prefixLift 5630808
  have htrace : WordTrace (prefixWord ++ tailWord_5630808) baseStart_5630808 baseEnd_5630808 := by
    simpa [prefixWord, tailWord_5630808, baseEnd_5630808] using wordTrace_append hprefix tailTrace_5630808
  have hstable : (prefixWord ++ tailWord_5630808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630808).length < 2 ^ (prefixWord ++ tailWord_5630808).sum := by decide
  have hdescent : baseEnd_5630808 < baseStart_5630808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630809 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 1, 4]
def baseStart_5630809 : Nat := 118140960795 + 5630809 * 2 ^ 59
def prefixEnd_5630809 : Nat := 4983230072969 + 3 ^ 40 * 5630809 * 2
def baseEnd_5630809 : Nat := 963770496887521722530629

theorem tailTrace_5630809 : CollatzResearch.WordTrace tailWord_5630809 prefixEnd_5630809 963770496887521722530629 := by
  unfold tailWord_5630809
  simp only [CollatzResearch.WordTrace]
  refine ⟨205372476257548133460199481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136914984171698755640132987 205372476257548133460199481)
  ·
    refine ⟨154029357193161100095149611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205372476257548133460199481 154029357193161100095149611)
    ·
      refine ⟨231044035789741650142724417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154029357193161100095149611 231044035789741650142724417)
      ·
        refine ⟨173283026842306237607043313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231044035789741650142724417 173283026842306237607043313)
        ·
          refine ⟨129962270131729678205282485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173283026842306237607043313 129962270131729678205282485)
          ·
            refine ⟨12183962824849657331745233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129962270131729678205282485 12183962824849657331745233)
            ·
              refine ⟨9137972118637242998808925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12183962824849657331745233 9137972118637242998808925)
              ·
                refine ⟨3426739544488966124553347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9137972118637242998808925 3426739544488966124553347)
                ·
                  refine ⟨5140109316733449186830021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426739544488966124553347 5140109316733449186830021)
                  ·
                    refine ⟨963770496887521722530629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140109316733449186830021 963770496887521722530629)
                    ·
                      rfl

theorem cell23_5630809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 4].length) (baseStart_5630809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630809 prefixEnd_5630809 := by exact prefixLift 5630809
  have htrace : WordTrace (prefixWord ++ tailWord_5630809) baseStart_5630809 baseEnd_5630809 := by
    simpa [prefixWord, tailWord_5630809, baseEnd_5630809] using wordTrace_append hprefix tailTrace_5630809
  have hstable : (prefixWord ++ tailWord_5630809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630809).length < 2 ^ (prefixWord ++ tailWord_5630809).sum := by decide
  have hdescent : baseEnd_5630809 < baseStart_5630809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630832 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3]
def baseStart_5630832 : Nat := 118140960795 + 5630832 * 2 ^ 59
def prefixEnd_5630832 : Nat := 4983230072969 + 3 ^ 40 * 5630832 * 2
def baseEnd_5630832 : Nat := 2891323300717618577604281

theorem tailTrace_5630832 : CollatzResearch.WordTrace tailWord_5630832 prefixEnd_5630832 2891323300717618577604281 := by
  unfold tailWord_5630832
  simp only [CollatzResearch.WordTrace]
  refine ⟨102686657568232404194143375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136915543424309872258857833 102686657568232404194143375)
  ·
    refine ⟨154029986352348606291215063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102686657568232404194143375 154029986352348606291215063)
    ·
      refine ⟨231044979528522909436822595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154029986352348606291215063 231044979528522909436822595)
      ·
        refine ⟨346567469292784364155233893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231044979528522909436822595 346567469292784364155233893)
        ·
          refine ⟨64981400492397068279106355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346567469292784364155233893 64981400492397068279106355)
          ·
            refine ⟨97472100738595602418659533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64981400492397068279106355 97472100738595602418659533)
            ·
              refine ⟨36552037776973350906997325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97472100738595602418659533 36552037776973350906997325)
              ·
                refine ⟨13707014166365006590123997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36552037776973350906997325 13707014166365006590123997)
                ·
                  refine ⟨5140130312386877471296499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13707014166365006590123997 5140130312386877471296499)
                  ·
                    refine ⟨7710195468580316206944749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140130312386877471296499 7710195468580316206944749)
                    ·
                      refine ⟨2891323300717618577604281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710195468580316206944749 2891323300717618577604281)
                      ·
                        rfl

theorem cell23_5630832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_5630832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630832 prefixEnd_5630832 := by exact prefixLift 5630832
  have htrace : WordTrace (prefixWord ++ tailWord_5630832) baseStart_5630832 baseEnd_5630832 := by
    simpa [prefixWord, tailWord_5630832, baseEnd_5630832] using wordTrace_append hprefix tailTrace_5630832
  have hstable : (prefixWord ++ tailWord_5630832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630832).length < 2 ^ (prefixWord ++ tailWord_5630832).sum := by decide
  have hdescent : baseEnd_5630832 < baseStart_5630832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630876 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5630876 : Nat := 118140960795 + 5630876 * 2 ^ 59
def prefixEnd_5630876 : Nat := 4983230072969 + 3 ^ 40 * 5630876 * 2
def baseEnd_5630876 : Nat := 2891345893866416405454079

theorem tailTrace_5630876 : CollatzResearch.WordTrace tailWord_5630876 prefixEnd_5630876 2891345893866416405454079 := by
  unfold tailWord_5630876
  simp only [CollatzResearch.WordTrace]
  refine ⟨102687459974152701951444241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136916613298870269268592321 102687459974152701951444241)
  ·
    refine ⟨77015594980614526463583181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102687459974152701951444241 77015594980614526463583181)
    ·
      refine ⟨28880848117730447423843693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77015594980614526463583181 28880848117730447423843693)
      ·
        refine ⟨10830318044148917783941385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28880848117730447423843693 10830318044148917783941385)
        ·
          refine ⟨8122738533111688337956039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10830318044148917783941385 8122738533111688337956039)
          ·
            refine ⟨12184107799667532506934059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122738533111688337956039 12184107799667532506934059)
            ·
              refine ⟨18276161699501298760401089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12184107799667532506934059 18276161699501298760401089)
              ·
                refine ⟨13707121274625974070300817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18276161699501298760401089 13707121274625974070300817)
                ·
                  refine ⟨10280340955969480552725613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13707121274625974070300817 10280340955969480552725613)
                  ·
                    refine ⟨3855127858488555207272105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10280340955969480552725613 3855127858488555207272105)
                    ·
                      refine ⟨2891345893866416405454079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855127858488555207272105 2891345893866416405454079)
                      ·
                        rfl

theorem cell23_5630876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5630876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630876 prefixEnd_5630876 := by exact prefixLift 5630876
  have htrace : WordTrace (prefixWord ++ tailWord_5630876) baseStart_5630876 baseEnd_5630876 := by
    simpa [prefixWord, tailWord_5630876, baseEnd_5630876] using wordTrace_append hprefix tailTrace_5630876
  have hstable : (prefixWord ++ tailWord_5630876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630876).length < 2 ^ (prefixWord ++ tailWord_5630876).sum := by decide
  have hdescent : baseEnd_5630876 < baseStart_5630876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630909 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5630909 : Nat := 118140960795 + 5630909 * 2 ^ 59
def prefixEnd_5630909 : Nat := 4983230072969 + 3 ^ 40 * 5630909 * 2
def baseEnd_5630909 : Nat := 2891362838728014776341427

theorem tailTrace_5630909 : CollatzResearch.WordTrace tailWord_5630909 prefixEnd_5630909 2891362838728014776341427 := by
  unfold tailWord_5630909
  simp only [CollatzResearch.WordTrace]
  refine ⟨205376123557185850538839781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136917415704790567025893187 205376123557185850538839781)
  ·
    refine ⟨38508023166972346976032459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205376123557185850538839781 38508023166972346976032459)
    ·
      refine ⟨57762034750458520464048689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38508023166972346976032459 57762034750458520464048689)
      ·
        refine ⟨43321526062843890348036517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57762034750458520464048689 43321526062843890348036517)
        ·
          refine ⟨8122786136783229440256847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43321526062843890348036517 8122786136783229440256847)
          ·
            refine ⟨12184179205174844160385271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122786136783229440256847 12184179205174844160385271)
            ·
              refine ⟨18276268807762266240577907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12184179205174844160385271 18276268807762266240577907)
              ·
                refine ⟨27414403211643399360866861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18276268807762266240577907 27414403211643399360866861)
                ·
                  refine ⟨10280401204366274760325073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27414403211643399360866861 10280401204366274760325073)
                  ·
                    refine ⟨7710300903274706070243805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10280401204366274760325073 7710300903274706070243805)
                    ·
                      refine ⟨2891362838728014776341427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710300903274706070243805 2891362838728014776341427)
                      ·
                        rfl

theorem cell23_5630909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5630909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630909 prefixEnd_5630909 := by exact prefixLift 5630909
  have htrace : WordTrace (prefixWord ++ tailWord_5630909) baseStart_5630909 baseEnd_5630909 := by
    simpa [prefixWord, tailWord_5630909, baseEnd_5630909] using wordTrace_append hprefix tailTrace_5630909
  have hstable : (prefixWord ++ tailWord_5630909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630909).length < 2 ^ (prefixWord ++ tailWord_5630909).sum := by decide
  have hdescent : baseEnd_5630909 < baseStart_5630909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630926 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_5630926 : Nat := 118140960795 + 5630926 * 2 ^ 59
def prefixEnd_5630926 : Nat := 4983230072969 + 3 ^ 40 * 5630926 * 2
def baseEnd_5630926 : Nat := 2891371567899141209828849

theorem tailTrace_5630926 : CollatzResearch.WordTrace tailWord_5630926 prefixEnd_5630926 2891371567899141209828849 := by
  unfold tailWord_5630926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25672092949765532805276079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136917829065416174961472421 25672092949765532805276079)
  ·
    refine ⟨38508139424648299207914119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25672092949765532805276079 38508139424648299207914119)
    ·
      refine ⟨57762209136972448811871179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38508139424648299207914119 57762209136972448811871179)
      ·
        refine ⟨86643313705458673217806769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57762209136972448811871179 86643313705458673217806769)
        ·
          refine ⟨64982485279094004913355077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86643313705458673217806769 64982485279094004913355077)
          ·
            refine ⟨12184215989830125921254077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64982485279094004913355077 12184215989830125921254077)
            ·
              refine ⟨4569080996186297220470279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12184215989830125921254077 4569080996186297220470279)
              ·
                refine ⟨6853621494279445830705419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569080996186297220470279 6853621494279445830705419)
                ·
                  refine ⟨10280432241419168746058129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6853621494279445830705419 10280432241419168746058129)
                  ·
                    refine ⟨7710324181064376559543597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10280432241419168746058129 7710324181064376559543597)
                    ·
                      refine ⟨2891371567899141209828849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710324181064376559543597 2891371567899141209828849)
                      ·
                        rfl

theorem cell23_5630926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_5630926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630926 prefixEnd_5630926 := by exact prefixLift 5630926
  have htrace : WordTrace (prefixWord ++ tailWord_5630926) baseStart_5630926 baseEnd_5630926 := by
    simpa [prefixWord, tailWord_5630926, baseEnd_5630926] using wordTrace_append hprefix tailTrace_5630926
  have hstable : (prefixWord ++ tailWord_5630926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630926).length < 2 ^ (prefixWord ++ tailWord_5630926).sum := by decide
  have hdescent : baseEnd_5630926 < baseStart_5630926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630966 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5630966 : Nat := 118140960795 + 5630966 * 2 ^ 59
def prefixEnd_5630966 : Nat := 4983230072969 + 3 ^ 40 * 5630966 * 2
def baseEnd_5630966 : Nat := 2891392107125321053328665

theorem tailTrace_5630966 : CollatzResearch.WordTrace tailWord_5630966 prefixEnd_5630966 2891392107125321053328665 := by
  unfold tailWord_5630966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12836137657373709329604047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136918801678652899515776501 12836137657373709329604047)
  ·
    refine ⟨19254206486060563994406071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12836137657373709329604047 19254206486060563994406071)
    ·
      refine ⟨28881309729090845991609107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19254206486060563994406071 28881309729090845991609107)
      ·
        refine ⟨43321964593636268987413661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28881309729090845991609107 43321964593636268987413661)
        ·
          refine ⟨16245736722613600870280123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43321964593636268987413661 16245736722613600870280123)
          ·
            refine ⟨24368605083920401305420185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16245736722613600870280123 24368605083920401305420185)
            ·
              refine ⟨18276453812940300979065139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24368605083920401305420185 18276453812940300979065139)
              ·
                refine ⟨27414680719410451468597709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18276453812940300979065139 27414680719410451468597709)
                ·
                  refine ⟨10280505269778919300724141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27414680719410451468597709 10280505269778919300724141)
                  ·
                    refine ⟨3855189476167094737771553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10280505269778919300724141 3855189476167094737771553)
                    ·
                      refine ⟨2891392107125321053328665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855189476167094737771553 2891392107125321053328665)
                      ·
                        rfl

theorem cell23_5630966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5630966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630966 prefixEnd_5630966 := by exact prefixLift 5630966
  have htrace : WordTrace (prefixWord ++ tailWord_5630966) baseStart_5630966 baseEnd_5630966 := by
    simpa [prefixWord, tailWord_5630966, baseEnd_5630966] using wordTrace_append hprefix tailTrace_5630966
  have hstable : (prefixWord ++ tailWord_5630966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630966).length < 2 ^ (prefixWord ++ tailWord_5630966).sum := by decide
  have hdescent : baseEnd_5630966 < baseStart_5630966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631002 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_5631002 : Nat := 118140960795 + 5631002 * 2 ^ 59
def prefixEnd_5631002 : Nat := 4983230072969 + 3 ^ 40 * 5631002 * 2
def baseEnd_5631002 : Nat := 321267843603209212497611

theorem tailTrace_5631002 : CollatzResearch.WordTrace tailWord_5631002 prefixEnd_5631002 321267843603209212497611 := by
  unfold tailWord_5631002
  simp only [CollatzResearch.WordTrace]
  refine ⟨51344878886462231855493815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136919677030565951614650173 51344878886462231855493815)
  ·
    refine ⟨77017318329693347783240723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51344878886462231855493815 77017318329693347783240723)
    ·
      refine ⟨115525977494540021674861085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77017318329693347783240723 115525977494540021674861085)
      ·
        refine ⟨43322241560452508128072907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115525977494540021674861085 43322241560452508128072907)
        ·
          refine ⟨64983362340678762192109361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43322241560452508128072907 64983362340678762192109361)
          ·
            refine ⟨48737521755509071644082021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64983362340678762192109361 48737521755509071644082021)
            ·
              refine ⟨9138285329157950933265379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48737521755509071644082021 9138285329157950933265379)
              ·
                refine ⟨13707427993736926399898069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9138285329157950933265379 13707427993736926399898069)
                ·
                  refine ⟨321267843603209212497611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13707427993736926399898069 321267843603209212497611)
                  ·
                    rfl

theorem cell23_5631002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_5631002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631002 prefixEnd_5631002 := by exact prefixLift 5631002
  have htrace : WordTrace (prefixWord ++ tailWord_5631002) baseStart_5631002 baseEnd_5631002 := by
    simpa [prefixWord, tailWord_5631002, baseEnd_5631002] using wordTrace_append hprefix tailTrace_5631002
  have hstable : (prefixWord ++ tailWord_5631002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631002).length < 2 ^ (prefixWord ++ tailWord_5631002).sum := by decide
  have hdescent : baseEnd_5631002 < baseStart_5631002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631013 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 2, 2, 2]
def baseStart_5631013 : Nat := 118140960795 + 5631013 * 2 ^ 59
def prefixEnd_5631013 : Nat := 4983230072969 + 3 ^ 40 * 5631013 * 2
def baseEnd_5631013 : Nat := 2891416240716082369440949

theorem tailTrace_5631013 : CollatzResearch.WordTrace tailWord_5631013 prefixEnd_5631013 2891416240716082369440949 := by
  unfold tailWord_5631013
  simp only [CollatzResearch.WordTrace]
  refine ⟨205379916748809076300625693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136919944499206050867083795 205379916748809076300625693)
  ·
    refine ⟨77017468780803403612734635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205379916748809076300625693 77017468780803403612734635)
    ·
      refine ⟨115526203171205105419101953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77017468780803403612734635 115526203171205105419101953)
      ·
        refine ⟨86644652378403829064326465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115526203171205105419101953 86644652378403829064326465)
        ·
          refine ⟨64983489283802871798244849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86644652378403829064326465 64983489283802871798244849)
          ·
            refine ⟨48737616962852153848683637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64983489283802871798244849 48737616962852153848683637)
            ·
              refine ⟨4569151590267389423314091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48737616962852153848683637 4569151590267389423314091)
              ·
                refine ⟨6853727385401084134971137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569151590267389423314091 6853727385401084134971137)
                ·
                  refine ⟨5140295539050813101228353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6853727385401084134971137 5140295539050813101228353)
                  ·
                    refine ⟨3855221654288109825921265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5140295539050813101228353 3855221654288109825921265)
                    ·
                      refine ⟨2891416240716082369440949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855221654288109825921265 2891416240716082369440949)
                      ·
                        rfl

theorem cell23_5631013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_5631013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631013 prefixEnd_5631013 := by exact prefixLift 5631013
  have htrace : WordTrace (prefixWord ++ tailWord_5631013) baseStart_5631013 baseEnd_5631013 := by
    simpa [prefixWord, tailWord_5631013, baseEnd_5631013] using wordTrace_append hprefix tailTrace_5631013
  have hstable : (prefixWord ++ tailWord_5631013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631013).length < 2 ^ (prefixWord ++ tailWord_5631013).sum := by decide
  have hdescent : baseEnd_5631013 < baseStart_5631013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631032 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_5631032 : Nat := 118140960795 + 5631032 * 2 ^ 59
def prefixEnd_5631032 : Nat := 4983230072969 + 3 ^ 40 * 5631032 * 2
def baseEnd_5631032 : Nat := 963808665616172598367787

theorem tailTrace_5631032 : CollatzResearch.WordTrace tailWord_5631032 prefixEnd_5631032 963808665616172598367787 := by
  unfold tailWord_5631032
  simp only [CollatzResearch.WordTrace]
  refine ⟨102690304867870121272783675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136920406490493495030378233 102690304867870121272783675)
  ·
    refine ⟨154035457301805181909175513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102690304867870121272783675 154035457301805181909175513)
    ·
      refine ⟨115526592976353886431881635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154035457301805181909175513 115526592976353886431881635)
      ·
        refine ⟨173289889464530829647822453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115526592976353886431881635 173289889464530829647822453)
        ·
          refine ⟨16245927137299765279483355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173289889464530829647822453 16245927137299765279483355)
          ·
            refine ⟨24368890705949647919225033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16245927137299765279483355 24368890705949647919225033)
            ·
              refine ⟨18276668029462235939418775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24368890705949647919225033 18276668029462235939418775)
              ·
                refine ⟨27415002044193353909128163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18276668029462235939418775 27415002044193353909128163)
                ·
                  refine ⟨41122503066290030863692245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27415002044193353909128163 41122503066290030863692245)
                  ·
                    refine ⟨963808665616172598367787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41122503066290030863692245 963808665616172598367787)
                    ·
                      rfl

theorem cell23_5631032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_5631032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631032 prefixEnd_5631032 := by exact prefixLift 5631032
  have htrace : WordTrace (prefixWord ++ tailWord_5631032) baseStart_5631032 baseEnd_5631032 := by
    simpa [prefixWord, tailWord_5631032, baseEnd_5631032] using wordTrace_append hprefix tailTrace_5631032
  have hstable : (prefixWord ++ tailWord_5631032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631032).length < 2 ^ (prefixWord ++ tailWord_5631032).sum := by decide
  have hdescent : baseEnd_5631032 < baseStart_5631032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631036 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 5]
def baseStart_5631036 : Nat := 118140960795 + 5631036 * 2 ^ 59
def prefixEnd_5631036 : Nat := 4983230072969 + 3 ^ 40 * 5631036 * 2
def baseEnd_5631036 : Nat := 321269783419015086605927

theorem tailTrace_5631036 : CollatzResearch.WordTrace tailWord_5631036 prefixEnd_5631036 321269783419015086605927 := by
  unfold tailWord_5631036
  simp only [CollatzResearch.WordTrace]
  refine ⟨102690377813862875614356481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136920503751817167485808641 102690377813862875614356481)
  ·
    refine ⟨77017783360397156710767361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102690377813862875614356481 77017783360397156710767361)
    ·
      refine ⟨57763337520297867533075521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77017783360397156710767361 57763337520297867533075521)
      ·
        refine ⟨43322503140223400649806641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57763337520297867533075521 43322503140223400649806641)
        ·
          refine ⟨32491877355167550487354981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43322503140223400649806641 32491877355167550487354981)
          ·
            refine ⟨6092227004093915716379059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32491877355167550487354981 6092227004093915716379059)
            ·
              refine ⟨9138340506140873574568589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092227004093915716379059 9138340506140873574568589)
              ·
                refine ⟨3426877689802827590463221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9138340506140873574568589 3426877689802827590463221)
                ·
                  refine ⟨321269783419015086605927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426877689802827590463221 321269783419015086605927)
                  ·
                    rfl

theorem cell23_5631036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_5631036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631036 prefixEnd_5631036 := by exact prefixLift 5631036
  have htrace : WordTrace (prefixWord ++ tailWord_5631036) baseStart_5631036 baseEnd_5631036 := by
    simpa [prefixWord, tailWord_5631036, baseEnd_5631036] using wordTrace_append hprefix tailTrace_5631036
  have hstable : (prefixWord ++ tailWord_5631036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631036).length < 2 ^ (prefixWord ++ tailWord_5631036).sum := by decide
  have hdescent : baseEnd_5631036 < baseStart_5631036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631053 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5631053 : Nat := 118140960795 + 5631053 * 2 ^ 59
def prefixEnd_5631053 : Nat := 4983230072969 + 3 ^ 40 * 5631053 * 2
def baseEnd_5631053 : Nat := 321270753326918023660085

theorem tailTrace_5631053 : CollatzResearch.WordTrace tailWord_5631053 prefixEnd_5631053 321270753326918023660085 := by
  unfold tailWord_5631053
  simp only [CollatzResearch.WordTrace]
  refine ⟨205381375668664163132081813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136920917112442775421387875 205381375668664163132081813)
  ·
    refine ⟨9627251984468632646816335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205381375668664163132081813 9627251984468632646816335)
    ·
      refine ⟨14440877976702948970224503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9627251984468632646816335 14440877976702948970224503)
      ·
        refine ⟨21661316965054423455336755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14440877976702948970224503 21661316965054423455336755)
        ·
          refine ⟨32491975447581635183005133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21661316965054423455336755 32491975447581635183005133)
          ·
            refine ⟨12184490792843113193626925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32491975447581635183005133 12184490792843113193626925)
            ·
              refine ⟨4569184047316167447610097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12184490792843113193626925 4569184047316167447610097)
              ·
                refine ⟨3426888035487125585707573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569184047316167447610097 3426888035487125585707573)
                ·
                  refine ⟨321270753326918023660085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426888035487125585707573 321270753326918023660085)
                  ·
                    rfl

theorem cell23_5631053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5631053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631053 prefixEnd_5631053 := by exact prefixLift 5631053
  have htrace : WordTrace (prefixWord ++ tailWord_5631053) baseStart_5631053 baseEnd_5631053 := by
    simpa [prefixWord, tailWord_5631053, baseEnd_5631053] using wordTrace_append hprefix tailTrace_5631053
  have hstable : (prefixWord ++ tailWord_5631053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631053).length < 2 ^ (prefixWord ++ tailWord_5631053).sum := by decide
  have hdescent : baseEnd_5631053 < baseStart_5631053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631086 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5631086 : Nat := 118140960795 + 5631086 * 2 ^ 59
def prefixEnd_5631086 : Nat := 4983230072969 + 3 ^ 40 * 5631086 * 2
def baseEnd_5631086 : Nat := 2891453724803860583828113

theorem tailTrace_5631086 : CollatzResearch.WordTrace tailWord_5631086 prefixEnd_5631086 2891453724803860583828113 := by
  unfold tailWord_5631086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25672822409693076221004139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136921719518363073178688741 25672822409693076221004139)
  ·
    refine ⟨38509233614539614331506209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25672822409693076221004139 38509233614539614331506209)
    ·
      refine ⟨28881925210904710748629657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38509233614539614331506209 28881925210904710748629657)
      ·
        refine ⟨21661443908178533061472243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28881925210904710748629657 21661443908178533061472243)
        ·
          refine ⟨32492165862267799592208365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21661443908178533061472243 32492165862267799592208365)
          ·
            refine ⟨12184562198350424847078137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32492165862267799592208365 12184562198350424847078137)
            ·
              refine ⟨9138421648762818635308603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12184562198350424847078137 9138421648762818635308603)
              ·
                refine ⟨13707632473144227952962905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9138421648762818635308603 13707632473144227952962905)
                ·
                  refine ⟨10280724354858170964722179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13707632473144227952962905 10280724354858170964722179)
                  ·
                    refine ⟨15421086532287256447083269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10280724354858170964722179 15421086532287256447083269)
                    ·
                      refine ⟨2891453724803860583828113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15421086532287256447083269 2891453724803860583828113)
                      ·
                        rfl

theorem cell23_5631086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5631086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631086 prefixEnd_5631086 := by exact prefixLift 5631086
  have htrace : WordTrace (prefixWord ++ tailWord_5631086) baseStart_5631086 baseEnd_5631086 := by
    simpa [prefixWord, tailWord_5631086, baseEnd_5631086] using wordTrace_append hprefix tailTrace_5631086
  have hstable : (prefixWord ++ tailWord_5631086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631086).length < 2 ^ (prefixWord ++ tailWord_5631086).sum := by decide
  have hdescent : baseEnd_5631086 < baseStart_5631086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631113 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 1, 4]
def baseStart_5631113 : Nat := 118140960795 + 5631113 * 2 ^ 59
def prefixEnd_5631113 : Nat := 4983230072969 + 3 ^ 40 * 5631113 * 2
def baseEnd_5631113 : Nat := 963822529593843992730163

theorem tailTrace_5631113 : CollatzResearch.WordTrace tailWord_5631113 prefixEnd_5631113 963822529593843992730163 := by
  unfold tailWord_5631113
  simp only [CollatzResearch.WordTrace]
  refine ⟨205383564048446793379265993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136922376032297862252843995 205383564048446793379265993)
  ·
    refine ⟨154037673036335095034449495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205383564048446793379265993 154037673036335095034449495)
    ·
      refine ⟨231056509554502642551674243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154037673036335095034449495 231056509554502642551674243)
      ·
        refine ⟨346584764331753963827511365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231056509554502642551674243 346584764331753963827511365)
        ·
          refine ⟨64984643312203868217658381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346584764331753963827511365 64984643312203868217658381)
          ·
            refine ⟨24369241242076450581621893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64984643312203868217658381 24369241242076450581621893)
            ·
              refine ⟨4569232732889334484054105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24369241242076450581621893 4569232732889334484054105)
              ·
                refine ⟨3426924549667000863040579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569232732889334484054105 3426924549667000863040579)
                ·
                  refine ⟨5140386824500501294560869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426924549667000863040579 5140386824500501294560869)
                  ·
                    refine ⟨963822529593843992730163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140386824500501294560869 963822529593843992730163)
                    ·
                      rfl

theorem cell23_5631113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 4].length) (baseStart_5631113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631113 prefixEnd_5631113 := by exact prefixLift 5631113
  have htrace : WordTrace (prefixWord ++ tailWord_5631113) baseStart_5631113 baseEnd_5631113 := by
    simpa [prefixWord, tailWord_5631113, baseEnd_5631113] using wordTrace_append hprefix tailTrace_5631113
  have hstable : (prefixWord ++ tailWord_5631113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631113).length < 2 ^ (prefixWord ++ tailWord_5631113).sum := by decide
  have hdescent : baseEnd_5631113 < baseStart_5631113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631136 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3]
def baseStart_5631136 : Nat := 118140960795 + 5631136 * 2 ^ 59
def prefixEnd_5631136 : Nat := 4983230072969 + 3 ^ 40 * 5631136 * 2
def baseEnd_5631136 : Nat := 2891479398836585388202883

theorem tailTrace_5631136 : CollatzResearch.WordTrace tailWord_5631136 prefixEnd_5631136 2891479398836585388202883 := by
  unfold tailWord_5631136
  simp only [CollatzResearch.WordTrace]
  refine ⟨102692201463681734153676631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136922935284908978871568841 102692201463681734153676631)
  ·
    refine ⟨154038302195522601230514947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102692201463681734153676631 154038302195522601230514947)
    ·
      refine ⟨231057453293283901845772421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154038302195522601230514947 231057453293283901845772421)
      ·
        refine ⟨43323272492490731596082329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231057453293283901845772421 43323272492490731596082329)
        ·
          refine ⟨32492454369368048697061747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43323272492490731596082329 32492454369368048697061747)
          ·
            refine ⟨48738681554052073045592621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32492454369368048697061747 48738681554052073045592621)
            ·
              refine ⟨18277005582769527392097233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48738681554052073045592621 18277005582769527392097233)
              ·
                refine ⟨13707754187077145544072925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18277005582769527392097233 13707754187077145544072925)
                ·
                  refine ⟨5140407820153929579027347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13707754187077145544072925 5140407820153929579027347)
                  ·
                    refine ⟨7710611730230894368541021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140407820153929579027347 7710611730230894368541021)
                    ·
                      refine ⟨2891479398836585388202883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710611730230894368541021 2891479398836585388202883)
                      ·
                        rfl

theorem cell23_5631136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_5631136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631136 prefixEnd_5631136 := by exact prefixLift 5631136
  have htrace : WordTrace (prefixWord ++ tailWord_5631136) baseStart_5631136 baseEnd_5631136 := by
    simpa [prefixWord, tailWord_5631136, baseEnd_5631136] using wordTrace_append hprefix tailTrace_5631136
  have hstable : (prefixWord ++ tailWord_5631136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631136).length < 2 ^ (prefixWord ++ tailWord_5631136).sum := by decide
  have hdescent : baseEnd_5631136 < baseStart_5631136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631179 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3]
def baseStart_5631179 : Nat := 118140960795 + 5631179 * 2 ^ 59
def prefixEnd_5631179 : Nat := 4983230072969 + 3 ^ 40 * 5631179 * 2
def baseEnd_5631179 : Nat := 2891501478504728719965185

theorem tailTrace_5631179 : CollatzResearch.WordTrace tailWord_5631179 prefixEnd_5631179 2891501478504728719965185 := by
  unfold tailWord_5631179
  simp only [CollatzResearch.WordTrace]
  refine ⟨205385971266207686651168591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136923980844138457767445727 205385971266207686651168591)
  ·
    refine ⟨308078956899311529976752887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205385971266207686651168591 308078956899311529976752887)
    ·
      refine ⟨462118435348967294965129331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308078956899311529976752887 462118435348967294965129331)
      ·
        refine ⟨693177653023450942447693997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462118435348967294965129331 693177653023450942447693997)
        ·
          refine ⟨259941619883794103417885249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693177653023450942447693997 259941619883794103417885249)
          ·
            refine ⟨194956214912845577563413937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259941619883794103417885249 194956214912845577563413937)
            ·
              refine ⟨146217161184634183172560453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194956214912845577563413937 146217161184634183172560453)
              ·
                refine ⟨27415717722118909344855085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146217161184634183172560453 27415717722118909344855085)
                ·
                  refine ⟨10280894145794591004320657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27415717722118909344855085 10280894145794591004320657)
                  ·
                    refine ⟨7710670609345943253240493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10280894145794591004320657 7710670609345943253240493)
                    ·
                      refine ⟨2891501478504728719965185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710670609345943253240493 2891501478504728719965185)
                      ·
                        rfl

theorem cell23_5631179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3].length) (baseStart_5631179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631179 prefixEnd_5631179 := by exact prefixLift 5631179
  have htrace : WordTrace (prefixWord ++ tailWord_5631179) baseStart_5631179 baseEnd_5631179 := by
    simpa [prefixWord, tailWord_5631179, baseEnd_5631179] using wordTrace_append hprefix tailTrace_5631179
  have hstable : (prefixWord ++ tailWord_5631179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631179).length < 2 ^ (prefixWord ++ tailWord_5631179).sum := by decide
  have hdescent : baseEnd_5631179 < baseStart_5631179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631190 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5631190 : Nat := 118140960795 + 5631190 * 2 ^ 59
def prefixEnd_5631190 : Nat := 4983230072969 + 3 ^ 40 * 5631190 * 2
def baseEnd_5631190 : Nat := 963835708930642725642545

theorem tailTrace_5631190 : CollatzResearch.WordTrace tailWord_5631190 prefixEnd_5631190 963835708930642725642545 := by
  unfold tailWord_5631190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12836648279322989720613689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136924248312778557019879349 12836648279322989720613689)
  ·
    refine ⟨9627486209492242290460267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12836648279322989720613689 9627486209492242290460267)
    ·
      refine ⟨14441229314238363435690401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9627486209492242290460267 14441229314238363435690401)
      ·
        refine ⟨10830921985678772576767801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14441229314238363435690401 10830921985678772576767801)
        ·
          refine ⟨8123191489259079432575851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10830921985678772576767801 8123191489259079432575851)
          ·
            refine ⟨12184787233888619148863777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8123191489259079432575851 12184787233888619148863777)
            ·
              refine ⟨9138590425416464361647833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12184787233888619148863777 9138590425416464361647833)
              ·
                refine ⟨6853942819062348271235875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9138590425416464361647833 6853942819062348271235875)
                ·
                  refine ⟨10280914228593522406853813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6853942819062348271235875 10280914228593522406853813)
                  ·
                    refine ⟨963835708930642725642545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10280914228593522406853813 963835708930642725642545)
                    ·
                      rfl

theorem cell23_5631190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5631190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631190 prefixEnd_5631190 := by exact prefixLift 5631190
  have htrace : WordTrace (prefixWord ++ tailWord_5631190) baseStart_5631190 baseEnd_5631190 := by
    simpa [prefixWord, tailWord_5631190, baseEnd_5631190] using wordTrace_append hprefix tailTrace_5631190
  have hstable : (prefixWord ++ tailWord_5631190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631190).length < 2 ^ (prefixWord ++ tailWord_5631190).sum := by decide
  have hdescent : baseEnd_5631190 < baseStart_5631190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631199 : List Nat := [1, 1, 2, 3, 2, 1, 6, 7]
def baseStart_5631199 : Nat := 118140960795 + 5631199 * 2 ^ 59
def prefixEnd_5631199 : Nat := 4983230072969 + 3 ^ 40 * 5631199 * 2
def baseEnd_5631199 : Nat := 107093027708067357100559

theorem tailTrace_5631199 : CollatzResearch.WordTrace tailWord_5631199 prefixEnd_5631199 107093027708067357100559 := by
  unfold tailWord_5631199
  simp only [CollatzResearch.WordTrace]
  refine ⟨205386700726135230066896651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136924467150756820044597767 205386700726135230066896651)
  ·
    refine ⟨308080051089202845100344977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205386700726135230066896651 308080051089202845100344977)
    ·
      refine ⟨231060038316902133825258733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308080051089202845100344977 231060038316902133825258733)
      ·
        refine ⟨86647514368838300184472025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231060038316902133825258733 86647514368838300184472025)
        ·
          refine ⟨64985635776628725138354019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86647514368838300184472025 64985635776628725138354019)
          ·
            refine ⟨97478453664943087707531029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64985635776628725138354019 97478453664943087707531029)
            ·
              refine ⟨4569302515544207236290517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97478453664943087707531029 4569302515544207236290517)
              ·
                refine ⟨107093027708067357100559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4569302515544207236290517 107093027708067357100559)
                ·
                  rfl

theorem cell23_5631199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 7].length) (baseStart_5631199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631199 prefixEnd_5631199 := by exact prefixLift 5631199
  have htrace : WordTrace (prefixWord ++ tailWord_5631199) baseStart_5631199 baseEnd_5631199 := by
    simpa [prefixWord, tailWord_5631199, baseEnd_5631199] using wordTrace_append hprefix tailTrace_5631199
  have hstable : (prefixWord ++ tailWord_5631199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631199).length < 2 ^ (prefixWord ++ tailWord_5631199).sum := by decide
  have hdescent : baseEnd_5631199 < baseStart_5631199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631213 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5631213 : Nat := 118140960795 + 5631213 * 2 ^ 59
def prefixEnd_5631213 : Nat := 4983230072969 + 3 ^ 40 * 5631213 * 2
def baseEnd_5631213 : Nat := 2891518936846981586940029

theorem tailTrace_5631213 : CollatzResearch.WordTrace tailWord_5631213 prefixEnd_5631213 2891518936846981586940029 := by
  unfold tailWord_5631213
  simp only [CollatzResearch.WordTrace]
  refine ⟨205387211348084510457906293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136924807565389673638604195 205387211348084510457906293)
  ·
    refine ⟨19255051063882922855428715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205387211348084510457906293 19255051063882922855428715)
    ·
      refine ⟨28882576595824384283143073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19255051063882922855428715 28882576595824384283143073)
      ·
        refine ⟨21661932446868288212357305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28882576595824384283143073 21661932446868288212357305)
        ·
          refine ⟨16246449335151216159267979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21661932446868288212357305 16246449335151216159267979)
          ·
            refine ⟨24369674002726824238901969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16246449335151216159267979 24369674002726824238901969)
            ·
              refine ⟨18277255502045118179176477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24369674002726824238901969 18277255502045118179176477)
              ·
                refine ⟨6853970813266919317191179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18277255502045118179176477 6853970813266919317191179)
                ·
                  refine ⟨10280956219900378975786769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6853970813266919317191179 10280956219900378975786769)
                  ·
                    refine ⟨7710717164925284231840077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10280956219900378975786769 7710717164925284231840077)
                    ·
                      refine ⟨2891518936846981586940029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710717164925284231840077 2891518936846981586940029)
                      ·
                        rfl

theorem cell23_5631213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5631213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631213 prefixEnd_5631213 := by exact prefixLift 5631213
  have htrace : WordTrace (prefixWord ++ tailWord_5631213) baseStart_5631213 baseEnd_5631213 := by
    simpa [prefixWord, tailWord_5631213, baseEnd_5631213] using wordTrace_append hprefix tailTrace_5631213
  have hstable : (prefixWord ++ tailWord_5631213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631213).length < 2 ^ (prefixWord ++ tailWord_5631213).sum := by decide
  have hdescent : baseEnd_5631213 < baseStart_5631213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631226 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_5631226 : Nat := 118140960795 + 5631226 * 2 ^ 59
def prefixEnd_5631226 : Nat := 4983230072969 + 3 ^ 40 * 5631226 * 2
def baseEnd_5631226 : Nat := 2891525612095490036077469

theorem tailTrace_5631226 : CollatzResearch.WordTrace tailWord_5631226 prefixEnd_5631226 2891525612095490036077469 := by
  unfold tailWord_5631226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51346921374259353419532383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136925123664691609118753021 51346921374259353419532383)
  ·
    refine ⟨77020382061389030129298575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51346921374259353419532383 77020382061389030129298575)
    ·
      refine ⟨115530573092083545193947863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77020382061389030129298575 115530573092083545193947863)
      ·
        refine ⟨173295859638125317790921795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115530573092083545193947863 173295859638125317790921795)
        ·
          refine ⟨259943789457187976686382693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173295859638125317790921795 259943789457187976686382693)
          ·
            refine ⟨48739460523222745628696755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259943789457187976686382693 48739460523222745628696755)
            ·
              refine ⟨73109190784834118443045133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48739460523222745628696755 73109190784834118443045133)
              ·
                refine ⟨27415946544312794416141925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73109190784834118443045133 27415946544312794416141925)
                ·
                  refine ⟨5140489977058648953026611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27415946544312794416141925 5140489977058648953026611)
                  ·
                    refine ⟨7710734965587973429539917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140489977058648953026611 7710734965587973429539917)
                    ·
                      refine ⟨2891525612095490036077469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710734965587973429539917 2891525612095490036077469)
                      ·
                        rfl

theorem cell23_5631226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_5631226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631226 prefixEnd_5631226 := by exact prefixLift 5631226
  have htrace : WordTrace (prefixWord ++ tailWord_5631226) baseStart_5631226 baseEnd_5631226 := by
    simpa [prefixWord, tailWord_5631226, baseEnd_5631226] using wordTrace_append hprefix tailTrace_5631226
  have hstable : (prefixWord ++ tailWord_5631226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631226).length < 2 ^ (prefixWord ++ tailWord_5631226).sum := by decide
  have hdescent : baseEnd_5631226 < baseStart_5631226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631243 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 3]
def baseStart_5631243 : Nat := 118140960795 + 5631243 * 2 ^ 59
def prefixEnd_5631243 : Nat := 4983230072969 + 3 ^ 40 * 5631243 * 2
def baseEnd_5631243 : Nat := 2891534341266616469564891

theorem tailTrace_5631243 : CollatzResearch.WordTrace tailWord_5631243 prefixEnd_5631243 2891534341266616469564891 := by
  unfold tailWord_5631243
  simp only [CollatzResearch.WordTrace]
  refine ⟨205388305537975825581498383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136925537025317217054332255 205388305537975825581498383)
  ·
    refine ⟨308082458306963738372247575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205388305537975825581498383 308082458306963738372247575)
    ·
      refine ⟨462123687460445607558371363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308082458306963738372247575 462123687460445607558371363)
      ·
        refine ⟨693185531190668411337557045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462123687460445607558371363 693185531190668411337557045)
        ·
          refine ⟨64986143549125163562895973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 693185531190668411337557045 64986143549125163562895973)
          ·
            refine ⟨12184901915460968168042995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64986143549125163562895973 12184901915460968168042995)
            ·
              refine ⟨18277352873191452252064493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12184901915460968168042995 18277352873191452252064493)
              ·
                refine ⟨6854007327446794594524185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18277352873191452252064493 6854007327446794594524185)
                ·
                  refine ⟨5140505495585095945893139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854007327446794594524185 5140505495585095945893139)
                  ·
                    refine ⟨7710758243377643918839709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140505495585095945893139 7710758243377643918839709)
                    ·
                      refine ⟨2891534341266616469564891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710758243377643918839709 2891534341266616469564891)
                      ·
                        rfl

theorem cell23_5631243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 3].length) (baseStart_5631243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631243 prefixEnd_5631243 := by exact prefixLift 5631243
  have htrace : WordTrace (prefixWord ++ tailWord_5631243) baseStart_5631243 baseEnd_5631243 := by
    simpa [prefixWord, tailWord_5631243, baseEnd_5631243] using wordTrace_append hprefix tailTrace_5631243
  have hstable : (prefixWord ++ tailWord_5631243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631243).length < 2 ^ (prefixWord ++ tailWord_5631243).sum := by decide
  have hdescent : baseEnd_5631243 < baseStart_5631243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631277 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5631277 : Nat := 118140960795 + 5631277 * 2 ^ 59
def prefixEnd_5631277 : Nat := 4983230072969 + 3 ^ 40 * 5631277 * 2
def baseEnd_5631277 : Nat := 2891551799608869336539735

theorem tailTrace_5631277 : CollatzResearch.WordTrace tailWord_5631277 prefixEnd_5631277 2891551799608869336539735 := by
  unfold tailWord_5631277
  simp only [CollatzResearch.WordTrace]
  refine ⟨205389545619852649388236085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136926363746568432925490723 205389545619852649388236085)
  ·
    refine ⟨19255269901861185880147133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205389545619852649388236085 19255269901861185880147133)
    ·
      refine ⟨7220726213197944705055175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19255269901861185880147133 7220726213197944705055175)
      ·
        refine ⟨10831089319796917057582763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220726213197944705055175 10831089319796917057582763)
        ·
          refine ⟨16246633979695375586374145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10831089319796917057582763 16246633979695375586374145)
          ·
            refine ⟨12184975484771531689780609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16246633979695375586374145 12184975484771531689780609)
            ·
              refine ⟨9138731613578648767335457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12184975484771531689780609 9138731613578648767335457)
              ·
                refine ⟨6854048710183986575501593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9138731613578648767335457 6854048710183986575501593)
                ·
                  refine ⟨5140536532637989931626195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854048710183986575501593 5140536532637989931626195)
                  ·
                    refine ⟨7710804798956984897439293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140536532637989931626195 7710804798956984897439293)
                    ·
                      refine ⟨2891551799608869336539735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710804798956984897439293 2891551799608869336539735)
                      ·
                        rfl

theorem cell23_5631277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5631277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631277 prefixEnd_5631277 := by exact prefixLift 5631277
  have htrace : WordTrace (prefixWord ++ tailWord_5631277) baseStart_5631277 baseEnd_5631277 := by
    simpa [prefixWord, tailWord_5631277, baseEnd_5631277] using wordTrace_append hprefix tailTrace_5631277
  have hstable : (prefixWord ++ tailWord_5631277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631277).length < 2 ^ (prefixWord ++ tailWord_5631277).sum := by decide
  have hdescent : baseEnd_5631277 < baseStart_5631277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631279 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_5631279 : Nat := 118140960795 + 5631279 * 2 ^ 59
def prefixEnd_5631279 : Nat := 4983230072969 + 3 ^ 40 * 5631279 * 2
def baseEnd_5631279 : Nat := 2891552826570178328714725

theorem tailTrace_5631279 : CollatzResearch.WordTrace tailWord_5631279 prefixEnd_5631279 2891552826570178328714725 := by
  unfold tailWord_5631279
  simp only [CollatzResearch.WordTrace]
  refine ⟨205389618565845403729808891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136926412377230269153205927 205389618565845403729808891)
  ·
    refine ⟨308084427848768105594713337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205389618565845403729808891 308084427848768105594713337)
    ·
      refine ⟨231063320886576079196035003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308084427848768105594713337 231063320886576079196035003)
      ·
        refine ⟨346594981329864118794052505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231063320886576079196035003 346594981329864118794052505)
        ·
          refine ⟨259946235997398089095539379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346594981329864118794052505 259946235997398089095539379)
          ·
            refine ⟨389919353996097133643309069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259946235997398089095539379 389919353996097133643309069)
            ·
              refine ⟨146219757748536425116240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389919353996097133643309069 146219757748536425116240901)
              ·
                refine ⟨27416204577850579709295169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146219757748536425116240901 27416204577850579709295169)
                ·
                  refine ⟨20562153433387934781971377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27416204577850579709295169 20562153433387934781971377)
                  ·
                    refine ⟨15421615075040951086478533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20562153433387934781971377 15421615075040951086478533)
                    ·
                      refine ⟨2891552826570178328714725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15421615075040951086478533 2891552826570178328714725)
                      ·
                        rfl

theorem cell23_5631279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_5631279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631279 prefixEnd_5631279 := by exact prefixLift 5631279
  have htrace : WordTrace (prefixWord ++ tailWord_5631279) baseStart_5631279 baseEnd_5631279 := by
    simpa [prefixWord, tailWord_5631279, baseEnd_5631279] using wordTrace_append hprefix tailTrace_5631279
  have hstable : (prefixWord ++ tailWord_5631279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631279).length < 2 ^ (prefixWord ++ tailWord_5631279).sum := by decide
  have hdescent : baseEnd_5631279 < baseStart_5631279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631293 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_5631293 : Nat := 118140960795 + 5631293 * 2 ^ 59
def prefixEnd_5631293 : Nat := 4983230072969 + 3 ^ 40 * 5631293 * 2
def baseEnd_5631293 : Nat := 963853338433113757979887

theorem tailTrace_5631293 : CollatzResearch.WordTrace tailWord_5631293 prefixEnd_5631293 963853338433113757979887 := by
  unfold tailWord_5631293
  simp only [CollatzResearch.WordTrace]
  refine ⟨205390129187794684120818533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136926752791863122747212355 205390129187794684120818533)
  ·
    refine ⟨38510649222711503272653475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205390129187794684120818533 38510649222711503272653475)
    ·
      refine ⟨57765973834067254908980213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38510649222711503272653475 57765973834067254908980213)
      ·
        refine ⟨5415560046943805147716895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57765973834067254908980213 5415560046943805147716895)
        ·
          refine ⟨8123340070415707721575343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415560046943805147716895 8123340070415707721575343)
          ·
            refine ⟨12185010105623561582363015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8123340070415707721575343 12185010105623561582363015)
            ·
              refine ⟨18277515158435342373544523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12185010105623561582363015 18277515158435342373544523)
              ·
                refine ⟨27416272737653013560316785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18277515158435342373544523 27416272737653013560316785)
                ·
                  refine ⟨20562204553239760170237589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27416272737653013560316785 20562204553239760170237589)
                  ·
                    refine ⟨963853338433113757979887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20562204553239760170237589 963853338433113757979887)
                    ·
                      rfl

theorem cell23_5631293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_5631293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631293 prefixEnd_5631293 := by exact prefixLift 5631293
  have htrace : WordTrace (prefixWord ++ tailWord_5631293) baseStart_5631293 baseEnd_5631293 := by
    simpa [prefixWord, tailWord_5631293, baseEnd_5631293] using wordTrace_append hprefix tailTrace_5631293
  have hstable : (prefixWord ++ tailWord_5631293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631293).length < 2 ^ (prefixWord ++ tailWord_5631293).sum := by decide
  have hdescent : baseEnd_5631293 < baseStart_5631293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631300 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5631300 : Nat := 118140960795 + 5631300 * 2 ^ 59
def prefixEnd_5631300 : Nat := 4983230072969 + 3 ^ 40 * 5631300 * 2
def baseEnd_5631300 : Nat := 2891563609663922746552129

theorem tailTrace_5631300 : CollatzResearch.WordTrace tailWord_5631300 prefixEnd_5631300 2891563609663922746552129 := by
  unfold tailWord_5631300
  simp only [CollatzResearch.WordTrace]
  refine ⟨102695192249384662158161677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136926922999179549544215569 102695192249384662158161677)
  ·
    refine ⟨38510697093519248309310629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102695192249384662158161677 38510697093519248309310629)
    ·
      refine ⟨7220755705034859057995743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38510697093519248309310629 7220755705034859057995743)
      ·
        refine ⟨10831133557552288586993615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220755705034859057995743 10831133557552288586993615)
        ·
          refine ⟨16246700336328432880490423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10831133557552288586993615 16246700336328432880490423)
          ·
            refine ⟨24370050504492649320735635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16246700336328432880490423 24370050504492649320735635)
            ·
              refine ⟨36555075756738973981103453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24370050504492649320735635 36555075756738973981103453)
              ·
                refine ⟨13708153408777115242913795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36555075756738973981103453 13708153408777115242913795)
                ·
                  refine ⟨20562230113165672864370693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13708153408777115242913795 20562230113165672864370693)
                  ·
                    refine ⟨3855418146218563662069505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20562230113165672864370693 3855418146218563662069505)
                    ·
                      refine ⟨2891563609663922746552129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855418146218563662069505 2891563609663922746552129)
                      ·
                        rfl

theorem cell23_5631300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5631300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631300 prefixEnd_5631300 := by exact prefixLift 5631300
  have htrace : WordTrace (prefixWord ++ tailWord_5631300) baseStart_5631300 baseEnd_5631300 := by
    simpa [prefixWord, tailWord_5631300, baseEnd_5631300] using wordTrace_append hprefix tailTrace_5631300
  have hstable : (prefixWord ++ tailWord_5631300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631300).length < 2 ^ (prefixWord ++ tailWord_5631300).sum := by decide
  have hdescent : baseEnd_5631300 < baseStart_5631300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631316 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_5631316 : Nat := 118140960795 + 5631316 * 2 ^ 59
def prefixEnd_5631316 : Nat := 4983230072969 + 3 ^ 40 * 5631316 * 2
def baseEnd_5631316 : Nat := 2891571825354394683952055

theorem tailTrace_5631316 : CollatzResearch.WordTrace tailWord_5631316 prefixEnd_5631316 2891571825354394683952055 := by
  unfold tailWord_5631316
  simp only [CollatzResearch.WordTrace]
  refine ⟨102695484033355679524452901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136927312044474239365937201 102695484033355679524452901)
  ·
    refine ⟨19255403256254189910834919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102695484033355679524452901 19255403256254189910834919)
    ·
      refine ⟨28883104884381284866252379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19255403256254189910834919 28883104884381284866252379)
      ·
        refine ⟨43324657326571927299378569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28883104884381284866252379 43324657326571927299378569)
        ·
          refine ⟨32493492994928945474533927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43324657326571927299378569 32493492994928945474533927)
          ·
            refine ⟨48740239492393418211800891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32493492994928945474533927 48740239492393418211800891)
            ·
              refine ⟨73110359238590127317701337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48740239492393418211800891 73110359238590127317701337)
              ·
                refine ⟨54832769428942595488276003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73110359238590127317701337 54832769428942595488276003)
                ·
                  refine ⟨82249154143413893232414005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54832769428942595488276003 82249154143413893232414005)
                  ·
                    refine ⟨7710858200945052490538813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82249154143413893232414005 7710858200945052490538813)
                    ·
                      refine ⟨2891571825354394683952055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7710858200945052490538813 2891571825354394683952055)
                      ·
                        rfl

theorem cell23_5631316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_5631316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631316 prefixEnd_5631316 := by exact prefixLift 5631316
  have htrace : WordTrace (prefixWord ++ tailWord_5631316) baseStart_5631316 baseEnd_5631316 := by
    simpa [prefixWord, tailWord_5631316, baseEnd_5631316] using wordTrace_append hprefix tailTrace_5631316
  have hstable : (prefixWord ++ tailWord_5631316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631316).length < 2 ^ (prefixWord ++ tailWord_5631316).sum := by decide
  have hdescent : baseEnd_5631316 < baseStart_5631316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631329 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5631329 : Nat := 118140960795 + 5631329 * 2 ^ 59
def prefixEnd_5631329 : Nat := 4983230072969 + 3 ^ 40 * 5631329 * 2
def baseEnd_5631329 : Nat := 2891578500602903133089495

theorem tailTrace_5631329 : CollatzResearch.WordTrace tailWord_5631329 prefixEnd_5631329 2891578500602903133089495 := by
  unfold tailWord_5631329
  simp only [CollatzResearch.WordTrace]
  refine ⟨205391442215664262269129041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136927628143776174846086027 205391442215664262269129041)
  ·
    refine ⟨154043581661748196701846781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205391442215664262269129041 154043581661748196701846781)
    ·
      refine ⟨57766343123155573763192543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154043581661748196701846781 57766343123155573763192543)
      ·
        refine ⟨86649514684733360644788815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57766343123155573763192543 86649514684733360644788815)
        ·
          refine ⟨129974272027100040967183223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86649514684733360644788815 129974272027100040967183223)
          ·
            refine ⟨194961408040650061450774835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129974272027100040967183223 194961408040650061450774835)
            ·
              refine ⟨292442112060975092176162253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194961408040650061450774835 292442112060975092176162253)
              ·
                refine ⟨109665792022865659566060845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292442112060975092176162253 109665792022865659566060845)
                ·
                  refine ⟨41124672008574622337272817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109665792022865659566060845 41124672008574622337272817)
                  ·
                    refine ⟨30843504006430966752954613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41124672008574622337272817 30843504006430966752954613)
                    ·
                      refine ⟨2891578500602903133089495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30843504006430966752954613 2891578500602903133089495)
                      ·
                        rfl

theorem cell23_5631329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5631329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631329 prefixEnd_5631329 := by exact prefixLift 5631329
  have htrace : WordTrace (prefixWord ++ tailWord_5631329) baseStart_5631329 baseEnd_5631329 := by
    simpa [prefixWord, tailWord_5631329, baseEnd_5631329] using wordTrace_append hprefix tailTrace_5631329
  have hstable : (prefixWord ++ tailWord_5631329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631329).length < 2 ^ (prefixWord ++ tailWord_5631329).sum := by decide
  have hdescent : baseEnd_5631329 < baseStart_5631329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631339 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_5631339 : Nat := 118140960795 + 5631339 * 2 ^ 59
def prefixEnd_5631339 : Nat := 4983230072969 + 3 ^ 40 * 5631339 * 2
def baseEnd_5631339 : Nat := 2891583635409448093964449

theorem tailTrace_5631339 : CollatzResearch.WordTrace tailWord_5631339 prefixEnd_5631339 2891583635409448093964449 := by
  unfold tailWord_5631339
  simp only [CollatzResearch.WordTrace]
  refine ⟨205391806945628033976993071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136927871297085355984662047 205391806945628033976993071)
  ·
    refine ⟨308087710418442050965489607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205391806945628033976993071 308087710418442050965489607)
    ·
      refine ⟨462131565627663076448234411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308087710418442050965489607 462131565627663076448234411)
      ·
        refine ⟨693197348441494614672351617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462131565627663076448234411 693197348441494614672351617)
        ·
          refine ⟨519898011331120961004263713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693197348441494614672351617 519898011331120961004263713)
          ·
            refine ⟨389923508498340720753197785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519898011331120961004263713 389923508498340720753197785)
            ·
              refine ⟨292442631373755540564898339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389923508498340720753197785 292442631373755540564898339)
              ·
                refine ⟨438663947060633310847347509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292442631373755540564898339 438663947060633310847347509)
                ·
                  refine ⟨41124745036934372891938829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438663947060633310847347509 41124745036934372891938829)
                  ·
                    refine ⟨15421779388850389834477061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41124745036934372891938829 15421779388850389834477061)
                    ·
                      refine ⟨2891583635409448093964449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15421779388850389834477061 2891583635409448093964449)
                      ·
                        rfl

theorem cell23_5631339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_5631339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631339 prefixEnd_5631339 := by exact prefixLift 5631339
  have htrace : WordTrace (prefixWord ++ tailWord_5631339) baseStart_5631339 baseEnd_5631339 := by
    simpa [prefixWord, tailWord_5631339, baseEnd_5631339] using wordTrace_append hprefix tailTrace_5631339
  have hstable : (prefixWord ++ tailWord_5631339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631339).length < 2 ^ (prefixWord ++ tailWord_5631339).sum := by decide
  have hdescent : baseEnd_5631339 < baseStart_5631339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631396 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 6]
def baseStart_5631396 : Nat := 118140960795 + 5631396 * 2 ^ 59
def prefixEnd_5631396 : Nat := 4983230072969 + 3 ^ 40 * 5631396 * 2
def baseEnd_5631396 : Nat := 321290322645194930105743

theorem tailTrace_5631396 : CollatzResearch.WordTrace tailWord_5631396 prefixEnd_5631396 321290322645194930105743 := by
  unfold tailWord_5631396
  simp only [CollatzResearch.WordTrace]
  refine ⟨102696942953210766355909021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136929257270947688474545361 102696942953210766355909021)
  ·
    refine ⟨38511353607454037383465883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102696942953210766355909021 38511353607454037383465883)
    ·
      refine ⟨57767030411181056075198825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38511353607454037383465883 57767030411181056075198825)
      ·
        refine ⟨43325272808385792056399119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57767030411181056075198825 43325272808385792056399119)
        ·
          refine ⟨64987909212578688084598679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43325272808385792056399119 64987909212578688084598679)
          ·
            refine ⟨97481863818868032126898019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64987909212578688084598679 97481863818868032126898019)
            ·
              refine ⟨146222795728302048190347029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97481863818868032126898019 146222795728302048190347029)
              ·
                refine ⟨6854193549764158508922517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146222795728302048190347029 6854193549764158508922517)
                ·
                  refine ⟨321290322645194930105743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6854193549764158508922517 321290322645194930105743)
                  ·
                    rfl

theorem cell23_5631396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_5631396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631396 prefixEnd_5631396 := by exact prefixLift 5631396
  have htrace : WordTrace (prefixWord ++ tailWord_5631396) baseStart_5631396 baseEnd_5631396 := by
    simpa [prefixWord, tailWord_5631396, baseEnd_5631396] using wordTrace_append hprefix tailTrace_5631396
  have hstable : (prefixWord ++ tailWord_5631396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631396).length < 2 ^ (prefixWord ++ tailWord_5631396).sum := by decide
  have hdescent : baseEnd_5631396 < baseStart_5631396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631413 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 6]
def baseStart_5631413 : Nat := 118140960795 + 5631413 * 2 ^ 59
def prefixEnd_5631413 : Nat := 4983230072969 + 3 ^ 40 * 5631413 * 2
def baseEnd_5631413 : Nat := 321291292553097867159901

theorem tailTrace_5631413 : CollatzResearch.WordTrace tailWord_5631413 prefixEnd_5631413 321291292553097867159901 := by
  unfold tailWord_5631413
  simp only [CollatzResearch.WordTrace]
  refine ⟨205394505947359944615186893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136929670631573296410124595 205394505947359944615186893)
  ·
    refine ⟨77022939730259979230695085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205394505947359944615186893 77022939730259979230695085)
    ·
      refine ⟨28883602398847492211510657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77022939730259979230695085 28883602398847492211510657)
      ·
        refine ⟨21662701799135619158632993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28883602398847492211510657 21662701799135619158632993)
        ·
          refine ⟨16247026349351714368974745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21662701799135619158632993 16247026349351714368974745)
          ·
            refine ⟨12185269762013785776731059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16247026349351714368974745 12185269762013785776731059)
            ·
              refine ⟨18277904643020678665096589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12185269762013785776731059 18277904643020678665096589)
              ·
                refine ⟨6854214241132754499411221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18277904643020678665096589 6854214241132754499411221)
                ·
                  refine ⟨321291292553097867159901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6854214241132754499411221 321291292553097867159901)
                  ·
                    rfl

theorem cell23_5631413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_5631413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631413 prefixEnd_5631413 := by exact prefixLift 5631413
  have htrace : WordTrace (prefixWord ++ tailWord_5631413) baseStart_5631413 baseEnd_5631413 := by
    simpa [prefixWord, tailWord_5631413, baseEnd_5631413] using wordTrace_append hprefix tailTrace_5631413
  have hstable : (prefixWord ++ tailWord_5631413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631413).length < 2 ^ (prefixWord ++ tailWord_5631413).sum := by decide
  have hdescent : baseEnd_5631413 < baseStart_5631413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631423 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 3]
def baseStart_5631423 : Nat := 118140960795 + 5631423 * 2 ^ 59
def prefixEnd_5631423 : Nat := 4983230072969 + 3 ^ 40 * 5631423 * 2
def baseEnd_5631423 : Nat := 2891626767784425765314063

theorem tailTrace_5631423 : CollatzResearch.WordTrace tailWord_5631423 prefixEnd_5631423 2891626767784425765314063 := by
  unfold tailWord_5631423
  simp only [CollatzResearch.WordTrace]
  refine ⟨205394870677323716323050923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136929913784882477548700615 205394870677323716323050923)
  ·
    refine ⟨308092306015985574484576385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205394870677323716323050923 308092306015985574484576385)
    ·
      refine ⟨231069229511989180863432289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308092306015985574484576385 231069229511989180863432289)
      ·
        refine ⟨173301922133991885647574217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231069229511989180863432289 173301922133991885647574217)
        ·
          refine ⟨129976441600493914235680663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173301922133991885647574217 129976441600493914235680663)
          ·
            refine ⟨194964662400740871353520995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129976441600493914235680663 194964662400740871353520995)
            ·
              refine ⟨292446993601111307030281493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194964662400740871353520995 292446993601111307030281493)
              ·
                refine ⟨13708452825052092517044445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292446993601111307030281493 13708452825052092517044445)
                ·
                  refine ⟨5140669809394534693891667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13708452825052092517044445 5140669809394534693891667)
                  ·
                    refine ⟨7711004714091802040837501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140669809394534693891667 7711004714091802040837501)
                    ·
                      refine ⟨2891626767784425765314063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711004714091802040837501 2891626767784425765314063)
                      ·
                        rfl

theorem cell23_5631423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_5631423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631423 prefixEnd_5631423 := by exact prefixLift 5631423
  have htrace : WordTrace (prefixWord ++ tailWord_5631423) baseStart_5631423 baseEnd_5631423 := by
    simpa [prefixWord, tailWord_5631423, baseEnd_5631423] using wordTrace_append hprefix tailTrace_5631423
  have hstable : (prefixWord ++ tailWord_5631423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631423).length < 2 ^ (prefixWord ++ tailWord_5631423).sum := by decide
  have hdescent : baseEnd_5631423 < baseStart_5631423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631450 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_5631450 : Nat := 118140960795 + 5631450 * 2 ^ 59
def prefixEnd_5631450 : Nat := 4983230072969 + 3 ^ 40 * 5631450 * 2
def baseEnd_5631450 : Nat := 2891640631762097159676439

theorem tailTrace_5631450 : CollatzResearch.WordTrace tailWord_5631450 prefixEnd_5631450 2891640631762097159676439 := by
  unfold tailWord_5631450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51348963862056474983570951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136930570298817266622855869 51348963862056474983570951)
  ·
    refine ⟨77023445793084712475356427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51348963862056474983570951 77023445793084712475356427)
    ·
      refine ⟨115535168689627068713034641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77023445793084712475356427 115535168689627068713034641)
      ·
        refine ⟨86651376517220301534775981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115535168689627068713034641 86651376517220301534775981)
        ·
          refine ⟨32494266193957613075540993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86651376517220301534775981 32494266193957613075540993)
          ·
            refine ⟨24370699645468209806655745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32494266193957613075540993 24370699645468209806655745)
            ·
              refine ⟨18278024734101157354991809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24370699645468209806655745 18278024734101157354991809)
              ·
                refine ⟨13708518550575868016243857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18278024734101157354991809 13708518550575868016243857)
                ·
                  refine ⟨10281388912931901012182893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13708518550575868016243857 10281388912931901012182893)
                  ·
                    refine ⟨3855520842349462879568585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10281388912931901012182893 3855520842349462879568585)
                    ·
                      refine ⟨2891640631762097159676439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855520842349462879568585 2891640631762097159676439)
                      ·
                        rfl

theorem cell23_5631450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_5631450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631450 prefixEnd_5631450 := by exact prefixLift 5631450
  have htrace : WordTrace (prefixWord ++ tailWord_5631450) baseStart_5631450 baseEnd_5631450 := by
    simpa [prefixWord, tailWord_5631450, baseEnd_5631450] using wordTrace_append hprefix tailTrace_5631450
  have hstable : (prefixWord ++ tailWord_5631450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631450).length < 2 ^ (prefixWord ++ tailWord_5631450).sum := by decide
  have hdescent : baseEnd_5631450 < baseStart_5631450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631457 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_5631457 : Nat := 118140960795 + 5631457 * 2 ^ 59
def prefixEnd_5631457 : Nat := 4983230072969 + 3 ^ 40 * 5631457 * 2
def baseEnd_5631457 : Nat := 2891644226126678632288907

theorem tailTrace_5631457 : CollatzResearch.WordTrace tailWord_5631457 prefixEnd_5631457 2891644226126678632288907 := by
  unfold tailWord_5631457
  simp only [CollatzResearch.WordTrace]
  refine ⟨205396110759200540129788625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136930740506133693419859083 205396110759200540129788625)
  ·
    refine ⟨154047083069400405097341469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205396110759200540129788625 154047083069400405097341469)
    ·
      refine ⟨57767656151025151911503051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154047083069400405097341469 57767656151025151911503051)
      ·
        refine ⟨86651484226537727867254577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57767656151025151911503051 86651484226537727867254577)
        ·
          refine ⟨64988613169903295900440933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86651484226537727867254577 64988613169903295900440933)
          ·
            refine ⟨12185364969356867981332675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64988613169903295900440933 12185364969356867981332675)
            ·
              refine ⟨18278047454035301971999013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12185364969356867981332675 18278047454035301971999013)
              ·
                refine ⟨3427133897631619119749815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18278047454035301971999013 3427133897631619119749815)
                ·
                  refine ⟨5140700846447428679624723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427133897631619119749815 5140700846447428679624723)
                  ·
                    refine ⟨7711051269671143019437085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140700846447428679624723 7711051269671143019437085)
                    ·
                      refine ⟨2891644226126678632288907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711051269671143019437085 2891644226126678632288907)
                      ·
                        rfl

theorem cell23_5631457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_5631457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631457 prefixEnd_5631457 := by exact prefixLift 5631457
  have htrace : WordTrace (prefixWord ++ tailWord_5631457) baseStart_5631457 baseEnd_5631457 := by
    simpa [prefixWord, tailWord_5631457, baseEnd_5631457] using wordTrace_append hprefix tailTrace_5631457
  have hstable : (prefixWord ++ tailWord_5631457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631457).length < 2 ^ (prefixWord ++ tailWord_5631457).sum := by decide
  have hdescent : baseEnd_5631457 < baseStart_5631457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631463 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5631463 : Nat := 118140960795 + 5631463 * 2 ^ 59
def prefixEnd_5631463 : Nat := 4983230072969 + 3 ^ 40 * 5631463 * 2
def baseEnd_5631463 : Nat := 2891647307010605608813879

theorem tailTrace_5631463 : CollatzResearch.WordTrace tailWord_5631463 prefixEnd_5631463 2891647307010605608813879 := by
  unfold tailWord_5631463
  simp only [CollatzResearch.WordTrace]
  refine ⟨205396329597178803154507043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136930886398119202103004695 205396329597178803154507043)
  ·
    refine ⟨308094494395768204731760565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205396329597178803154507043 308094494395768204731760565)
    ·
      refine ⟨28883858849603269193602553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308094494395768204731760565 28883858849603269193602553)
      ·
        refine ⟨21662894137202451895201915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28883858849603269193602553 21662894137202451895201915)
        ·
          refine ⟨32494341205803677842802873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21662894137202451895201915 32494341205803677842802873)
          ·
            refine ⟨24370755904352758382102155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32494341205803677842802873 24370755904352758382102155)
            ·
              refine ⟨36556133856529137573153233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24370755904352758382102155 36556133856529137573153233)
              ·
                refine ⟨27417100392396853179864925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36556133856529137573153233 27417100392396853179864925)
                ·
                  refine ⟨10281412647148819942449347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27417100392396853179864925 10281412647148819942449347)
                  ·
                    refine ⟨15422118970723229913674021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10281412647148819942449347 15422118970723229913674021)
                    ·
                      refine ⟨2891647307010605608813879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15422118970723229913674021 2891647307010605608813879)
                      ·
                        rfl

theorem cell23_5631463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5631463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631463 prefixEnd_5631463 := by exact prefixLift 5631463
  have htrace : WordTrace (prefixWord ++ tailWord_5631463) baseStart_5631463 baseEnd_5631463 := by
    simpa [prefixWord, tailWord_5631463, baseEnd_5631463] using wordTrace_append hprefix tailTrace_5631463
  have hstable : (prefixWord ++ tailWord_5631463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631463).length < 2 ^ (prefixWord ++ tailWord_5631463).sum := by decide
  have hdescent : baseEnd_5631463 < baseStart_5631463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631473 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_5631473 : Nat := 118140960795 + 5631473 * 2 ^ 59
def prefixEnd_5631473 : Nat := 4983230072969 + 3 ^ 40 * 5631473 * 2
def baseEnd_5631473 : Nat := 963884147272383523229611

theorem tailTrace_5631473 : CollatzResearch.WordTrace tailWord_5631473 prefixEnd_5631473 963884147272383523229611 := by
  unfold tailWord_5631473
  simp only [CollatzResearch.WordTrace]
  refine ⟨205396694327142574862371073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136931129551428383241580715 205396694327142574862371073)
  ·
    refine ⟨154047520745356931146778305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205396694327142574862371073 154047520745356931146778305)
    ·
      refine ⟨115535640559017698360083729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154047520745356931146778305 115535640559017698360083729)
      ·
        refine ⟨86651730419263273770062797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115535640559017698360083729 86651730419263273770062797)
        ·
          refine ⟨32494398907223727663773549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86651730419263273770062797 32494398907223727663773549)
          ·
            refine ⟨12185399590208897873915081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32494398907223727663773549 12185399590208897873915081)
            ·
              refine ⟨9139049692656673405436311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12185399590208897873915081 9139049692656673405436311)
              ·
                refine ⟨13708574538985010108154467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139049692656673405436311 13708574538985010108154467)
                ·
                  refine ⟨20562861808477515162231701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13708574538985010108154467 20562861808477515162231701)
                  ·
                    refine ⟨963884147272383523229611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20562861808477515162231701 963884147272383523229611)
                    ·
                      rfl

theorem cell23_5631473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_5631473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631473 prefixEnd_5631473 := by exact prefixLift 5631473
  have htrace : WordTrace (prefixWord ++ tailWord_5631473) baseStart_5631473 baseEnd_5631473 := by
    simpa [prefixWord, tailWord_5631473, baseEnd_5631473] using wordTrace_append hprefix tailTrace_5631473
  have hstable : (prefixWord ++ tailWord_5631473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631473).length < 2 ^ (prefixWord ++ tailWord_5631473).sum := by decide
  have hdescent : baseEnd_5631473 < baseStart_5631473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631480 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_5631480 : Nat := 118140960795 + 5631480 * 2 ^ 59
def prefixEnd_5631480 : Nat := 4983230072969 + 3 ^ 40 * 5631480 * 2
def baseEnd_5631480 : Nat := 2891656036181732042301301

theorem tailTrace_5631480 : CollatzResearch.WordTrace tailWord_5631480 prefixEnd_5631480 2891656036181732042301301 := by
  unfold tailWord_5631480
  simp only [CollatzResearch.WordTrace]
  refine ⟨102698474819058607528937947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136931299758744810038583929 102698474819058607528937947)
  ·
    refine ⟨154047712228587911293406921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102698474819058607528937947 154047712228587911293406921)
    ·
      refine ⟨115535784171440933470055191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154047712228587911293406921 115535784171440933470055191)
      ·
        refine ⟨173303676257161400205082787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115535784171440933470055191 173303676257161400205082787)
        ·
          refine ⟨259955514385742100307624181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173303676257161400205082787 259955514385742100307624181)
          ·
            refine ⟨24370829473663321903839767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 259955514385742100307624181 24370829473663321903839767)
            ·
              refine ⟨36556244210494982855759651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24370829473663321903839767 36556244210494982855759651)
              ·
                refine ⟨54834366315742474283639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36556244210494982855759651 54834366315742474283639477)
                ·
                  refine ⟨5140721842100856964091201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54834366315742474283639477 5140721842100856964091201)
                  ·
                    refine ⟨3855541381575642723068401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5140721842100856964091201 3855541381575642723068401)
                    ·
                      refine ⟨2891656036181732042301301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855541381575642723068401 2891656036181732042301301)
                      ·
                        rfl

theorem cell23_5631480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_5631480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631480 prefixEnd_5631480 := by exact prefixLift 5631480
  have htrace : WordTrace (prefixWord ++ tailWord_5631480) baseStart_5631480 baseEnd_5631480 := by
    simpa [prefixWord, tailWord_5631480, baseEnd_5631480] using wordTrace_append hprefix tailTrace_5631480
  have hstable : (prefixWord ++ tailWord_5631480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631480).length < 2 ^ (prefixWord ++ tailWord_5631480).sum := by decide
  have hdescent : baseEnd_5631480 < baseStart_5631480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631490 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5631490 : Nat := 118140960795 + 5631490 * 2 ^ 59
def prefixEnd_5631490 : Nat := 4983230072969 + 3 ^ 40 * 5631490 * 2
def baseEnd_5631490 : Nat := 963887056996092334392085

theorem tailTrace_5631490 : CollatzResearch.WordTrace tailWord_5631490 prefixEnd_5631490 963887056996092334392085 := by
  unfold tailWord_5631490
  simp only [CollatzResearch.WordTrace]
  refine ⟨51349328592020246691434981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136931542912053991177159949 51349328592020246691434981)
  ·
    refine ⟨9627999111003796254644059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51349328592020246691434981 9627999111003796254644059)
    ·
      refine ⟨14441998666505694381966089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9627999111003796254644059 14441998666505694381966089)
      ·
        refine ⟨10831498999879270786474567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14441998666505694381966089 10831498999879270786474567)
        ·
          refine ⟨16247248499818906179711851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10831498999879270786474567 16247248499818906179711851)
          ·
            refine ⟨24370872749728359269567777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16247248499818906179711851 24370872749728359269567777)
            ·
              refine ⟨18278154562296269452175833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24370872749728359269567777 18278154562296269452175833)
              ·
                refine ⟨13708615921722202089131875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18278154562296269452175833 13708615921722202089131875)
                ·
                  refine ⟨20562923882583303133697813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13708615921722202089131875 20562923882583303133697813)
                  ·
                    refine ⟨963887056996092334392085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20562923882583303133697813 963887056996092334392085)
                    ·
                      rfl

theorem cell23_5631490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5631490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631490 prefixEnd_5631490 := by exact prefixLift 5631490
  have htrace : WordTrace (prefixWord ++ tailWord_5631490) baseStart_5631490 baseEnd_5631490 := by
    simpa [prefixWord, tailWord_5631490, baseEnd_5631490] using wordTrace_append hprefix tailTrace_5631490
  have hstable : (prefixWord ++ tailWord_5631490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631490).length < 2 ^ (prefixWord ++ tailWord_5631490).sum := by decide
  have hdescent : baseEnd_5631490 < baseStart_5631490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631548 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_5631548 : Nat := 118140960795 + 5631548 * 2 ^ 59
def prefixEnd_5631548 : Nat := 4983230072969 + 3 ^ 40 * 5631548 * 2
def baseEnd_5631548 : Nat := 2891690952866237776250989

theorem tailTrace_5631548 : CollatzResearch.WordTrace tailWord_5631548 prefixEnd_5631548 2891690952866237776250989 := by
  unfold tailWord_5631548
  simp only [CollatzResearch.WordTrace]
  refine ⟨102699714900935431335675649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136932953201247241780900865 102699714900935431335675649)
  ·
    refine ⟨77024786175701573501756737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102699714900935431335675649 77024786175701573501756737)
    ·
      refine ⟨57768589631776180126317553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77024786175701573501756737 57768589631776180126317553)
      ·
        refine ⟨43326442223832135094738165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57768589631776180126317553 43326442223832135094738165)
        ·
          refine ⟨4061853958484262665131703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43326442223832135094738165 4061853958484262665131703)
          ·
            refine ⟨6092780937726393997697555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061853958484262665131703 6092780937726393997697555)
            ·
              refine ⟨9139171406589590996546333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092780937726393997697555 9139171406589590996546333)
              ·
                refine ⟨3427189277471096623704875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9139171406589590996546333 3427189277471096623704875)
                ·
                  refine ⟨5140783916206644935557313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427189277471096623704875 5140783916206644935557313)
                  ·
                    refine ⟨3855587937154983701667985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5140783916206644935557313 3855587937154983701667985)
                    ·
                      refine ⟨2891690952866237776250989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855587937154983701667985 2891690952866237776250989)
                      ·
                        rfl

theorem cell23_5631548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_5631548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631548 prefixEnd_5631548 := by exact prefixLift 5631548
  have htrace : WordTrace (prefixWord ++ tailWord_5631548) baseStart_5631548 baseEnd_5631548 := by
    simpa [prefixWord, tailWord_5631548, baseEnd_5631548] using wordTrace_append hprefix tailTrace_5631548
  have hstable : (prefixWord ++ tailWord_5631548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631548).length < 2 ^ (prefixWord ++ tailWord_5631548).sum := by decide
  have hdescent : baseEnd_5631548 < baseStart_5631548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631573 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_5631573 : Nat := 118140960795 + 5631573 * 2 ^ 59
def prefixEnd_5631573 : Nat := 4983230072969 + 3 ^ 40 * 5631573 * 2
def baseEnd_5631573 : Nat := 2891703789882600178438373

theorem tailTrace_5631573 : CollatzResearch.WordTrace tailWord_5631573 prefixEnd_5631573 2891703789882600178438373 := by
  unfold tailWord_5631573
  simp only [CollatzResearch.WordTrace]
  refine ⟨205400341626780291941011373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136933561084520194627340915 205400341626780291941011373)
  ·
    refine ⟨77025128110042609477879265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205400341626780291941011373 77025128110042609477879265)
    ·
      refine ⟨57768846082531957108409449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77025128110042609477879265 57768846082531957108409449)
      ·
        refine ⟨43326634561898967831307087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57768846082531957108409449 43326634561898967831307087)
        ·
          refine ⟨64989951842848451746960631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43326634561898967831307087 64989951842848451746960631)
          ·
            refine ⟨97484927764272677620440947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64989951842848451746960631 97484927764272677620440947)
            ·
              refine ⟨146227391646409016430661421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97484927764272677620440947 146227391646409016430661421)
              ·
                refine ⟨54835271867403381161498033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146227391646409016430661421 54835271867403381161498033)
                ·
                  refine ⟨41126453900552535871123525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54835271867403381161498033 41126453900552535871123525)
                  ·
                    refine ⟨7711210106353600475835661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41126453900552535871123525 7711210106353600475835661)
                    ·
                      refine ⟨2891703789882600178438373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711210106353600475835661 2891703789882600178438373)
                      ·
                        rfl

theorem cell23_5631573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_5631573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631573 prefixEnd_5631573 := by exact prefixLift 5631573
  have htrace : WordTrace (prefixWord ++ tailWord_5631573) baseStart_5631573 baseEnd_5631573 := by
    simpa [prefixWord, tailWord_5631573, baseEnd_5631573] using wordTrace_append hprefix tailTrace_5631573
  have hstable : (prefixWord ++ tailWord_5631573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631573).length < 2 ^ (prefixWord ++ tailWord_5631573).sum := by decide
  have hdescent : baseEnd_5631573 < baseStart_5631573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631581 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5631581 : Nat := 118140960795 + 5631581 * 2 ^ 59
def prefixEnd_5631581 : Nat := 4983230072969 + 3 ^ 40 * 5631581 * 2
def baseEnd_5631581 : Nat := 2891707897727836147138337

theorem tailTrace_5631581 : CollatzResearch.WordTrace tailWord_5631581 prefixEnd_5631581 2891707897727836147138337 := by
  unfold tailWord_5631581
  simp only [CollatzResearch.WordTrace]
  refine ⟨205400633410751309307302597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136933755607167539538201731 205400633410751309307302597)
  ·
    refine ⟨38512618764515870495119237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205400633410751309307302597 38512618764515870495119237)
    ·
      refine ⟨7221116018346725717834857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38512618764515870495119237 7221116018346725717834857)
      ·
        refine ⟨5415837013760044288376143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7221116018346725717834857 5415837013760044288376143)
        ·
          refine ⟨8123755520640066432564215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415837013760044288376143 8123755520640066432564215)
          ·
            refine ⟨12185633280960099648846323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8123755520640066432564215 12185633280960099648846323)
            ·
              refine ⟨18278449921440149473269485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12185633280960099648846323 18278449921440149473269485)
              ·
                refine ⟨6854418720540056052476057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18278449921440149473269485 6854418720540056052476057)
                ·
                  refine ⟨5140814040405042039357043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854418720540056052476057 5140814040405042039357043)
                  ·
                    refine ⟨7711221060607563059035565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140814040405042039357043 7711221060607563059035565)
                    ·
                      refine ⟨2891707897727836147138337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711221060607563059035565 2891707897727836147138337)
                      ·
                        rfl

theorem cell23_5631581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5631581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631581 prefixEnd_5631581 := by exact prefixLift 5631581
  have htrace : WordTrace (prefixWord ++ tailWord_5631581) baseStart_5631581 baseEnd_5631581 := by
    simpa [prefixWord, tailWord_5631581, baseEnd_5631581] using wordTrace_append hprefix tailTrace_5631581
  have hstable : (prefixWord ++ tailWord_5631581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631581).length < 2 ^ (prefixWord ++ tailWord_5631581).sum := by decide
  have hdescent : baseEnd_5631581 < baseStart_5631581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631673 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5631673 : Nat := 118140960795 + 5631673 * 2 ^ 59
def prefixEnd_5631673 : Nat := 4983230072969 + 3 ^ 40 * 5631673 * 2
def baseEnd_5631673 : Nat := 2891755137948049787187913

theorem tailTrace_5631673 : CollatzResearch.WordTrace tailWord_5631673 prefixEnd_5631673 2891755137948049787187913 := by
  unfold tailWord_5631673
  simp only [CollatzResearch.WordTrace]
  refine ⟨205403988926418009019651673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136935992617612006013101115 205403988926418009019651673)
  ·
    refine ⟨154052991694813506764738755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205403988926418009019651673 154052991694813506764738755)
    ·
      refine ⟨231079487542220260147108133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154052991694813506764738755 231079487542220260147108133)
      ·
        refine ⟨43327403914166298777582775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231079487542220260147108133 43327403914166298777582775)
        ·
          refine ⟨64991105871249448166374163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43327403914166298777582775 64991105871249448166374163)
          ·
            refine ⟨97486658806874172249561245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64991105871249448166374163 97486658806874172249561245)
            ·
              refine ⟨36557497052577814593585467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97486658806874172249561245 36557497052577814593585467)
              ·
                refine ⟨54836245578866721890378201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36557497052577814593585467 54836245578866721890378201)
                ·
                  refine ⟨41127184184150041417783651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54836245578866721890378201 41127184184150041417783651)
                  ·
                    refine ⟨61690776276225062126675477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41127184184150041417783651 61690776276225062126675477)
                    ·
                      refine ⟨2891755137948049787187913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61690776276225062126675477 2891755137948049787187913)
                      ·
                        rfl

theorem cell23_5631673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5631673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631673 prefixEnd_5631673 := by exact prefixLift 5631673
  have htrace : WordTrace (prefixWord ++ tailWord_5631673) baseStart_5631673 baseEnd_5631673 := by
    simpa [prefixWord, tailWord_5631673, baseEnd_5631673] using wordTrace_append hprefix tailTrace_5631673
  have hstable : (prefixWord ++ tailWord_5631673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631673).length < 2 ^ (prefixWord ++ tailWord_5631673).sum := by decide
  have hdescent : baseEnd_5631673 < baseStart_5631673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631680 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_5631680 : Nat := 118140960795 + 5631680 * 2 ^ 59
def prefixEnd_5631680 : Nat := 4983230072969 + 3 ^ 40 * 5631680 * 2
def baseEnd_5631680 : Nat := 2891758732312631259800381

theorem tailTrace_5631680 : CollatzResearch.WordTrace tailWord_5631680 prefixEnd_5631680 2891758732312631259800381 := by
  unfold tailWord_5631680
  simp only [CollatzResearch.WordTrace]
  refine ⟨102702122118696324607578247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136936162824928432810104329 102702122118696324607578247)
  ·
    refine ⟨154053183178044486911367371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102702122118696324607578247 154053183178044486911367371)
    ·
      refine ⟨231079774767066730367051057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154053183178044486911367371 231079774767066730367051057)
      ·
        refine ⟨173309831075300047775288293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231079774767066730367051057 173309831075300047775288293)
        ·
          refine ⟨32495593326618758957866555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173309831075300047775288293 32495593326618758957866555)
          ·
            refine ⟨48743389989928138436799833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32495593326618758957866555 48743389989928138436799833)
            ·
              refine ⟨36557542492446103827599875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48743389989928138436799833 36557542492446103827599875)
              ·
                refine ⟨54836313738669155741399813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36557542492446103827599875 54836313738669155741399813)
                ·
                  refine ⟨10281808826000466701512465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54836313738669155741399813 10281808826000466701512465)
                  ·
                    refine ⟨7711356619500350026134349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10281808826000466701512465 7711356619500350026134349)
                    ·
                      refine ⟨2891758732312631259800381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711356619500350026134349 2891758732312631259800381)
                      ·
                        rfl

theorem cell23_5631680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_5631680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631680 prefixEnd_5631680 := by exact prefixLift 5631680
  have htrace : WordTrace (prefixWord ++ tailWord_5631680) baseStart_5631680 baseEnd_5631680 := by
    simpa [prefixWord, tailWord_5631680, baseEnd_5631680] using wordTrace_append hprefix tailTrace_5631680
  have hstable : (prefixWord ++ tailWord_5631680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631680).length < 2 ^ (prefixWord ++ tailWord_5631680).sum := by decide
  have hdescent : baseEnd_5631680 < baseStart_5631680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631687 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 1, 4]
def baseStart_5631687 : Nat := 118140960795 + 5631687 * 2 ^ 59
def prefixEnd_5631687 : Nat := 4983230072969 + 3 ^ 40 * 5631687 * 2
def baseEnd_5631687 : Nat := 963920775559070910804283

theorem tailTrace_5631687 : CollatzResearch.WordTrace tailWord_5631687 prefixEnd_5631687 963920775559070910804283 := by
  unfold tailWord_5631687
  simp only [CollatzResearch.WordTrace]
  refine ⟨205404499548367289410661315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136936333032244859607107543 205404499548367289410661315)
  ·
    refine ⟨308106749322550934115991973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205404499548367289410661315 308106749322550934115991973)
    ·
      refine ⟨57770015497978300146748495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308106749322550934115991973 57770015497978300146748495)
      ·
        refine ⟨86655023246967450220122743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57770015497978300146748495 86655023246967450220122743)
        ·
          refine ⟨129982534870451175330184115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86655023246967450220122743 129982534870451175330184115)
          ·
            refine ⟨194973802305676762995276173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129982534870451175330184115 194973802305676762995276173)
            ·
              refine ⟨73115175864628786123228565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194973802305676762995276173 73115175864628786123228565)
              ·
                refine ⟨3427273868654474349526339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73115175864628786123228565 3427273868654474349526339)
                ·
                  refine ⟨5140910802981711524289509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427273868654474349526339 5140910802981711524289509)
                  ·
                    refine ⟨963920775559070910804283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140910802981711524289509 963920775559070910804283)
                    ·
                      rfl

theorem cell23_5631687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_5631687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631687 prefixEnd_5631687 := by exact prefixLift 5631687
  have htrace : WordTrace (prefixWord ++ tailWord_5631687) baseStart_5631687 baseEnd_5631687 := by
    simpa [prefixWord, tailWord_5631687, baseEnd_5631687] using wordTrace_append hprefix tailTrace_5631687
  have hstable : (prefixWord ++ tailWord_5631687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631687).length < 2 ^ (prefixWord ++ tailWord_5631687).sum := by decide
  have hdescent : baseEnd_5631687 < baseStart_5631687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631703 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5631703 : Nat := 118140960795 + 5631703 * 2 ^ 59
def prefixEnd_5631703 : Nat := 4983230072969 + 3 ^ 40 * 5631703 * 2
def baseEnd_5631703 : Nat := 2891770542367684669812775

theorem tailTrace_5631703 : CollatzResearch.WordTrace tailWord_5631703 prefixEnd_5631703 2891770542367684669812775 := by
  unfold tailWord_5631703
  simp only [CollatzResearch.WordTrace]
  refine ⟨205405083116309324143243763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136936722077539549428829175 205405083116309324143243763)
  ·
    refine ⟨308107624674463986214865645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205405083116309324143243763 308107624674463986214865645)
    ·
      refine ⟨115540359252923994830574617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308107624674463986214865645 115540359252923994830574617)
      ·
        refine ⟨86655269439692996122930963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115540359252923994830574617 86655269439692996122930963)
        ·
          refine ⟨129982904159539494184396445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86655269439692996122930963 129982904159539494184396445)
          ·
            refine ⟨48743589059827310319148667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129982904159539494184396445 48743589059827310319148667)
            ·
              refine ⟨73115383589740965478723001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48743589059827310319148667 73115383589740965478723001)
              ·
                refine ⟨54836537692305724109042251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73115383589740965478723001 54836537692305724109042251)
                ·
                  refine ⟨82254806538458586163563377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54836537692305724109042251 82254806538458586163563377)
                  ·
                    refine ⟨61691104903843939622672533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82254806538458586163563377 61691104903843939622672533)
                    ·
                      refine ⟨2891770542367684669812775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61691104903843939622672533 2891770542367684669812775)
                      ·
                        rfl

theorem cell23_5631703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5631703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631703 prefixEnd_5631703 := by exact prefixLift 5631703
  have htrace : WordTrace (prefixWord ++ tailWord_5631703) baseStart_5631703 baseEnd_5631703 := by
    simpa [prefixWord, tailWord_5631703, baseEnd_5631703] using wordTrace_append hprefix tailTrace_5631703
  have hstable : (prefixWord ++ tailWord_5631703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631703).length < 2 ^ (prefixWord ++ tailWord_5631703).sum := by decide
  have hdescent : baseEnd_5631703 < baseStart_5631703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631751 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 6]
def baseStart_5631751 : Nat := 118140960795 + 5631751 * 2 ^ 59
def prefixEnd_5631751 : Nat := 4983230072969 + 3 ^ 40 * 5631751 * 2
def baseEnd_5631751 : Nat := 321310576604344498001395

theorem tailTrace_5631751 : CollatzResearch.WordTrace tailWord_5631751 prefixEnd_5631751 321310576604344498001395 := by
  unfold tailWord_5631751
  simp only [CollatzResearch.WordTrace]
  refine ⟨205406833820135428340991107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136937889213423618893994071 205406833820135428340991107)
  ·
    refine ⟨308110250730203142511486661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205406833820135428340991107 308110250730203142511486661)
    ·
      refine ⟨57770672011913089220903749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308110250730203142511486661 57770672011913089220903749)
      ·
        refine ⟨10832001002233704228919453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57770672011913089220903749 10832001002233704228919453)
        ·
          refine ⟨4062000375837639085844795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10832001002233704228919453 4062000375837639085844795)
          ·
            refine ⟨6093000563756458628767193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062000375837639085844795 6093000563756458628767193)
            ·
              refine ⟨4569750422817343971575395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093000563756458628767193 4569750422817343971575395)
              ·
                refine ⟨6854625634226015957363093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569750422817343971575395 6854625634226015957363093)
                ·
                  refine ⟨321310576604344498001395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6854625634226015957363093 321310576604344498001395)
                  ·
                    rfl

theorem cell23_5631751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 6].length) (baseStart_5631751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631751 prefixEnd_5631751 := by exact prefixLift 5631751
  have htrace : WordTrace (prefixWord ++ tailWord_5631751) baseStart_5631751 baseEnd_5631751 := by
    simpa [prefixWord, tailWord_5631751, baseEnd_5631751] using wordTrace_append hprefix tailTrace_5631751
  have hstable : (prefixWord ++ tailWord_5631751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631751).length < 2 ^ (prefixWord ++ tailWord_5631751).sum := by decide
  have hdescent : baseEnd_5631751 < baseStart_5631751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631767 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5631767 : Nat := 118140960795 + 5631767 * 2 ^ 59
def prefixEnd_5631767 : Nat := 4983230072969 + 3 ^ 40 * 5631767 * 2
def baseEnd_5631767 : Nat := 2891803405129572419412481

theorem tailTrace_5631767 : CollatzResearch.WordTrace tailWord_5631767 prefixEnd_5631767 2891803405129572419412481 := by
  unfold tailWord_5631767
  simp only [CollatzResearch.WordTrace]
  refine ⟨205407417388077463073573555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136938278258718308715715703 205407417388077463073573555)
  ·
    refine ⟨308111126082116194610360333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205407417388077463073573555 308111126082116194610360333)
    ·
      refine ⟨115541672280793572978885125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308111126082116194610360333 115541672280793572978885125)
      ·
        refine ⟨21664063552648794933540961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115541672280793572978885125 21664063552648794933540961)
        ·
          refine ⟨16248047664486596200155721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21664063552648794933540961 16248047664486596200155721)
          ·
            refine ⟨12186035748364947150116791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16248047664486596200155721 12186035748364947150116791)
            ·
              refine ⟨18279053622547420725175187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12186035748364947150116791 18279053622547420725175187)
              ·
                refine ⟨27418580433821131087762781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18279053622547420725175187 27418580433821131087762781)
                ·
                  refine ⟨10281967662682924157911043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27418580433821131087762781 10281967662682924157911043)
                  ·
                    refine ⟨15422951494024386236866565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10281967662682924157911043 15422951494024386236866565)
                    ·
                      refine ⟨2891803405129572419412481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15422951494024386236866565 2891803405129572419412481)
                      ·
                        rfl

theorem cell23_5631767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5631767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631767 prefixEnd_5631767 := by exact prefixLift 5631767
  have htrace : WordTrace (prefixWord ++ tailWord_5631767) baseStart_5631767 baseEnd_5631767 := by
    simpa [prefixWord, tailWord_5631767, baseEnd_5631767] using wordTrace_append hprefix tailTrace_5631767
  have hstable : (prefixWord ++ tailWord_5631767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631767).length < 2 ^ (prefixWord ++ tailWord_5631767).sum := by decide
  have hdescent : baseEnd_5631767 < baseStart_5631767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631790 : List Nat := [4, 1, 3, 2, 13]
def baseStart_5631790 : Nat := 118140960795 + 5631790 * 2 ^ 59
def prefixEnd_5631790 : Nat := 4983230072969 + 3 ^ 40 * 5631790 * 2
def baseEnd_5631790 : Nat := 3966824712187415403875

theorem tailTrace_5631790 : CollatzResearch.WordTrace tailWord_5631790 prefixEnd_5631790 3966824712187415403875 := by
  unfold tailWord_5631790
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676032033374267250207603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136938837511329425334440549 25676032033374267250207603)
  ·
    refine ⟨38514048050061400875311405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25676032033374267250207603 38514048050061400875311405)
    ·
      refine ⟨14442768018773025328241777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38514048050061400875311405 14442768018773025328241777)
      ·
        refine ⟨10832076014079768996181333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14442768018773025328241777 10832076014079768996181333)
        ·
          refine ⟨3966824712187415403875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10832076014079768996181333 3966824712187415403875)
          ·
            rfl

theorem cell23_5631790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 13].length) (baseStart_5631790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631790 prefixEnd_5631790 := by exact prefixLift 5631790
  have htrace : WordTrace (prefixWord ++ tailWord_5631790) baseStart_5631790 baseEnd_5631790 := by
    simpa [prefixWord, tailWord_5631790, baseEnd_5631790] using wordTrace_append hprefix tailTrace_5631790
  have hstable : (prefixWord ++ tailWord_5631790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631790).length < 2 ^ (prefixWord ++ tailWord_5631790).sum := by decide
  have hdescent : baseEnd_5631790 < baseStart_5631790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631794 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_5631794 : Nat := 118140960795 + 5631794 * 2 ^ 59
def prefixEnd_5631794 : Nat := 4983230072969 + 3 ^ 40 * 5631794 * 2
def baseEnd_5631794 : Nat := 963939089702414604591619

theorem tailTrace_5631794 : CollatzResearch.WordTrace tailWord_5631794 prefixEnd_5631794 963939089702414604591619 := by
  unfold tailWord_5631794
  simp only [CollatzResearch.WordTrace]
  refine ⟨51352100539744911671201609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136938934772653097789870957 51352100539744911671201609)
  ·
    refine ⟨38514075404808683753401207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51352100539744911671201609 38514075404808683753401207)
    ·
      refine ⟨57771113107213025630101811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38514075404808683753401207 57771113107213025630101811)
      ·
        refine ⟨86656669660819538445152717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57771113107213025630101811 86656669660819538445152717)
        ·
          refine ⟨32496251122807326916932269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86656669660819538445152717 32496251122807326916932269)
          ·
            refine ⟨12186094171052747593849601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32496251122807326916932269 12186094171052747593849601)
            ·
              refine ⟨9139570628289560695387201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12186094171052747593849601 9139570628289560695387201)
              ·
                refine ⟨6854677971217170521540401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9139570628289560695387201 6854677971217170521540401)
                ·
                  refine ⟨5141008478412877891155301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854677971217170521540401 5141008478412877891155301)
                  ·
                    refine ⟨963939089702414604591619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141008478412877891155301 963939089702414604591619)
                    ·
                      rfl

theorem cell23_5631794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_5631794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631794 prefixEnd_5631794 := by exact prefixLift 5631794
  have htrace : WordTrace (prefixWord ++ tailWord_5631794) baseStart_5631794 baseEnd_5631794 := by
    simpa [prefixWord, tailWord_5631794, baseEnd_5631794] using wordTrace_append hprefix tailTrace_5631794
  have hstable : (prefixWord ++ tailWord_5631794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631794).length < 2 ^ (prefixWord ++ tailWord_5631794).sum := by decide
  have hdescent : baseEnd_5631794 < baseStart_5631794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631795 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 1, 1, 3]
def baseStart_5631795 : Nat := 118140960795 + 5631795 * 2 ^ 59
def prefixEnd_5631795 : Nat := 4983230072969 + 3 ^ 40 * 5631795 * 2
def baseEnd_5631795 : Nat := 2891817782587898309862353

theorem tailTrace_5631795 : CollatzResearch.WordTrace tailWord_5631795 prefixEnd_5631795 2891817782587898309862353 := by
  unfold tailWord_5631795
  simp only [CollatzResearch.WordTrace]
  refine ⟨205408438631976023855592839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136938959087984015903728559 205408438631976023855592839)
  ·
    refine ⟨308112657947964035783389259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205408438631976023855592839 308112657947964035783389259)
    ·
      refine ⟨462168986921946053675083889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308112657947964035783389259 462168986921946053675083889)
      ·
        refine ⟨346626740191459540256312917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462168986921946053675083889 346626740191459540256312917)
        ·
          refine ⟨4062032111618666487378667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 346626740191459540256312917 4062032111618666487378667)
          ·
            refine ⟨6093048167427999731068001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062032111618666487378667 6093048167427999731068001)
            ·
              refine ⟨4569786125570999798301001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093048167427999731068001 4569786125570999798301001)
              ·
                refine ⟨3427339594178249848725751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569786125570999798301001 3427339594178249848725751)
                ·
                  refine ⟨5141009391267374773088627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427339594178249848725751 5141009391267374773088627)
                  ·
                    refine ⟨7711514086901062159632941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141009391267374773088627 7711514086901062159632941)
                    ·
                      refine ⟨2891817782587898309862353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711514086901062159632941 2891817782587898309862353)
                      ·
                        rfl

theorem cell23_5631795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 1, 3].length) (baseStart_5631795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631795 prefixEnd_5631795 := by exact prefixLift 5631795
  have htrace : WordTrace (prefixWord ++ tailWord_5631795) baseStart_5631795 baseEnd_5631795 := by
    simpa [prefixWord, tailWord_5631795, baseEnd_5631795] using wordTrace_append hprefix tailTrace_5631795
  have hstable : (prefixWord ++ tailWord_5631795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631795).length < 2 ^ (prefixWord ++ tailWord_5631795).sum := by decide
  have hdescent : baseEnd_5631795 < baseStart_5631795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631807 : List Nat := [1, 1, 2, 2, 6, 2, 1, 8]
def baseStart_5631807 : Nat := 118140960795 + 5631807 * 2 ^ 59
def prefixEnd_5631807 : Nat := 4983230072969 + 3 ^ 40 * 5631807 * 2
def baseEnd_5631807 : Nat := 107104590531694528256011

theorem tailTrace_5631807 : CollatzResearch.WordTrace tailWord_5631807 prefixEnd_5631807 107104590531694528256011 := by
  unfold tailWord_5631807
  simp only [CollatzResearch.WordTrace]
  refine ⟨205408876307932549905029675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136939250871955033270019783 205408876307932549905029675)
  ·
    refine ⟨308113314461898824857544513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205408876307932549905029675 308113314461898824857544513)
    ·
      refine ⟨231084985846424118643158385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308113314461898824857544513 231084985846424118643158385)
      ·
        refine ⟨173313739384818088982368789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231084985846424118643158385 173313739384818088982368789)
        ·
          refine ⟨8124081533663347921048537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173313739384818088982368789 8124081533663347921048537)
          ·
            refine ⟨6093061150247510940786403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8124081533663347921048537 6093061150247510940786403)
            ·
              refine ⟨9139591725371266411179605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093061150247510940786403 9139591725371266411179605)
              ·
                refine ⟨107104590531694528256011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9139591725371266411179605 107104590531694528256011)
                ·
                  rfl

theorem cell23_5631807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 8].length) (baseStart_5631807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631807 prefixEnd_5631807 := by exact prefixLift 5631807
  have htrace : WordTrace (prefixWord ++ tailWord_5631807) baseStart_5631807 baseEnd_5631807 := by
    simpa [prefixWord, tailWord_5631807, baseEnd_5631807] using wordTrace_append hprefix tailTrace_5631807
  have hstable : (prefixWord ++ tailWord_5631807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631807).length < 2 ^ (prefixWord ++ tailWord_5631807).sum := by decide
  have hdescent : baseEnd_5631807 < baseStart_5631807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631817 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_5631817 : Nat := 118140960795 + 5631817 * 2 ^ 59
def prefixEnd_5631817 : Nat := 4983230072969 + 3 ^ 40 * 5631817 * 2
def baseEnd_5631817 : Nat := 2891829079162297223787251

theorem tailTrace_5631817 : CollatzResearch.WordTrace tailWord_5631817 prefixEnd_5631817 2891829079162297223787251 := by
  unfold tailWord_5631817
  simp only [CollatzResearch.WordTrace]
  refine ⟨205409241037896321612893705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136939494025264214408595803 205409241037896321612893705)
  ·
    refine ⟨154056930778422241209670279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205409241037896321612893705 154056930778422241209670279)
    ·
      refine ⟨231085396167633361814505419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154056930778422241209670279 231085396167633361814505419)
      ·
        refine ⟨346628094251450042721758129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231085396167633361814505419 346628094251450042721758129)
        ·
          refine ⟨259971070688587532041318597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346628094251450042721758129 259971070688587532041318597)
          ·
            refine ⟨48744575754110162257747237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259971070688587532041318597 48744575754110162257747237)
            ·
              refine ⟨9139607953895655423327607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48744575754110162257747237 9139607953895655423327607)
              ·
                refine ⟨13709411930843483134991411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139607953895655423327607 13709411930843483134991411)
                ·
                  refine ⟨20564117896265224702487117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13709411930843483134991411 20564117896265224702487117)
                  ·
                    refine ⟨7711544211099459263432669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20564117896265224702487117 7711544211099459263432669)
                    ·
                      refine ⟨2891829079162297223787251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711544211099459263432669 2891829079162297223787251)
                      ·
                        rfl

theorem cell23_5631817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_5631817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631817 prefixEnd_5631817 := by exact prefixLift 5631817
  have htrace : WordTrace (prefixWord ++ tailWord_5631817) baseStart_5631817 baseEnd_5631817 := by
    simpa [prefixWord, tailWord_5631817, baseEnd_5631817] using wordTrace_append hprefix tailTrace_5631817
  have hstable : (prefixWord ++ tailWord_5631817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631817).length < 2 ^ (prefixWord ++ tailWord_5631817).sum := by decide
  have hdescent : baseEnd_5631817 < baseStart_5631817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631925 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_5631925 : Nat := 118140960795 + 5631925 * 2 ^ 59
def prefixEnd_5631925 : Nat := 4983230072969 + 3 ^ 40 * 5631925 * 2
def baseEnd_5631925 : Nat := 2891884535072982801236755

theorem tailTrace_5631925 : CollatzResearch.WordTrace tailWord_5631925 prefixEnd_5631925 2891884535072982801236755 := by
  unfold tailWord_5631925
  simp only [CollatzResearch.WordTrace]
  refine ⟨205413180121505056057825229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136942120081003370705216819 205413180121505056057825229)
  ·
    refine ⟨77029942545564396021684461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205413180121505056057825229 77029942545564396021684461)
    ·
      refine ⟨28886228454586648508131673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77029942545564396021684461 28886228454586648508131673)
      ·
        refine ⟨21664671340939986381098755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28886228454586648508131673 21664671340939986381098755)
        ·
          refine ⟨32497007011409979571648133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21664671340939986381098755 32497007011409979571648133)
          ·
            refine ⟨6093188814639371169684025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32497007011409979571648133 6093188814639371169684025)
            ·
              refine ⟨4569891610979528377263019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093188814639371169684025 4569891610979528377263019)
              ·
                refine ⟨6854837416469292565894529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569891610979528377263019 6854837416469292565894529)
                ·
                  refine ⟨5141128062351969424420897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854837416469292565894529 5141128062351969424420897)
                  ·
                    refine ⟨3855846046763977068315673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141128062351969424420897 3855846046763977068315673)
                    ·
                      refine ⟨2891884535072982801236755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855846046763977068315673 2891884535072982801236755)
                      ·
                        rfl

theorem cell23_5631925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_5631925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631925 prefixEnd_5631925 := by exact prefixLift 5631925
  have htrace : WordTrace (prefixWord ++ tailWord_5631925) baseStart_5631925 baseEnd_5631925 := by
    simpa [prefixWord, tailWord_5631925, baseEnd_5631925] using wordTrace_append hprefix tailTrace_5631925
  have hstable : (prefixWord ++ tailWord_5631925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631925).length < 2 ^ (prefixWord ++ tailWord_5631925).sum := by decide
  have hdescent : baseEnd_5631925 < baseStart_5631925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631944 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_5631944 : Nat := 118140960795 + 5631944 * 2 ^ 59
def prefixEnd_5631944 : Nat := 4983230072969 + 3 ^ 40 * 5631944 * 2
def baseEnd_5631944 : Nat := 963964763735139408966389

theorem tailTrace_5631944 : CollatzResearch.WordTrace tailWord_5631944 prefixEnd_5631944 963964763735139408966389 := by
  unfold tailWord_5631944
  simp only [CollatzResearch.WordTrace]
  refine ⟨102706936554218111151383443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136942582072290814868511257 102706936554218111151383443)
  ·
    refine ⟨154060404831327166727075165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102706936554218111151383443 154060404831327166727075165)
    ·
      refine ⟨57772651811747687522653187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154060404831327166727075165 57772651811747687522653187)
      ·
        refine ⟨86658977717621531283979781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57772651811747687522653187 86658977717621531283979781)
        ·
          refine ⟨16248558322054037115746209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86658977717621531283979781 16248558322054037115746209)
          ·
            refine ⟨12186418741540527836809657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16248558322054037115746209 12186418741540527836809657)
            ·
              refine ⟨9139814056155395877607243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12186418741540527836809657 9139814056155395877607243)
              ·
                refine ⟨13709721084233093816410865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139814056155395877607243 13709721084233093816410865)
                ·
                  refine ⟨10282290813174820362308149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13709721084233093816410865 10282290813174820362308149)
                  ·
                    refine ⟨963964763735139408966389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10282290813174820362308149 963964763735139408966389)
                    ·
                      rfl

theorem cell23_5631944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_5631944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631944 prefixEnd_5631944 := by exact prefixLift 5631944
  have htrace : WordTrace (prefixWord ++ tailWord_5631944) baseStart_5631944 baseEnd_5631944 := by
    simpa [prefixWord, tailWord_5631944, baseEnd_5631944] using wordTrace_append hprefix tailTrace_5631944
  have hstable : (prefixWord ++ tailWord_5631944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631944).length < 2 ^ (prefixWord ++ tailWord_5631944).sum := by decide
  have hdescent : baseEnd_5631944 < baseStart_5631944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631965 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 5]
def baseStart_5631965 : Nat := 118140960795 + 5631965 * 2 ^ 59
def prefixEnd_5631965 : Nat := 4983230072969 + 3 ^ 40 * 5631965 * 2
def baseEnd_5631965 : Nat := 321322786033240293859619

theorem tailTrace_5631965 : CollatzResearch.WordTrace tailWord_5631965 prefixEnd_5631965 321322786033240293859619 := by
  unfold tailWord_5631965
  simp only [CollatzResearch.WordTrace]
  refine ⟨205414639041360142889281349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136943092694240095259520899 205414639041360142889281349)
  ·
    refine ⟨38515244820255026791740253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205414639041360142889281349 38515244820255026791740253)
    ·
      refine ⟨14443216807595635046902595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38515244820255026791740253 14443216807595635046902595)
      ·
        refine ⟨21664825211393452570353893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14443216807595635046902595 21664825211393452570353893)
        ·
          refine ⟨4062154727136272356941355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21664825211393452570353893 4062154727136272356941355)
          ·
            refine ⟨6093232090704408535412033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062154727136272356941355 6093232090704408535412033)
            ·
              refine ⟨4569924068028306401559025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093232090704408535412033 4569924068028306401559025)
              ·
                refine ⟨3427443051021229801169269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569924068028306401559025 3427443051021229801169269)
                ·
                  refine ⟨321322786033240293859619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3427443051021229801169269 321322786033240293859619)
                  ·
                    rfl

theorem cell23_5631965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_5631965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631965 prefixEnd_5631965 := by exact prefixLift 5631965
  have htrace : WordTrace (prefixWord ++ tailWord_5631965) baseStart_5631965 baseEnd_5631965 := by
    simpa [prefixWord, tailWord_5631965, baseEnd_5631965] using wordTrace_append hprefix tailTrace_5631965
  have hstable : (prefixWord ++ tailWord_5631965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631965).length < 2 ^ (prefixWord ++ tailWord_5631965).sum := by decide
  have hdescent : baseEnd_5631965 < baseStart_5631965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5631998 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5631998 : Nat := 118140960795 + 5631998 * 2 ^ 59
def prefixEnd_5631998 : Nat := 4983230072969 + 3 ^ 40 * 5631998 * 2
def baseEnd_5631998 : Nat := 2891922019160761015623919

theorem tailTrace_5631998 : CollatzResearch.WordTrace tailWord_5631998 prefixEnd_5631998 2891922019160761015623919 := by
  unfold tailWord_5631998
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676980331280073690654081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136943895100160393016821765 25676980331280073690654081)
  ·
    refine ⟨19257735248460055267990561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25676980331280073690654081 19257735248460055267990561)
    ·
      refine ⟨14443301436345041450992921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19257735248460055267990561 14443301436345041450992921)
      ·
        refine ⟨10832476077258781088244691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14443301436345041450992921 10832476077258781088244691)
        ·
          refine ⟨16248714115888171632367037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832476077258781088244691 16248714115888171632367037)
          ·
            refine ⟨6093267793458064362137639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16248714115888171632367037 6093267793458064362137639)
            ·
              refine ⟨9139901690187096543206459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093267793458064362137639 9139901690187096543206459)
              ·
                refine ⟨13709852535280644814809689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139901690187096543206459 13709852535280644814809689)
                ·
                  refine ⟨10282389401460483611107267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13709852535280644814809689 10282389401460483611107267)
                  ·
                    refine ⟨15423584102190725416660901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10282389401460483611107267 15423584102190725416660901)
                    ·
                      refine ⟨2891922019160761015623919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15423584102190725416660901 2891922019160761015623919)
                      ·
                        rfl

theorem cell23_5631998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5631998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5631998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5631998 prefixEnd_5631998 := by exact prefixLift 5631998
  have htrace : WordTrace (prefixWord ++ tailWord_5631998) baseStart_5631998 baseEnd_5631998 := by
    simpa [prefixWord, tailWord_5631998, baseEnd_5631998] using wordTrace_append hprefix tailTrace_5631998
  have hstable : (prefixWord ++ tailWord_5631998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5631998).length < 2 ^ (prefixWord ++ tailWord_5631998).sum := by decide
  have hdescent : baseEnd_5631998 < baseStart_5631998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5631998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632021 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 6]
def baseStart_5632021 : Nat := 118140960795 + 5632021 * 2 ^ 59
def prefixEnd_5632021 : Nat := 4983230072969 + 3 ^ 40 * 5632021 * 2
def baseEnd_5632021 : Nat := 321325981023979380626257

theorem tailTrace_5632021 : CollatzResearch.WordTrace tailWord_5632021 prefixEnd_5632021 321325981023979380626257 := by
  unfold tailWord_5632021
  simp only [CollatzResearch.WordTrace]
  refine ⟨205416681529157264453319917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136944454352771509635546611 205416681529157264453319917)
  ·
    refine ⟨77031255573433974169994969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205416681529157264453319917 77031255573433974169994969)
    ·
      refine ⟨57773441680075480627496227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77031255573433974169994969 57773441680075480627496227)
      ·
        refine ⟨86660162520113220941244341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57773441680075480627496227 86660162520113220941244341)
        ·
          refine ⟨8124390236260614463241657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86660162520113220941244341 8124390236260614463241657)
          ·
            refine ⟨6093292677195460847431243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8124390236260614463241657 6093292677195460847431243)
            ·
              refine ⟨9139939015793191271146865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093292677195460847431243 9139939015793191271146865)
              ·
                refine ⟨6854954261844893453360149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9139939015793191271146865 6854954261844893453360149)
                ·
                  refine ⟨321325981023979380626257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6854954261844893453360149 321325981023979380626257)
                  ·
                    rfl

theorem cell23_5632021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_5632021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632021 prefixEnd_5632021 := by exact prefixLift 5632021
  have htrace : WordTrace (prefixWord ++ tailWord_5632021) baseStart_5632021 baseEnd_5632021 := by
    simpa [prefixWord, tailWord_5632021, baseEnd_5632021] using wordTrace_append hprefix tailTrace_5632021
  have hstable : (prefixWord ++ tailWord_5632021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632021).length < 2 ^ (prefixWord ++ tailWord_5632021).sum := by decide
  have hdescent : baseEnd_5632021 < baseStart_5632021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632031 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 3]
def baseStart_5632031 : Nat := 118140960795 + 5632031 * 2 ^ 59
def prefixEnd_5632031 : Nat := 4983230072969 + 3 ^ 40 * 5632031 * 2
def baseEnd_5632031 : Nat := 2891938964022359386511267

theorem tailTrace_5632031 : CollatzResearch.WordTrace tailWord_5632031 prefixEnd_5632031 2891938964022359386511267 := by
  unfold tailWord_5632031
  simp only [CollatzResearch.WordTrace]
  refine ⟨205417046259121036161183947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136944697506080690774122631 205417046259121036161183947)
  ·
    refine ⟨308125569388681554241775921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205417046259121036161183947 308125569388681554241775921)
    ·
      refine ⟨231094177041511165681331941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308125569388681554241775921 231094177041511165681331941)
      ·
        refine ⟨43330158195283343565249739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231094177041511165681331941 43330158195283343565249739)
        ·
          refine ⟨64995237292925015347874609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43330158195283343565249739 64995237292925015347874609)
          ·
            refine ⟨48746427969693761510905957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64995237292925015347874609 48746427969693761510905957)
            ·
              refine ⟨9139955244317580283294867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48746427969693761510905957 9139955244317580283294867)
              ·
                refine ⟨13709932866476370424942301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9139955244317580283294867 13709932866476370424942301)
                ·
                  refine ⟨5141224824928638909353363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13709932866476370424942301 5141224824928638909353363)
                  ·
                    refine ⟨7711837237392958364030045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141224824928638909353363 7711837237392958364030045)
                    ·
                      refine ⟨2891938964022359386511267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711837237392958364030045 2891938964022359386511267)
                      ·
                        rfl

theorem cell23_5632031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_5632031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632031 prefixEnd_5632031 := by exact prefixLift 5632031
  have htrace : WordTrace (prefixWord ++ tailWord_5632031) baseStart_5632031 baseEnd_5632031 := by
    simpa [prefixWord, tailWord_5632031, baseEnd_5632031] using wordTrace_append hprefix tailTrace_5632031
  have hstable : (prefixWord ++ tailWord_5632031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632031).length < 2 ^ (prefixWord ++ tailWord_5632031).sum := by decide
  have hdescent : baseEnd_5632031 < baseStart_5632031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632047 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 1, 6]
def baseStart_5632047 : Nat := 118140960795 + 5632047 * 2 ^ 59
def prefixEnd_5632047 : Nat := 4983230072969 + 3 ^ 40 * 5632047 * 2
def baseEnd_5632047 : Nat := 963982393237610441303731

theorem tailTrace_5632047 : CollatzResearch.WordTrace tailWord_5632047 prefixEnd_5632047 963982393237610441303731 := by
  unfold tailWord_5632047
  simp only [CollatzResearch.WordTrace]
  refine ⟨205417629827063070893766395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136945086551375380595844263 205417629827063070893766395)
  ·
    refine ⟨308126444740594606340649593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205417629827063070893766395 308126444740594606340649593)
    ·
      refine ⟨231094833555445954755487195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308126444740594606340649593 231094833555445954755487195)
      ·
        refine ⟨346642250333168932133230793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231094833555445954755487195 346642250333168932133230793)
        ·
          refine ⟨259981687749876699099923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346642250333168932133230793 259981687749876699099923095)
          ·
            refine ⟨389972531624815048649884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259981687749876699099923095 389972531624815048649884643)
            ·
              refine ⟨584958797437222572974826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389972531624815048649884643 584958797437222572974826965)
              ·
                refine ⟨13709971814934904054097507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 584958797437222572974826965 13709971814934904054097507)
                ·
                  refine ⟨20564957722402356081146261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13709971814934904054097507 20564957722402356081146261)
                  ·
                    refine ⟨963982393237610441303731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20564957722402356081146261 963982393237610441303731)
                    ·
                      rfl

theorem cell23_5632047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_5632047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632047 prefixEnd_5632047 := by exact prefixLift 5632047
  have htrace : WordTrace (prefixWord ++ tailWord_5632047) baseStart_5632047 baseEnd_5632047 := by
    simpa [prefixWord, tailWord_5632047, baseEnd_5632047] using wordTrace_append hprefix tailTrace_5632047
  have hstable : (prefixWord ++ tailWord_5632047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632047).length < 2 ^ (prefixWord ++ tailWord_5632047).sum := by decide
  have hdescent : baseEnd_5632047 < baseStart_5632047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632064 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_5632064 : Nat := 118140960795 + 5632064 * 2 ^ 59
def prefixEnd_5632064 : Nat := 4983230072969 + 3 ^ 40 * 5632064 * 2
def baseEnd_5632064 : Nat := 963985302961319252466205

theorem tailTrace_5632064 : CollatzResearch.WordTrace tailWord_5632064 prefixEnd_5632064 963985302961319252466205 := by
  unfold tailWord_5632064
  simp only [CollatzResearch.WordTrace]
  refine ⟨102709124934000741398567623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136945499912000988531423497 102709124934000741398567623)
  ·
    refine ⟨154063687401001112097851435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102709124934000741398567623 154063687401001112097851435)
    ·
      refine ⟨231095531101501668146777153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154063687401001112097851435 231095531101501668146777153)
      ·
        refine ⟨173321648326126251110082865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231095531101501668146777153 173321648326126251110082865)
        ·
          refine ⟨129991236244594688332562149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173321648326126251110082865 129991236244594688332562149)
          ·
            refine ⟨24373356795861504062355403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129991236244594688332562149 24373356795861504062355403)
            ·
              refine ⟨36560035193792256093533105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24373356795861504062355403 36560035193792256093533105)
              ·
                refine ⟨27420026395344192070149829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36560035193792256093533105 27420026395344192070149829)
                ·
                  refine ⟨5141254949127036013153093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27420026395344192070149829 5141254949127036013153093)
                  ·
                    refine ⟨963985302961319252466205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141254949127036013153093 963985302961319252466205)
                    ·
                      rfl

theorem cell23_5632064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_5632064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632064 prefixEnd_5632064 := by exact prefixLift 5632064
  have htrace : WordTrace (prefixWord ++ tailWord_5632064) baseStart_5632064 baseEnd_5632064 := by
    simpa [prefixWord, tailWord_5632064, baseEnd_5632064] using wordTrace_append hprefix tailTrace_5632064
  have hstable : (prefixWord ++ tailWord_5632064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632064).length < 2 ^ (prefixWord ++ tailWord_5632064).sum := by decide
  have hdescent : baseEnd_5632064 < baseStart_5632064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632065 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5632065 : Nat := 118140960795 + 5632065 * 2 ^ 59
def prefixEnd_5632065 : Nat := 4983230072969 + 3 ^ 40 * 5632065 * 2
def baseEnd_5632065 : Nat := 2891956422364612253486111

theorem tailTrace_5632065 : CollatzResearch.WordTrace tailWord_5632065 prefixEnd_5632065 2891956422364612253486111 := by
  unfold tailWord_5632065
  simp only [CollatzResearch.WordTrace]
  refine ⟨205418286340997859967921649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136945524227331906645281099 205418286340997859967921649)
  ·
    refine ⟨154063714755748394975941237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205418286340997859967921649 154063714755748394975941237)
    ·
      refine ⟨14443473258351412028994491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154063714755748394975941237 14443473258351412028994491)
      ·
        refine ⟨21665209887527118043491737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14443473258351412028994491 21665209887527118043491737)
        ·
          refine ⟨16248907415645338532618803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21665209887527118043491737 16248907415645338532618803)
          ·
            refine ⟨24373361123468007798928205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16248907415645338532618803 24373361123468007798928205)
            ·
              refine ⟨9140010421300502924598077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24373361123468007798928205 9140010421300502924598077)
              ·
                refine ⟨3427503907987688596724279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9140010421300502924598077 3427503907987688596724279)
                ·
                  refine ⟨5141255861981532895086419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427503907987688596724279 5141255861981532895086419)
                  ·
                    refine ⟨7711883792972299342629629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141255861981532895086419 7711883792972299342629629)
                    ·
                      refine ⟨2891956422364612253486111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711883792972299342629629 2891956422364612253486111)
                      ·
                        rfl

theorem cell23_5632065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5632065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632065 prefixEnd_5632065 := by exact prefixLift 5632065
  have htrace : WordTrace (prefixWord ++ tailWord_5632065) baseStart_5632065 baseEnd_5632065 := by
    simpa [prefixWord, tailWord_5632065, baseEnd_5632065] using wordTrace_append hprefix tailTrace_5632065
  have hstable : (prefixWord ++ tailWord_5632065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632065).length < 2 ^ (prefixWord ++ tailWord_5632065).sum := by decide
  have hdescent : baseEnd_5632065 < baseStart_5632065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632074 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_5632074 : Nat := 118140960795 + 5632074 * 2 ^ 59
def prefixEnd_5632074 : Nat := 4983230072969 + 3 ^ 40 * 5632074 * 2
def baseEnd_5632074 : Nat := 2891961043690502718273569

theorem tailTrace_5632074 : CollatzResearch.WordTrace tailWord_5632074 prefixEnd_5632074 2891961043690502718273569 := by
  unfold tailWord_5632074
  simp only [CollatzResearch.WordTrace]
  refine ⟨51354653649491313626249819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136945743065310169669999517 51354653649491313626249819)
  ·
    refine ⟨77031980474236970439374729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51354653649491313626249819 77031980474236970439374729)
    ·
      refine ⟨57773985355677727829531047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77031980474236970439374729 57773985355677727829531047)
      ·
        refine ⟨86660978033516591744296571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57773985355677727829531047 86660978033516591744296571)
        ·
          refine ⟨129991467050274887616444857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86660978033516591744296571 129991467050274887616444857)
          ·
            refine ⟨97493600287706165712333643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129991467050274887616444857 97493600287706165712333643)
            ·
              refine ⟨146240400431559248568500465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97493600287706165712333643 146240400431559248568500465)
              ·
                refine ⟨109680300323669436426375349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146240400431559248568500465 109680300323669436426375349)
                ·
                  refine ⟨10282528155344009664972689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109680300323669436426375349 10282528155344009664972689)
                  ·
                    refine ⟨7711896116508007248729517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10282528155344009664972689 7711896116508007248729517)
                    ·
                      refine ⟨2891961043690502718273569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711896116508007248729517 2891961043690502718273569)
                      ·
                        rfl

theorem cell23_5632074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_5632074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632074 prefixEnd_5632074 := by exact prefixLift 5632074
  have htrace : WordTrace (prefixWord ++ tailWord_5632074) baseStart_5632074 baseEnd_5632074 := by
    simpa [prefixWord, tailWord_5632074, baseEnd_5632074] using wordTrace_append hprefix tailTrace_5632074
  have hstable : (prefixWord ++ tailWord_5632074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632074).length < 2 ^ (prefixWord ++ tailWord_5632074).sum := by decide
  have hdescent : baseEnd_5632074 < baseStart_5632074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632082 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_5632082 : Nat := 118140960795 + 5632082 * 2 ^ 59
def prefixEnd_5632082 : Nat := 4983230072969 + 3 ^ 40 * 5632082 * 2
def baseEnd_5632082 : Nat := 2891965151535738686973533

theorem tailTrace_5632082 : CollatzResearch.WordTrace tailWord_5632082 prefixEnd_5632082 2891965151535738686973533 := by
  unfold tailWord_5632082
  simp only [CollatzResearch.WordTrace]
  refine ⟨51354726595484067967822625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136945937587957514580860333 51354726595484067967822625)
  ·
    refine ⟨38516044946613050975866969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51354726595484067967822625 38516044946613050975866969)
    ·
      refine ⟨28887033709959788231900227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38516044946613050975866969 28887033709959788231900227)
      ·
        refine ⟨43330550564939682347850341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28887033709959788231900227 43330550564939682347850341)
        ·
          refine ⟨8124478230926190440221939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43330550564939682347850341 8124478230926190440221939)
          ·
            refine ⟨12186717346389285660332909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124478230926190440221939 12186717346389285660332909)
            ·
              refine ⟨4570019004895982122624841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12186717346389285660332909 4570019004895982122624841)
              ·
                refine ⟨3427514253671986591968631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570019004895982122624841 3427514253671986591968631)
                ·
                  refine ⟨5141271380507979887952947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427514253671986591968631 5141271380507979887952947)
                  ·
                    refine ⟨7711907070761969831929421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141271380507979887952947 7711907070761969831929421)
                    ·
                      refine ⟨2891965151535738686973533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711907070761969831929421 2891965151535738686973533)
                      ·
                        rfl

theorem cell23_5632082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_5632082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632082 prefixEnd_5632082 := by exact prefixLift 5632082
  have htrace : WordTrace (prefixWord ++ tailWord_5632082) baseStart_5632082 baseEnd_5632082 := by
    simpa [prefixWord, tailWord_5632082, baseEnd_5632082] using wordTrace_append hprefix tailTrace_5632082
  have hstable : (prefixWord ++ tailWord_5632082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632082).length < 2 ^ (prefixWord ++ tailWord_5632082).sum := by decide
  have hdescent : baseEnd_5632082 < baseStart_5632082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632088 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_5632088 : Nat := 118140960795 + 5632088 * 2 ^ 59
def prefixEnd_5632088 : Nat := 4983230072969 + 3 ^ 40 * 5632088 * 2
def baseEnd_5632088 : Nat := 2891968232419665663498505

theorem tailTrace_5632088 : CollatzResearch.WordTrace tailWord_5632088 prefixEnd_5632088 2891968232419665663498505 := by
  unfold tailWord_5632088
  simp only [CollatzResearch.WordTrace]
  refine ⟨102709562609957267448004459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136946083479943023264005945 102709562609957267448004459)
  ·
    refine ⟨154064343914935901172006689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102709562609957267448004459 154064343914935901172006689)
    ·
      refine ⟨115548257936201925879005017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154064343914935901172006689 115548257936201925879005017)
      ·
        refine ⟨86661193452151444409253763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115548257936201925879005017 86661193452151444409253763)
        ·
          refine ⟨129991790178227166613880645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86661193452151444409253763 129991790178227166613880645)
          ·
            refine ⟨24373460658417593740102621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129991790178227166613880645 24373460658417593740102621)
            ·
              refine ⟨9140047746906597652538483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24373460658417593740102621 9140047746906597652538483)
              ·
                refine ⟨13710071620359896478807725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9140047746906597652538483 13710071620359896478807725)
                ·
                  refine ⟨5141276857634961179552897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13710071620359896478807725 5141276857634961179552897)
                  ·
                    refine ⟨3855957643226220884664673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141276857634961179552897 3855957643226220884664673)
                    ·
                      refine ⟨2891968232419665663498505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3855957643226220884664673 2891968232419665663498505)
                      ·
                        rfl

theorem cell23_5632088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_5632088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632088 prefixEnd_5632088 := by exact prefixLift 5632088
  have htrace : WordTrace (prefixWord ++ tailWord_5632088) baseStart_5632088 baseEnd_5632088 := by
    simpa [prefixWord, tailWord_5632088, baseEnd_5632088] using wordTrace_append hprefix tailTrace_5632088
  have hstable : (prefixWord ++ tailWord_5632088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632088).length < 2 ^ (prefixWord ++ tailWord_5632088).sum := by decide
  have hdescent : baseEnd_5632088 < baseStart_5632088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5632097 : Nat := 118140960795 + 5632097 * 2 ^ 59
def prefixEnd_5632097 : Nat := 4983230072969 + 3 ^ 40 * 5632097 * 2
def baseEnd_5632097 : Nat := 2891972853745556128285963

theorem tailTrace_5632097 : CollatzResearch.WordTrace tailWord_5632097 prefixEnd_5632097 2891972853745556128285963 := by
  unfold tailWord_5632097
  simp only [CollatzResearch.WordTrace]
  refine ⟨205419453476881929433086545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136946302317921286288724363 205419453476881929433086545)
  ·
    refine ⟨154064590107661447074814909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205419453476881929433086545 154064590107661447074814909)
    ·
      refine ⟨57774221290373042653055591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154064590107661447074814909 57774221290373042653055591)
      ·
        refine ⟨86661331935559563979583387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57774221290373042653055591 86661331935559563979583387)
        ·
          refine ⟨129991997903339345969375081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86661331935559563979583387 129991997903339345969375081)
          ·
            refine ⟨97493998427504509477031311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129991997903339345969375081 97493998427504509477031311)
            ·
              refine ⟨146240997641256764215546967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97493998427504509477031311 146240997641256764215546967)
              ·
                refine ⟨219361496461885146323320451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146240997641256764215546967 219361496461885146323320451)
                ·
                  refine ⟨329042244692827719484980677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219361496461885146323320451 329042244692827719484980677)
                  ·
                    refine ⟨61695420879905197403433877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329042244692827719484980677 61695420879905197403433877)
                    ·
                      refine ⟨2891972853745556128285963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61695420879905197403433877 2891972853745556128285963)
                      ·
                        rfl

theorem cell23_5632097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5632097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632097 prefixEnd_5632097 := by exact prefixLift 5632097
  have htrace : WordTrace (prefixWord ++ tailWord_5632097) baseStart_5632097 baseEnd_5632097 := by
    simpa [prefixWord, tailWord_5632097, baseEnd_5632097] using wordTrace_append hprefix tailTrace_5632097
  have hstable : (prefixWord ++ tailWord_5632097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632097).length < 2 ^ (prefixWord ++ tailWord_5632097).sum := by decide
  have hdescent : baseEnd_5632097 < baseStart_5632097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632108 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_5632108 : Nat := 118140960795 + 5632108 * 2 ^ 59
def prefixEnd_5632108 : Nat := 4983230072969 + 3 ^ 40 * 5632108 * 2
def baseEnd_5632108 : Nat := 2891978502032755585248413

theorem tailTrace_5632108 : CollatzResearch.WordTrace tailWord_5632108 prefixEnd_5632108 2891978502032755585248413 := by
  unfold tailWord_5632108
  simp only [CollatzResearch.WordTrace]
  refine ⟨102709927339921039155868489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136946569786561385541157985 102709927339921039155868489)
  ·
    refine ⟨77032445504940779366901367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102709927339921039155868489 77032445504940779366901367)
    ·
      refine ⟨115548668257411169050352051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77032445504940779366901367 115548668257411169050352051)
      ·
        refine ⟨173323002386116753575528077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115548668257411169050352051 173323002386116753575528077)
        ·
          refine ⟨64996125894793782590823029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173323002386116753575528077 64996125894793782590823029)
          ·
            refine ⟨6093386802636917117889659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64996125894793782590823029 6093386802636917117889659)
            ·
              refine ⟨9140080203955375676834489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093386802636917117889659 9140080203955375676834489)
              ·
                refine ⟨6855060152966531757625867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9140080203955375676834489 6855060152966531757625867)
                ·
                  refine ⟨10282590229449797636438801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855060152966531757625867 10282590229449797636438801)
                  ·
                    refine ⟨7711942672087348227329101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10282590229449797636438801 7711942672087348227329101)
                    ·
                      refine ⟨2891978502032755585248413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711942672087348227329101 2891978502032755585248413)
                      ·
                        rfl

theorem cell23_5632108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_5632108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632108 prefixEnd_5632108 := by exact prefixLift 5632108
  have htrace : WordTrace (prefixWord ++ tailWord_5632108) baseStart_5632108 baseEnd_5632108 := by
    simpa [prefixWord, tailWord_5632108, baseEnd_5632108] using wordTrace_append hprefix tailTrace_5632108
  have hstable : (prefixWord ++ tailWord_5632108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632108).length < 2 ^ (prefixWord ++ tailWord_5632108).sum := by decide
  have hdescent : baseEnd_5632108 < baseStart_5632108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632121 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_5632121 : Nat := 118140960795 + 5632121 * 2 ^ 59
def prefixEnd_5632121 : Nat := 4983230072969 + 3 ^ 40 * 5632121 * 2
def baseEnd_5632121 : Nat := 2891985177281264034385853

theorem tailTrace_5632121 : CollatzResearch.WordTrace tailWord_5632121 prefixEnd_5632121 2891985177281264034385853 := by
  unfold tailWord_5632121
  simp only [CollatzResearch.WordTrace]
  refine ⟨205420328828794981531960217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136946885885863321021306811 205420328828794981531960217)
  ·
    refine ⟨154065246621596236148970163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205420328828794981531960217 154065246621596236148970163)
    ·
      refine ⟨231097869932394354223455245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154065246621596236148970163 231097869932394354223455245)
      ·
        refine ⟨86661701224647882833795717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231097869932394354223455245 86661701224647882833795717)
        ·
          refine ⟨16249068979621478031336697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86661701224647882833795717 16249068979621478031336697)
          ·
            refine ⟨12186801734716108523502523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16249068979621478031336697 12186801734716108523502523)
            ·
              refine ⟨18280202602074162785253785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12186801734716108523502523 18280202602074162785253785)
              ·
                refine ⟨13710151951555622088940339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18280202602074162785253785 13710151951555622088940339)
                ·
                  refine ⟨20565227927333433133410509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13710151951555622088940339 20565227927333433133410509)
                  ·
                    refine ⟨7711960472750037425028941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20565227927333433133410509 7711960472750037425028941)
                    ·
                      refine ⟨2891985177281264034385853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711960472750037425028941 2891985177281264034385853)
                      ·
                        rfl

theorem cell23_5632121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_5632121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632121 prefixEnd_5632121 := by exact prefixLift 5632121
  have htrace : WordTrace (prefixWord ++ tailWord_5632121) baseStart_5632121 baseEnd_5632121 := by
    simpa [prefixWord, tailWord_5632121, baseEnd_5632121] using wordTrace_append hprefix tailTrace_5632121
  have hstable : (prefixWord ++ tailWord_5632121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632121).length < 2 ^ (prefixWord ++ tailWord_5632121).sum := by decide
  have hdescent : baseEnd_5632121 < baseStart_5632121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632138 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_5632138 : Nat := 118140960795 + 5632138 * 2 ^ 59
def prefixEnd_5632138 : Nat := 4983230072969 + 3 ^ 40 * 5632138 * 2
def baseEnd_5632138 : Nat := 2891993906452390467873275

theorem tailTrace_5632138 : CollatzResearch.WordTrace tailWord_5632138 prefixEnd_5632138 2891993906452390467873275 := by
  unfold tailWord_5632138
  simp only [CollatzResearch.WordTrace]
  refine ⟨51355237217433348358832267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136947299246488928956886045 51355237217433348358832267)
  ·
    refine ⟨77032855826150022538248401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51355237217433348358832267 77032855826150022538248401)
    ·
      refine ⟨57774641869612516903686301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77032855826150022538248401 57774641869612516903686301)
      ·
        refine ⟨21665490701104693838882363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57774641869612516903686301 21665490701104693838882363)
        ·
          refine ⟨32498236051657040758323545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21665490701104693838882363 32498236051657040758323545)
          ·
            refine ⟨24373677038742780568742659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32498236051657040758323545 24373677038742780568742659)
            ·
              refine ⟨36560515558114170853113989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24373677038742780568742659 36560515558114170853113989)
              ·
                refine ⟨6855096667146407034958873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36560515558114170853113989 6855096667146407034958873)
                ·
                  refine ⟨5141322500359805276219155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6855096667146407034958873 5141322500359805276219155)
                  ·
                    refine ⟨7711983750539707914328733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141322500359805276219155 7711983750539707914328733)
                    ·
                      refine ⟨2891993906452390467873275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7711983750539707914328733 2891993906452390467873275)
                      ·
                        rfl

theorem cell23_5632138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_5632138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632138 prefixEnd_5632138 := by exact prefixLift 5632138
  have htrace : WordTrace (prefixWord ++ tailWord_5632138) baseStart_5632138 baseEnd_5632138 := by
    simpa [prefixWord, tailWord_5632138, baseEnd_5632138] using wordTrace_append hprefix tailTrace_5632138
  have hstable : (prefixWord ++ tailWord_5632138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632138).length < 2 ^ (prefixWord ++ tailWord_5632138).sum := by decide
  have hdescent : baseEnd_5632138 < baseStart_5632138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632178 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_5632178 : Nat := 118140960795 + 5632178 * 2 ^ 59
def prefixEnd_5632178 : Nat := 4983230072969 + 3 ^ 40 * 5632178 * 2
def baseEnd_5632178 : Nat := 2892014445678570311373091

theorem tailTrace_5632178 : CollatzResearch.WordTrace tailWord_5632178 prefixEnd_5632178 2892014445678570311373091 := by
  unfold tailWord_5632178
  simp only [CollatzResearch.WordTrace]
  refine ⟨51355601947397120066696297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136948271859725653511190125 51355601947397120066696297)
  ·
    refine ⟨38516701460547840050022223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51355601947397120066696297 38516701460547840050022223)
    ·
      refine ⟨57775052190821760075033335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38516701460547840050022223 57775052190821760075033335)
      ·
        refine ⟨86662578286232640112550003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57775052190821760075033335 86662578286232640112550003)
        ·
          refine ⟨129993867429348960168825005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86662578286232640112550003 129993867429348960168825005)
          ·
            refine ⟨48747700286005860063309377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129993867429348960168825005 48747700286005860063309377)
            ·
              refine ⟨36560775214504395047482033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48747700286005860063309377 36560775214504395047482033)
              ·
                refine ⟨27420581410878296285611525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36560775214504395047482033 27420581410878296285611525)
                ·
                  refine ⟨5141359014539680553552161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27420581410878296285611525 5141359014539680553552161)
                  ·
                    refine ⟨3856019260904760415164121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141359014539680553552161 3856019260904760415164121)
                    ·
                      refine ⟨2892014445678570311373091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856019260904760415164121 2892014445678570311373091)
                      ·
                        rfl

theorem cell23_5632178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_5632178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632178 prefixEnd_5632178 := by exact prefixLift 5632178
  have htrace : WordTrace (prefixWord ++ tailWord_5632178) baseStart_5632178 baseEnd_5632178 := by
    simpa [prefixWord, tailWord_5632178, baseEnd_5632178] using wordTrace_append hprefix tailTrace_5632178
  have hstable : (prefixWord ++ tailWord_5632178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632178).length < 2 ^ (prefixWord ++ tailWord_5632178).sum := by decide
  have hdescent : baseEnd_5632178 < baseStart_5632178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632231 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 7]
def baseStart_5632231 : Nat := 118140960795 + 5632231 * 2 ^ 59
def prefixEnd_5632231 : Nat := 4983230072969 + 3 ^ 40 * 5632231 * 2
def baseEnd_5632231 : Nat := 964013886717752868003449

theorem tailTrace_5632231 : CollatzResearch.WordTrace tailWord_5632231 prefixEnd_5632231 964013886717752868003449 := by
  unfold tailWord_5632231
  simp only [CollatzResearch.WordTrace]
  refine ⟨205424340858396470318464547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136949560572264313545643031 205424340858396470318464547)
  ·
    refine ⟨308136511287594705477696821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205424340858396470318464547 308136511287594705477696821)
    ·
      refine ⟨28887797933212003638534077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308136511287594705477696821 28887797933212003638534077)
      ·
        refine ⟨10832924224954501364450279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28887797933212003638534077 10832924224954501364450279)
        ·
          refine ⟨16249386337431752046675419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832924224954501364450279 16249386337431752046675419)
          ·
            refine ⟨24374079506147628070013129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16249386337431752046675419 24374079506147628070013129)
            ·
              refine ⟨18280559629610721052509847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24374079506147628070013129 18280559629610721052509847)
              ·
                refine ⟨27420839444416081578764771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18280559629610721052509847 27420839444416081578764771)
                ·
                  refine ⟨41131259166624122368147157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27420839444416081578764771 41131259166624122368147157)
                  ·
                    refine ⟨964013886717752868003449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41131259166624122368147157 964013886717752868003449)
                    ·
                      rfl

theorem cell23_5632231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_5632231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632231 prefixEnd_5632231 := by exact prefixLift 5632231
  have htrace : WordTrace (prefixWord ++ tailWord_5632231) baseStart_5632231 baseEnd_5632231 := by
    simpa [prefixWord, tailWord_5632231, baseEnd_5632231] using wordTrace_append hprefix tailTrace_5632231
  have hstable : (prefixWord ++ tailWord_5632231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632231).length < 2 ^ (prefixWord ++ tailWord_5632231).sum := by decide
  have hdescent : baseEnd_5632231 < baseStart_5632231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632258 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_5632258 : Nat := 118140960795 + 5632258 * 2 ^ 59
def prefixEnd_5632258 : Nat := 4983230072969 + 3 ^ 40 * 5632258 * 2
def baseEnd_5632258 : Nat := 2892055524130929998372723

theorem tailTrace_5632258 : CollatzResearch.WordTrace tailWord_5632258 prefixEnd_5632258 2892055524130929998372723 := by
  unfold tailWord_5632258
  simp only [CollatzResearch.WordTrace]
  refine ⟨51356331407324663482424357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136950217086199102619798285 51356331407324663482424357)
  ·
    refine ⟨9629312138873374402954567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51356331407324663482424357 9629312138873374402954567)
    ·
      refine ⟨14443968208310061604431851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629312138873374402954567 14443968208310061604431851)
      ·
        refine ⟨21665952312465092406647777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14443968208310061604431851 21665952312465092406647777)
        ·
          refine ⟨16249464234348819304985833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21665952312465092406647777 16249464234348819304985833)
          ·
            refine ⟨12187098175761614478739375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16249464234348819304985833 12187098175761614478739375)
            ·
              refine ⟨18280647263642421718109063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187098175761614478739375 18280647263642421718109063)
              ·
                refine ⟨27420970895463632577163595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18280647263642421718109063 27420970895463632577163595)
                ·
                  refine ⟨41131456343195448865745393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27420970895463632577163595 41131456343195448865745393)
                  ·
                    refine ⟨30848592257396586649309045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41131456343195448865745393 30848592257396586649309045)
                    ·
                      refine ⟨2892055524130929998372723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30848592257396586649309045 2892055524130929998372723)
                      ·
                        rfl

theorem cell23_5632258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_5632258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632258 prefixEnd_5632258 := by exact prefixLift 5632258
  have htrace : WordTrace (prefixWord ++ tailWord_5632258) baseStart_5632258 baseEnd_5632258 := by
    simpa [prefixWord, tailWord_5632258, baseEnd_5632258] using wordTrace_append hprefix tailTrace_5632258
  have hstable : (prefixWord ++ tailWord_5632258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632258).length < 2 ^ (prefixWord ++ tailWord_5632258).sum := by decide
  have hdescent : baseEnd_5632258 < baseStart_5632258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632261 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_5632261 : Nat := 118140960795 + 5632261 * 2 ^ 59
def prefixEnd_5632261 : Nat := 4983230072969 + 3 ^ 40 * 5632261 * 2
def baseEnd_5632261 : Nat := 964019021524297828878403

theorem tailTrace_5632261 : CollatzResearch.WordTrace tailWord_5632261 prefixEnd_5632261 964019021524297828878403 := by
  unfold tailWord_5632261
  simp only [CollatzResearch.WordTrace]
  refine ⟨205425435048287785442056637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136950290032191856961371091 205425435048287785442056637)
  ·
    refine ⟨77034538143107919540771239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205425435048287785442056637 77034538143107919540771239)
    ·
      refine ⟨115551807214661879311156859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77034538143107919540771239 115551807214661879311156859)
      ·
        refine ⟨173327710821992818966735289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115551807214661879311156859 173327710821992818966735289)
        ·
          refine ⟨129995783116494614225051467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173327710821992818966735289 129995783116494614225051467)
          ·
            refine ⟨194993674674741921337577201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129995783116494614225051467 194993674674741921337577201)
            ·
              refine ⟨146245256006056441003182901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194993674674741921337577201 146245256006056441003182901)
              ·
                refine ⟨13710492750567791344048397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146245256006056441003182901 13710492750567791344048397)
                ·
                  refine ⟨5141434781462921754018149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13710492750567791344048397 5141434781462921754018149)
                  ·
                    refine ⟨964019021524297828878403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141434781462921754018149 964019021524297828878403)
                    ·
                      rfl

theorem cell23_5632261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_5632261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632261 prefixEnd_5632261 := by exact prefixLift 5632261
  have htrace : WordTrace (prefixWord ++ tailWord_5632261) baseStart_5632261 baseEnd_5632261 := by
    simpa [prefixWord, tailWord_5632261, baseEnd_5632261] using wordTrace_append hprefix tailTrace_5632261
  have hstable : (prefixWord ++ tailWord_5632261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632261).length < 2 ^ (prefixWord ++ tailWord_5632261).sum := by decide
  have hdescent : baseEnd_5632261 < baseStart_5632261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632285 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5632285 : Nat := 118140960795 + 5632285 * 2 ^ 59
def prefixEnd_5632285 : Nat := 4983230072969 + 3 ^ 40 * 5632285 * 2
def baseEnd_5632285 : Nat := 2892069388108601392735099

theorem tailTrace_5632285 : CollatzResearch.WordTrace tailWord_5632285 prefixEnd_5632285 2892069388108601392735099 := by
  unfold tailWord_5632285
  simp only [CollatzResearch.WordTrace]
  refine ⟨205426310400200837540930309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136950873600133891693953539 205426310400200837540930309)
  ·
    refine ⟨38517433200037657038924433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205426310400200837540930309 38517433200037657038924433)
    ·
      refine ⟨28888074900028242779193325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38517433200037657038924433 28888074900028242779193325)
      ·
        refine ⟨10833028087510591042197497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28888074900028242779193325 10833028087510591042197497)
        ·
          refine ⟨8124771065632943281648123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10833028087510591042197497 8124771065632943281648123)
          ·
            refine ⟨12187156598449414922472185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124771065632943281648123 12187156598449414922472185)
            ·
              refine ⟨9140367448837061191854139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12187156598449414922472185 9140367448837061191854139)
              ·
                refine ⟨13710551173255591787781209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9140367448837061191854139 13710551173255591787781209)
                ·
                  refine ⟨10282913379941693840835907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13710551173255591787781209 10282913379941693840835907)
                  ·
                    refine ⟨15424370069912540761253861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10282913379941693840835907 15424370069912540761253861)
                    ·
                      refine ⟨2892069388108601392735099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15424370069912540761253861 2892069388108601392735099)
                      ·
                        rfl

theorem cell23_5632285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5632285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632285 prefixEnd_5632285 := by exact prefixLift 5632285
  have htrace : WordTrace (prefixWord ++ tailWord_5632285) baseStart_5632285 baseEnd_5632285 := by
    simpa [prefixWord, tailWord_5632285, baseEnd_5632285] using wordTrace_append hprefix tailTrace_5632285
  have hstable : (prefixWord ++ tailWord_5632285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632285).length < 2 ^ (prefixWord ++ tailWord_5632285).sum := by decide
  have hdescent : baseEnd_5632285 < baseStart_5632285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632288 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5632288 : Nat := 118140960795 + 5632288 * 2 ^ 59
def prefixEnd_5632288 : Nat := 4983230072969 + 3 ^ 40 * 5632288 * 2
def baseEnd_5632288 : Nat := 2892070928550564880997585

theorem tailTrace_5632288 : CollatzResearch.WordTrace tailWord_5632288 prefixEnd_5632288 2892070928550564880997585 := by
  unfold tailWord_5632288
  simp only [CollatzResearch.WordTrace]
  refine ⟨102713209909594984526644759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136950946546126646035526345 102713209909594984526644759)
  ·
    refine ⟨154069814864392476789967139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102713209909594984526644759 154069814864392476789967139)
    ·
      refine ⟨231104722296588715184950709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154069814864392476789967139 231104722296588715184950709)
      ·
        refine ⟨21666067715305192048589129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231104722296588715184950709 21666067715305192048589129)
        ·
          refine ⟨16249550786478894036441847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21666067715305192048589129 16249550786478894036441847)
          ·
            refine ⟨24374326179718341054662771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16249550786478894036441847 24374326179718341054662771)
            ·
              refine ⟨36561489269577511581994157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24374326179718341054662771 36561489269577511581994157)
              ·
                refine ⟨13710558476091566843247809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36561489269577511581994157 13710558476091566843247809)
                ·
                  refine ⟨10282918857068675132435857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13710558476091566843247809 10282918857068675132435857)
                  ·
                    refine ⟨7712189142801506349326893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10282918857068675132435857 7712189142801506349326893)
                    ·
                      refine ⟨2892070928550564880997585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712189142801506349326893 2892070928550564880997585)
                      ·
                        rfl

theorem cell23_5632288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5632288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632288 prefixEnd_5632288 := by exact prefixLift 5632288
  have htrace : WordTrace (prefixWord ++ tailWord_5632288) baseStart_5632288 baseEnd_5632288 := by
    simpa [prefixWord, tailWord_5632288, baseEnd_5632288] using wordTrace_append hprefix tailTrace_5632288
  have hstable : (prefixWord ++ tailWord_5632288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632288).length < 2 ^ (prefixWord ++ tailWord_5632288).sum := by decide
  have hdescent : baseEnd_5632288 < baseStart_5632288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632308 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5632308 : Nat := 118140960795 + 5632308 * 2 ^ 59
def prefixEnd_5632308 : Nat := 4983230072969 + 3 ^ 40 * 5632308 * 2
def baseEnd_5632308 : Nat := 321342355351517200305277

theorem tailTrace_5632308 : CollatzResearch.WordTrace tailWord_5632308 prefixEnd_5632308 321342355351517200305277 := by
  unfold tailWord_5632308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102713574639558756234508789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136951432852745008312678385 102713574639558756234508789)
  ·
    refine ⟨9629397622458633396985199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102713574639558756234508789 9629397622458633396985199)
    ·
      refine ⟨14444096433687950095477799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629397622458633396985199 14444096433687950095477799)
      ·
        refine ⟨21666144650531925143216699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14444096433687950095477799 21666144650531925143216699)
        ·
          refine ⟨32499216975797887714825049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21666144650531925143216699 32499216975797887714825049)
          ·
            refine ⟨24374412731848415786118787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32499216975797887714825049 24374412731848415786118787)
            ·
              refine ⟨36561619097772623679178181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24374412731848415786118787 36561619097772623679178181)
              ·
                refine ⟨6855303580832366939845909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36561619097772623679178181 6855303580832366939845909)
                ·
                  refine ⟨321342355351517200305277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6855303580832366939845909 321342355351517200305277)
                  ·
                    rfl

theorem cell23_5632308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5632308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632308 prefixEnd_5632308 := by exact prefixLift 5632308
  have htrace : WordTrace (prefixWord ++ tailWord_5632308) baseStart_5632308 baseEnd_5632308 := by
    simpa [prefixWord, tailWord_5632308, baseEnd_5632308] using wordTrace_append hprefix tailTrace_5632308
  have hstable : (prefixWord ++ tailWord_5632308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632308).length < 2 ^ (prefixWord ++ tailWord_5632308).sum := by decide
  have hdescent : baseEnd_5632308 < baseStart_5632308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632328 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_5632328 : Nat := 118140960795 + 5632328 * 2 ^ 59
def prefixEnd_5632328 : Nat := 4983230072969 + 3 ^ 40 * 5632328 * 2
def baseEnd_5632328 : Nat := 2892091467776744724497401

theorem tailTrace_5632328 : CollatzResearch.WordTrace tailWord_5632328 prefixEnd_5632328 2892091467776744724497401 := by
  unfold tailWord_5632328
  simp only [CollatzResearch.WordTrace]
  refine ⟨102713939369522527942372819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136951919159363370589830425 102713939369522527942372819)
  ·
    refine ⟨154070909054283791913559229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102713939369522527942372819 154070909054283791913559229)
    ·
      refine ⟨57776590895356421967584711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154070909054283791913559229 57776590895356421967584711)
      ·
        refine ⟨86664886343034632951377067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57776590895356421967584711 86664886343034632951377067)
        ·
          refine ⟨129997329514551949427065601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86664886343034632951377067 129997329514551949427065601)
          ·
            refine ⟨97497997135913962070299201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129997329514551949427065601 97497997135913962070299201)
            ·
              refine ⟨73123497851935471552724401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97497997135913962070299201 73123497851935471552724401)
              ·
                refine ⟨54842623388951603664543301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73123497851935471552724401 54842623388951603664543301)
                ·
                  refine ⟨10282991885428425687101869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54842623388951603664543301 10282991885428425687101869)
                  ·
                    refine ⟨3856121957035659632663201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10282991885428425687101869 3856121957035659632663201)
                    ·
                      refine ⟨2892091467776744724497401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856121957035659632663201 2892091467776744724497401)
                      ·
                        rfl

theorem cell23_5632328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_5632328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632328 prefixEnd_5632328 := by exact prefixLift 5632328
  have htrace : WordTrace (prefixWord ++ tailWord_5632328) baseStart_5632328 baseEnd_5632328 := by
    simpa [prefixWord, tailWord_5632328, baseEnd_5632328] using wordTrace_append hprefix tailTrace_5632328
  have hstable : (prefixWord ++ tailWord_5632328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632328).length < 2 ^ (prefixWord ++ tailWord_5632328).sum := by decide
  have hdescent : baseEnd_5632328 < baseStart_5632328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632351 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 1, 6]
def baseStart_5632351 : Nat := 118140960795 + 5632351 * 2 ^ 59
def prefixEnd_5632351 : Nat := 4983230072969 + 3 ^ 40 * 5632351 * 2
def baseEnd_5632351 : Nat := 964034425943932711503265

theorem tailTrace_5632351 : CollatzResearch.WordTrace tailWord_5632351 prefixEnd_5632351 964034425943932711503265 := by
  unfold tailWord_5632351
  simp only [CollatzResearch.WordTrace]
  refine ⟨205428717617961730812832907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136952478411974487208555271 205428717617961730812832907)
  ·
    refine ⟨308143076426942596219249361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205428717617961730812832907 308143076426942596219249361)
    ·
      refine ⟨231107307320206947164437021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308143076426942596219249361 231107307320206947164437021)
      ·
        refine ⟨86665240245077605186663883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231107307320206947164437021 86665240245077605186663883)
        ·
          refine ⟨129997860367616407779995825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86665240245077605186663883 129997860367616407779995825)
          ·
            refine ⟨97498395275712305834996869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129997860367616407779995825 97498395275712305834996869)
            ·
              refine ⟨18280949114196057344061913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97498395275712305834996869 18280949114196057344061913)
              ·
                refine ⟨13710711835647043008046435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18280949114196057344061913 13710711835647043008046435)
                ·
                  refine ⟨20566067753470564512069653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13710711835647043008046435 20566067753470564512069653)
                  ·
                    refine ⟨964034425943932711503265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20566067753470564512069653 964034425943932711503265)
                    ·
                      rfl

theorem cell23_5632351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_5632351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632351 prefixEnd_5632351 := by exact prefixLift 5632351
  have htrace : WordTrace (prefixWord ++ tailWord_5632351) baseStart_5632351 baseEnd_5632351 := by
    simpa [prefixWord, tailWord_5632351, baseEnd_5632351] using wordTrace_append hprefix tailTrace_5632351
  have hstable : (prefixWord ++ tailWord_5632351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632351).length < 2 ^ (prefixWord ++ tailWord_5632351).sum := by decide
  have hdescent : baseEnd_5632351 < baseStart_5632351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632361 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_5632361 : Nat := 118140960795 + 5632361 * 2 ^ 59
def prefixEnd_5632361 : Nat := 4983230072969 + 3 ^ 40 * 5632361 * 2
def baseEnd_5632361 : Nat := 2892108412638343095384749

theorem tailTrace_5632361 : CollatzResearch.WordTrace tailWord_5632361 prefixEnd_5632361 2892108412638343095384749 := by
  unfold tailWord_5632361
  simp only [CollatzResearch.WordTrace]
  refine ⟨205429082347925502520696937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136952721565283668347131291 205429082347925502520696937)
  ·
    refine ⟨154071811760944126890522703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205429082347925502520696937 154071811760944126890522703)
    ·
      refine ⟨231107717641416190335784055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154071811760944126890522703 231107717641416190335784055)
      ·
        refine ⟨346661576462124285503676083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231107717641416190335784055 346661576462124285503676083)
        ·
          refine ⟨519992364693186428255514125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346661576462124285503676083 519992364693186428255514125)
          ·
            refine ⟨194997136759944910595817797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519992364693186428255514125 194997136759944910595817797)
            ·
              refine ⟨36561963142489670736715837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194997136759944910595817797 36561963142489670736715837)
              ·
                refine ⟨13710736178433626526268439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36561963142489670736715837 13710736178433626526268439)
                ·
                  refine ⟨20566104267650439789402659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13710736178433626526268439 20566104267650439789402659)
                  ·
                    refine ⟨30849156401475659684103989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20566104267650439789402659 30849156401475659684103989)
                    ·
                      refine ⟨2892108412638343095384749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30849156401475659684103989 2892108412638343095384749)
                      ·
                        rfl

theorem cell23_5632361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_5632361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632361 prefixEnd_5632361 := by exact prefixLift 5632361
  have htrace : WordTrace (prefixWord ++ tailWord_5632361) baseStart_5632361 baseEnd_5632361 := by
    simpa [prefixWord, tailWord_5632361, baseEnd_5632361] using wordTrace_append hprefix tailTrace_5632361
  have hstable : (prefixWord ++ tailWord_5632361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632361).length < 2 ^ (prefixWord ++ tailWord_5632361).sum := by decide
  have hdescent : baseEnd_5632361 < baseStart_5632361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632368 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_5632368 : Nat := 118140960795 + 5632368 * 2 ^ 59
def prefixEnd_5632368 : Nat := 4983230072969 + 3 ^ 40 * 5632368 * 2
def baseEnd_5632368 : Nat := 964037335667641522665739

theorem tailTrace_5632368 : CollatzResearch.WordTrace tailWord_5632368 prefixEnd_5632368 964037335667641522665739 := by
  unfold tailWord_5632368
  simp only [CollatzResearch.WordTrace]
  refine ⟨102714668829450071358100879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136952891772600095144134505 102714668829450071358100879)
  ·
    refine ⟨154072003244175107037151319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102714668829450071358100879 154072003244175107037151319)
    ·
      refine ⟨231108004866262660555726979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154072003244175107037151319 231108004866262660555726979)
      ·
        refine ⟨346662007299393990833590469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231108004866262660555726979 346662007299393990833590469)
        ·
          refine ⟨64999126368636373281298213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346662007299393990833590469 64999126368636373281298213)
          ·
            refine ⟨12187336194119319990243415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64999126368636373281298213 12187336194119319990243415)
            ·
              refine ⟨18281004291178979985365123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187336194119319990243415 18281004291178979985365123)
              ·
                refine ⟨27421506436768469978047685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18281004291178979985365123 27421506436768469978047685)
                ·
                  refine ⟨5141532456894088120883941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27421506436768469978047685 5141532456894088120883941)
                  ·
                    refine ⟨964037335667641522665739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141532456894088120883941 964037335667641522665739)
                    ·
                      rfl

theorem cell23_5632368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_5632368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632368 prefixEnd_5632368 := by exact prefixLift 5632368
  have htrace : WordTrace (prefixWord ++ tailWord_5632368) baseStart_5632368 baseEnd_5632368 := by
    simpa [prefixWord, tailWord_5632368, baseEnd_5632368] using wordTrace_append hprefix tailTrace_5632368
  have hstable : (prefixWord ++ tailWord_5632368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632368).length < 2 ^ (prefixWord ++ tailWord_5632368).sum := by decide
  have hdescent : baseEnd_5632368 < baseStart_5632368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632385 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5632385 : Nat := 118140960795 + 5632385 * 2 ^ 59
def prefixEnd_5632385 : Nat := 4983230072969 + 3 ^ 40 * 5632385 * 2
def baseEnd_5632385 : Nat := 964040245391350333828213

theorem tailTrace_5632385 : CollatzResearch.WordTrace tailWord_5632385 prefixEnd_5632385 964040245391350333828213 := by
  unfold tailWord_5632385
  simp only [CollatzResearch.WordTrace]
  refine ⟨205429957699838554619570609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136953305133225703079713739 205429957699838554619570609)
  ·
    refine ⟨154072468274878915964677957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205429957699838554619570609 154072468274878915964677957)
    ·
      refine ⟨28888587801539796743377117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154072468274878915964677957 28888587801539796743377117)
      ·
        refine ⟨10833220425577423778766419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28888587801539796743377117 10833220425577423778766419)
        ·
          refine ⟨16249830638366135668149629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833220425577423778766419 16249830638366135668149629)
          ·
            refine ⟨6093686489387300875556111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16249830638366135668149629 6093686489387300875556111)
            ·
              refine ⟨9140529734080951313334167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093686489387300875556111 9140529734080951313334167)
              ·
                refine ⟨13710794601121426970001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9140529734080951313334167 13710794601121426970001251)
                ·
                  refine ⟨20566191901682140455001877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13710794601121426970001251 20566191901682140455001877)
                  ·
                    refine ⟨964040245391350333828213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20566191901682140455001877 964040245391350333828213)
                    ·
                      rfl

theorem cell23_5632385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5632385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632385 prefixEnd_5632385 := by exact prefixLift 5632385
  have htrace : WordTrace (prefixWord ++ tailWord_5632385) baseStart_5632385 baseEnd_5632385 := by
    simpa [prefixWord, tailWord_5632385, baseEnd_5632385] using wordTrace_append hprefix tailTrace_5632385
  have hstable : (prefixWord ++ tailWord_5632385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632385).length < 2 ^ (prefixWord ++ tailWord_5632385).sum := by decide
  have hdescent : baseEnd_5632385 < baseStart_5632385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632395 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 3]
def baseStart_5632395 : Nat := 118140960795 + 5632395 * 2 ^ 59
def prefixEnd_5632395 : Nat := 4983230072969 + 3 ^ 40 * 5632395 * 2
def baseEnd_5632395 : Nat := 2892125870980595962359593

theorem tailTrace_5632395 : CollatzResearch.WordTrace tailWord_5632395 prefixEnd_5632395 2892125870980595962359593 := by
  unfold tailWord_5632395
  simp only [CollatzResearch.WordTrace]
  refine ⟨205430322429802326327434639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136953548286534884218289759 205430322429802326327434639)
  ·
    refine ⟨308145483644703489491151959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205430322429802326327434639 308145483644703489491151959)
    ·
      refine ⟨462218225467055234236727939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308145483644703489491151959 462218225467055234236727939)
      ·
        refine ⟨693327338200582851355091909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462218225467055234236727939 693327338200582851355091909)
        ·
          refine ⟨129998875912609284629079733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 693327338200582851355091909 129998875912609284629079733)
          ·
            refine ⟨12187394616807120433976225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129998875912609284629079733 12187394616807120433976225)
            ·
              refine ⟨9140545962605340325482169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12187394616807120433976225 9140545962605340325482169)
              ·
                refine ⟨6855409471954005244111627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9140545962605340325482169 6855409471954005244111627)
                ·
                  refine ⟨10283114207931007866167441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855409471954005244111627 10283114207931007866167441)
                  ·
                    refine ⟨7712335655948255899625581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10283114207931007866167441 7712335655948255899625581)
                    ·
                      refine ⟨2892125870980595962359593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712335655948255899625581 2892125870980595962359593)
                      ·
                        rfl

theorem cell23_5632395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 3].length) (baseStart_5632395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632395 prefixEnd_5632395 := by exact prefixLift 5632395
  have htrace : WordTrace (prefixWord ++ tailWord_5632395) baseStart_5632395 baseEnd_5632395 := by
    simpa [prefixWord, tailWord_5632395, baseEnd_5632395] using wordTrace_append hprefix tailTrace_5632395
  have hstable : (prefixWord ++ tailWord_5632395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632395).length < 2 ^ (prefixWord ++ tailWord_5632395).sum := by decide
  have hdescent : baseEnd_5632395 < baseStart_5632395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632398 : List Nat := [4, 1, 1, 4, 1, 2, 1, 9]
def baseStart_5632398 : Nat := 118140960795 + 5632398 * 2 ^ 59
def prefixEnd_5632398 : Nat := 4983230072969 + 3 ^ 40 * 5632398 * 2
def baseEnd_5632398 : Nat := 107115830052687387060077

theorem tailTrace_5632398 : CollatzResearch.WordTrace tailWord_5632398 prefixEnd_5632398 107115830052687387060077 := by
  unfold tailWord_5632398
  simp only [CollatzResearch.WordTrace]
  refine ⟨25678803981098932229974231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136953621232527638559862565 25678803981098932229974231)
  ·
    refine ⟨38518205971648398344961347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25678803981098932229974231 38518205971648398344961347)
    ·
      refine ⟨57777308957472597517442021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38518205971648398344961347 57777308957472597517442021)
      ·
        refine ⟨10833245429526112034520379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57777308957472597517442021 10833245429526112034520379)
        ·
          refine ⟨16249868144289168051780569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833245429526112034520379 16249868144289168051780569)
          ·
            refine ⟨12187401108216876038835427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16249868144289168051780569 12187401108216876038835427)
            ·
              refine ⟨18281101662325314058253141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187401108216876038835427 18281101662325314058253141)
              ·
                refine ⟨107115830052687387060077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18281101662325314058253141 107115830052687387060077)
                ·
                  rfl

theorem cell23_5632398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_5632398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632398 prefixEnd_5632398 := by exact prefixLift 5632398
  have htrace : WordTrace (prefixWord ++ tailWord_5632398) baseStart_5632398 baseEnd_5632398 := by
    simpa [prefixWord, tailWord_5632398, baseEnd_5632398] using wordTrace_append hprefix tailTrace_5632398
  have hstable : (prefixWord ++ tailWord_5632398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632398).length < 2 ^ (prefixWord ++ tailWord_5632398).sum := by decide
  have hdescent : baseEnd_5632398 < baseStart_5632398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632421 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_5632421 : Nat := 118140960795 + 5632421 * 2 ^ 59
def prefixEnd_5632421 : Nat := 4983230072969 + 3 ^ 40 * 5632421 * 2
def baseEnd_5632421 : Nat := 2892139221477612860634473

theorem tailTrace_5632421 : CollatzResearch.WordTrace tailWord_5632421 prefixEnd_5632421 2892139221477612860634473 := by
  unfold tailWord_5632421
  simp only [CollatzResearch.WordTrace]
  refine ⟨205431270727708132767881117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136954180485138755178587411 205431270727708132767881117)
  ·
    refine ⟨77036726522890549787955419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205431270727708132767881117 77036726522890549787955419)
    ·
      refine ⟨115555089784335824681933129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77036726522890549787955419 115555089784335824681933129)
      ·
        refine ⟨86666317338251868511449847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115555089784335824681933129 86666317338251868511449847)
        ·
          refine ⟨129999476007377802767174771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86666317338251868511449847 129999476007377802767174771)
          ·
            refine ⟨194999214011066704150762157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129999476007377802767174771 194999214011066704150762157)
            ·
              refine ⟨73124705254150014056535809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194999214011066704150762157 73124705254150014056535809)
              ·
                refine ⟨54843528940612510542401857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73124705254150014056535809 54843528940612510542401857)
                ·
                  refine ⟨41132646705459382906801393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54843528940612510542401857 41132646705459382906801393)
                  ·
                    refine ⟨30849485029094537180101045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41132646705459382906801393 30849485029094537180101045)
                    ·
                      refine ⟨2892139221477612860634473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30849485029094537180101045 2892139221477612860634473)
                      ·
                        rfl

theorem cell23_5632421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_5632421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632421 prefixEnd_5632421 := by exact prefixLift 5632421
  have htrace : WordTrace (prefixWord ++ tailWord_5632421) baseStart_5632421 baseEnd_5632421 := by
    simpa [prefixWord, tailWord_5632421, baseEnd_5632421] using wordTrace_append hprefix tailTrace_5632421
  have hstable : (prefixWord ++ tailWord_5632421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632421).length < 2 ^ (prefixWord ++ tailWord_5632421).sum := by decide
  have hdescent : baseEnd_5632421 < baseStart_5632421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632465 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_5632465 : Nat := 118140960795 + 5632465 * 2 ^ 59
def prefixEnd_5632465 : Nat := 4983230072969 + 3 ^ 40 * 5632465 * 2
def baseEnd_5632465 : Nat := 2892161814626410688484271

theorem tailTrace_5632465 : CollatzResearch.WordTrace tailWord_5632465 prefixEnd_5632465 2892161814626410688484271 := by
  unfold tailWord_5632465
  simp only [CollatzResearch.WordTrace]
  refine ⟨205432875539548728282482849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136955250359699152188321899 205432875539548728282482849)
  ·
    refine ⟨154074656654661546211862137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205432875539548728282482849 154074656654661546211862137)
    ·
      refine ⟨115555992490996159658896603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154074656654661546211862137 115555992490996159658896603)
      ·
        refine ⟨173333988736494239488344905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115555992490996159658896603 173333988736494239488344905)
        ·
          refine ⟨130000491552370679616258679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173333988736494239488344905 130000491552370679616258679)
          ·
            refine ⟨195000737328556019424388019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130000491552370679616258679 195000737328556019424388019)
            ·
              refine ⟨292501105992834029136582029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195000737328556019424388019 292501105992834029136582029)
              ·
                refine ⟨109687914747312760926218261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292501105992834029136582029 109687914747312760926218261)
                ·
                  refine ⟨5141621003780285668416481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109687914747312760926218261 5141621003780285668416481)
                  ·
                    refine ⟨3856215752835214251312361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141621003780285668416481 3856215752835214251312361)
                    ·
                      refine ⟨2892161814626410688484271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856215752835214251312361 2892161814626410688484271)
                      ·
                        rfl

theorem cell23_5632465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_5632465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632465 prefixEnd_5632465 := by exact prefixLift 5632465
  have htrace : WordTrace (prefixWord ++ tailWord_5632465) baseStart_5632465 baseEnd_5632465 := by
    simpa [prefixWord, tailWord_5632465, baseEnd_5632465] using wordTrace_append hprefix tailTrace_5632465
  have hstable : (prefixWord ++ tailWord_5632465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632465).length < 2 ^ (prefixWord ++ tailWord_5632465).sum := by decide
  have hdescent : baseEnd_5632465 < baseStart_5632465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632469 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5632469 : Nat := 118140960795 + 5632469 * 2 ^ 59
def prefixEnd_5632469 : Nat := 4983230072969 + 3 ^ 40 * 5632469 * 2
def baseEnd_5632469 : Nat := 2892163868549028672834253

theorem tailTrace_5632469 : CollatzResearch.WordTrace tailWord_5632469 prefixEnd_5632469 2892163868549028672834253 := by
  unfold tailWord_5632469
  simp only [CollatzResearch.WordTrace]
  refine ⟨205433021431534236965628461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136955347621022824643752307 205433021431534236965628461)
  ·
    refine ⟨77037383036825338862110673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205433021431534236965628461 77037383036825338862110673)
    ·
      refine ⟨57778037277619004146583005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77037383036825338862110673 57778037277619004146583005)
      ·
        refine ⟨21666763979107126554968627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57778037277619004146583005 21666763979107126554968627)
        ·
          refine ⟨32500145968660689832452941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21666763979107126554968627 32500145968660689832452941)
          ·
            refine ⟨12187554738247758687169853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32500145968660689832452941 12187554738247758687169853)
            ·
              refine ⟨4570333026842909507688695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12187554738247758687169853 4570333026842909507688695)
              ·
                refine ⟨6855499540264364261533043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570333026842909507688695 6855499540264364261533043)
                ·
                  refine ⟨10283249310396546392299565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6855499540264364261533043 10283249310396546392299565)
                  ·
                    refine ⟨3856218491398704897112337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10283249310396546392299565 3856218491398704897112337)
                    ·
                      refine ⟨2892163868549028672834253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856218491398704897112337 2892163868549028672834253)
                      ·
                        rfl

theorem cell23_5632469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5632469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632469 prefixEnd_5632469 := by exact prefixLift 5632469
  have htrace : WordTrace (prefixWord ++ tailWord_5632469) baseStart_5632469 baseEnd_5632469 := by
    simpa [prefixWord, tailWord_5632469, baseEnd_5632469] using wordTrace_append hprefix tailTrace_5632469
  have hstable : (prefixWord ++ tailWord_5632469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632469).length < 2 ^ (prefixWord ++ tailWord_5632469).sum := by decide
  have hdescent : baseEnd_5632469 < baseStart_5632469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632532 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5632532 : Nat := 118140960795 + 5632532 * 2 ^ 59
def prefixEnd_5632532 : Nat := 4983230072969 + 3 ^ 40 * 5632532 * 2
def baseEnd_5632532 : Nat := 2892196217830261926346463

theorem tailTrace_5632532 : CollatzResearch.WordTrace tailWord_5632532 prefixEnd_5632532 2892196217830261926346463 := by
  unfold tailWord_5632532
  simp only [CollatzResearch.WordTrace]
  refine ⟨102717659615152999362585925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136956879486870665816781233 102717659615152999362585925)
  ·
    refine ⟨19259561177841187380484861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102717659615152999362585925 19259561177841187380484861)
    ·
      refine ⟨7222335441690445267681823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19259561177841187380484861 7222335441690445267681823)
      ·
        refine ⟨10833503162535667901522735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222335441690445267681823 10833503162535667901522735)
        ·
          refine ⟨16250254743803501852284103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833503162535667901522735 16250254743803501852284103)
          ·
            refine ⟨24375382115705252778426155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16250254743803501852284103 24375382115705252778426155)
            ·
              refine ⟨36563073173557879167639233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24375382115705252778426155 36563073173557879167639233)
              ·
                refine ⟨27422304880168409375729425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36563073173557879167639233 27422304880168409375729425)
                ·
                  refine ⟨20566728660126307031797069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27422304880168409375729425 20566728660126307031797069)
                  ·
                    refine ⟨7712523247547365136923901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20566728660126307031797069 7712523247547365136923901)
                    ·
                      refine ⟨2892196217830261926346463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712523247547365136923901 2892196217830261926346463)
                      ·
                        rfl

theorem cell23_5632532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5632532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632532 prefixEnd_5632532 := by exact prefixLift 5632532
  have htrace : WordTrace (prefixWord ++ tailWord_5632532) baseStart_5632532 baseEnd_5632532 := by
    simpa [prefixWord, tailWord_5632532, baseEnd_5632532] using wordTrace_append hprefix tailTrace_5632532
  have hstable : (prefixWord ++ tailWord_5632532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632532).length < 2 ^ (prefixWord ++ tailWord_5632532).sum := by decide
  have hdescent : baseEnd_5632532 < baseStart_5632532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632565 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5632565 : Nat := 118140960795 + 5632565 * 2 ^ 59
def prefixEnd_5632565 : Nat := 4983230072969 + 3 ^ 40 * 5632565 * 2
def baseEnd_5632565 : Nat := 964071054230620099077937

theorem tailTrace_5632565 : CollatzResearch.WordTrace tailWord_5632565 prefixEnd_5632565 964071054230620099077937 := by
  unfold tailWord_5632565
  simp only [CollatzResearch.WordTrace]
  refine ⟨205436522839186445361123149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136957681892790963574082099 205436522839186445361123149)
  ·
    refine ⟨77038696064694917010421181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205436522839186445361123149 77038696064694917010421181)
    ·
      refine ⟨28889511024260593878907943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77038696064694917010421181 28889511024260593878907943)
      ·
        refine ⟨43334266536390890818361915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28889511024260593878907943 43334266536390890818361915)
        ·
          refine ⟨65001399804586336227542873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43334266536390890818361915 65001399804586336227542873)
          ·
            refine ⟨48751049853439752170657155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65001399804586336227542873 48751049853439752170657155)
            ·
              refine ⟨73126574780159628255985733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48751049853439752170657155 73126574780159628255985733)
              ·
                refine ⟨13711232771279930297997325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73126574780159628255985733 13711232771279930297997325)
                ·
                  refine ⟨5141712289229973861748997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13711232771279930297997325 5141712289229973861748997)
                  ·
                    refine ⟨964071054230620099077937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141712289229973861748997 964071054230620099077937)
                    ·
                      rfl

theorem cell23_5632565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5632565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632565 prefixEnd_5632565 := by exact prefixLift 5632565
  have htrace : WordTrace (prefixWord ++ tailWord_5632565) baseStart_5632565 baseEnd_5632565 := by
    simpa [prefixWord, tailWord_5632565, baseEnd_5632565] using wordTrace_append hprefix tailTrace_5632565
  have hstable : (prefixWord ++ tailWord_5632565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632565).length < 2 ^ (prefixWord ++ tailWord_5632565).sum := by decide
  have hdescent : baseEnd_5632565 < baseStart_5632565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632568 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_5632568 : Nat := 118140960795 + 5632568 * 2 ^ 59
def prefixEnd_5632568 : Nat := 4983230072969 + 3 ^ 40 * 5632568 * 2
def baseEnd_5632568 : Nat := 2892214703133823785496297

theorem tailTrace_5632568 : CollatzResearch.WordTrace tailWord_5632568 prefixEnd_5632568 2892214703133823785496297 := by
  unfold tailWord_5632568
  simp only [CollatzResearch.WordTrace]
  refine ⟨102718316129087788436741179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136957754838783717915654905 102718316129087788436741179)
  ·
    refine ⟨154077474193631682655111769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102718316129087788436741179 154077474193631682655111769)
    ·
      refine ⟨115558105645223761991333827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154077474193631682655111769 115558105645223761991333827)
      ·
        refine ⟨173337158467835642987000741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115558105645223761991333827 173337158467835642987000741)
        ·
          refine ⟨32500717212719183060062639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173337158467835642987000741 32500717212719183060062639)
          ·
            refine ⟨48751075819078774590093959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32500717212719183060062639 48751075819078774590093959)
            ·
              refine ⟨73126613728618161885140939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48751075819078774590093959 73126613728618161885140939)
              ·
                refine ⟨109689920592927242827711409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73126613728618161885140939 109689920592927242827711409)
                ·
                  refine ⟨82267440444695432120783557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109689920592927242827711409 82267440444695432120783557)
                  ·
                    refine ⟨15425145083380393522646917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82267440444695432120783557 15425145083380393522646917)
                    ·
                      refine ⟨2892214703133823785496297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15425145083380393522646917 2892214703133823785496297)
                      ·
                        rfl

theorem cell23_5632568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_5632568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632568 prefixEnd_5632568 := by exact prefixLift 5632568
  have htrace : WordTrace (prefixWord ++ tailWord_5632568) baseStart_5632568 baseEnd_5632568 := by
    simpa [prefixWord, tailWord_5632568, baseEnd_5632568] using wordTrace_append hprefix tailTrace_5632568
  have hstable : (prefixWord ++ tailWord_5632568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632568).length < 2 ^ (prefixWord ++ tailWord_5632568).sum := by decide
  have hdescent : baseEnd_5632568 < baseStart_5632568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632575 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_5632575 : Nat := 118140960795 + 5632575 * 2 ^ 59
def prefixEnd_5632575 : Nat := 4983230072969 + 3 ^ 40 * 5632575 * 2
def baseEnd_5632575 : Nat := 2892218297498405258108765

theorem tailTrace_5632575 : CollatzResearch.WordTrace tailWord_5632575 prefixEnd_5632575 2892218297498405258108765 := by
  unfold tailWord_5632575
  simp only [CollatzResearch.WordTrace]
  refine ⟨205436887569150217068987179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136957925046100144712658119 205436887569150217068987179)
  ·
    refine ⟨308155331353725325603480769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205436887569150217068987179 308155331353725325603480769)
    ·
      refine ⟨231116498515293994202610577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308155331353725325603480769 231116498515293994202610577)
      ·
        refine ⟨173337373886470495651957933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231116498515293994202610577 173337373886470495651957933)
        ·
          refine ⟨65001515207426435869484225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173337373886470495651957933 65001515207426435869484225)
          ·
            refine ⟨48751136405569826902113169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65001515207426435869484225 48751136405569826902113169)
            ·
              refine ⟨36563352304177370176584877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48751136405569826902113169 36563352304177370176584877)
              ·
                refine ⟨13711257114066513816219329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36563352304177370176584877 13711257114066513816219329)
                ·
                  refine ⟨10283442835549885362164497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13711257114066513816219329 10283442835549885362164497)
                  ·
                    refine ⟨7712582126662414021623373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10283442835549885362164497 7712582126662414021623373)
                    ·
                      refine ⟨2892218297498405258108765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712582126662414021623373 2892218297498405258108765)
                      ·
                        rfl

theorem cell23_5632575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_5632575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632575 prefixEnd_5632575 := by exact prefixLift 5632575
  have htrace : WordTrace (prefixWord ++ tailWord_5632575) baseStart_5632575 baseEnd_5632575 := by
    simpa [prefixWord, tailWord_5632575, baseEnd_5632575] using wordTrace_append hprefix tailTrace_5632575
  have hstable : (prefixWord ++ tailWord_5632575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632575).length < 2 ^ (prefixWord ++ tailWord_5632575).sum := by decide
  have hdescent : baseEnd_5632575 < baseStart_5632575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632599 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 1, 4]
def baseStart_5632599 : Nat := 118140960795 + 5632599 * 2 ^ 59
def prefixEnd_5632599 : Nat := 4983230072969 + 3 ^ 40 * 5632599 * 2
def baseEnd_5632599 : Nat := 964076873678037721402885

theorem tailTrace_5632599 : CollatzResearch.WordTrace tailWord_5632599 prefixEnd_5632599 964076873678037721402885 := by
  unfold tailWord_5632599
  simp only [CollatzResearch.WordTrace]
  refine ⟨205437762921063269167860851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136958508614042179445240567 205437762921063269167860851)
  ·
    refine ⟨308156644381594903751791277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205437762921063269167860851 308156644381594903751791277)
    ·
      refine ⟨115558741643098088906921729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308156644381594903751791277 115558741643098088906921729)
      ·
        refine ⟨86669056232323566680191297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115558741643098088906921729 86669056232323566680191297)
        ·
          refine ⟨65001792174242675010143473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86669056232323566680191297 65001792174242675010143473)
          ·
            refine ⟨48751344130682006257607605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65001792174242675010143473 48751344130682006257607605)
            ·
              refine ⟨4570438512251438086650713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48751344130682006257607605 4570438512251438086650713)
              ·
                refine ⟨3427828884188578564988035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570438512251438086650713 3427828884188578564988035)
                ·
                  refine ⟨5141743326282867847482053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427828884188578564988035 5141743326282867847482053)
                  ·
                    refine ⟨964076873678037721402885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141743326282867847482053 964076873678037721402885)
                    ·
                      rfl

theorem cell23_5632599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_5632599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632599 prefixEnd_5632599 := by exact prefixLift 5632599
  have htrace : WordTrace (prefixWord ++ tailWord_5632599) baseStart_5632599 baseEnd_5632599 := by
    simpa [prefixWord, tailWord_5632599, baseEnd_5632599] using wordTrace_append hprefix tailTrace_5632599
  have hstable : (prefixWord ++ tailWord_5632599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632599).length < 2 ^ (prefixWord ++ tailWord_5632599).sum := by decide
  have hdescent : baseEnd_5632599 < baseStart_5632599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632665 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_5632665 : Nat := 118140960795 + 5632665 * 2 ^ 59
def prefixEnd_5632665 : Nat := 4983230072969 + 3 ^ 40 * 5632665 * 2
def baseEnd_5632665 : Nat := 2892264510757309905983351

theorem tailTrace_5632665 : CollatzResearch.WordTrace tailWord_5632665 prefixEnd_5632665 2892264510757309905983351 := by
  unfold tailWord_5632665
  simp only [CollatzResearch.WordTrace]
  refine ⟨205440170138824162439763449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136960113425882774959842299 205440170138824162439763449)
  ·
    refine ⟨154080127604118121829822587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205440170138824162439763449 154080127604118121829822587)
    ·
      refine ⟨231120191406177182744733881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154080127604118121829822587 231120191406177182744733881)
      ·
        refine ⟨173340143554632887058550411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231120191406177182744733881 173340143554632887058550411)
        ·
          refine ⟨260010215331949330587825617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173340143554632887058550411 260010215331949330587825617)
          ·
            refine ⟨195007661498961997940869213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260010215331949330587825617 195007661498961997940869213)
            ·
              refine ⟨73127873062110749227825955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195007661498961997940869213 73127873062110749227825955)
              ·
                refine ⟨109691809593166123841738933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73127873062110749227825955 109691809593166123841738933)
                ·
                  refine ⟨10283607149359324110163025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109691809593166123841738933 10283607149359324110163025)
                  ·
                    refine ⟨7712705362019493082622269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10283607149359324110163025 7712705362019493082622269)
                    ·
                      refine ⟨2892264510757309905983351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712705362019493082622269 2892264510757309905983351)
                      ·
                        rfl

theorem cell23_5632665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_5632665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632665 prefixEnd_5632665 := by exact prefixLift 5632665
  have htrace : WordTrace (prefixWord ++ tailWord_5632665) baseStart_5632665 baseEnd_5632665 := by
    simpa [prefixWord, tailWord_5632665, baseEnd_5632665] using wordTrace_append hprefix tailTrace_5632665
  have hstable : (prefixWord ++ tailWord_5632665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632665).length < 2 ^ (prefixWord ++ tailWord_5632665).sum := by decide
  have hdescent : baseEnd_5632665 < baseStart_5632665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632672 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_5632672 : Nat := 118140960795 + 5632672 * 2 ^ 59
def prefixEnd_5632672 : Nat := 4983230072969 + 3 ^ 40 * 5632672 * 2
def baseEnd_5632672 : Nat := 964089368373963792865273

theorem tailTrace_5632672 : CollatzResearch.WordTrace tailWord_5632672 prefixEnd_5632672 964089368373963792865273 := by
  unfold tailWord_5632672
  simp only [CollatzResearch.WordTrace]
  refine ⟨102720212724899401317634135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136960283633199201756845513 102720212724899401317634135)
  ·
    refine ⟨154080319087349101976451203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102720212724899401317634135 154080319087349101976451203)
    ·
      refine ⟨231120478631023652964676805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154080319087349101976451203 231120478631023652964676805)
      ·
        refine ⟨43335089743316934930876901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231120478631023652964676805 43335089743316934930876901)
        ·
          refine ⟨8125329326871925299539419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43335089743316934930876901 8125329326871925299539419)
          ·
            refine ⟨12187993990307887949309129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125329326871925299539419 12187993990307887949309129)
            ·
              refine ⟨9140995492730915961981847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12187993990307887949309129 9140995492730915961981847)
              ·
                refine ⟨13711493239096373942972771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9140995492730915961981847 13711493239096373942972771)
                ·
                  refine ⟨20567239858644560914459157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13711493239096373942972771 20567239858644560914459157)
                  ·
                    refine ⟨964089368373963792865273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20567239858644560914459157 964089368373963792865273)
                    ·
                      rfl

theorem cell23_5632672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_5632672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632672 prefixEnd_5632672 := by exact prefixLift 5632672
  have htrace : WordTrace (prefixWord ++ tailWord_5632672) baseStart_5632672 baseEnd_5632672 := by
    simpa [prefixWord, tailWord_5632672, baseEnd_5632672] using wordTrace_append hprefix tailTrace_5632672
  have hstable : (prefixWord ++ tailWord_5632672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632672).length < 2 ^ (prefixWord ++ tailWord_5632672).sum := by decide
  have hdescent : baseEnd_5632672 < baseStart_5632672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632752 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2]
def baseStart_5632752 : Nat := 118140960795 + 5632752 * 2 ^ 59
def prefixEnd_5632752 : Nat := 4983230072969 + 3 ^ 40 * 5632752 * 2
def baseEnd_5632752 : Nat := 2892309183574251065595451

theorem tailTrace_5632752 : CollatzResearch.WordTrace tailWord_5632752 prefixEnd_5632752 2892309183574251065595451 := by
  unfold tailWord_5632752
  simp only [CollatzResearch.WordTrace]
  refine ⟨102721671644754488149090255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136962228859672650865453673 102721671644754488149090255)
  ·
    refine ⟨154082507467131732223635383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102721671644754488149090255 154082507467131732223635383)
    ·
      refine ⟨231123761200697598335453075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154082507467131732223635383 231123761200697598335453075)
      ·
        refine ⟨346685641801046397503179613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231123761200697598335453075 346685641801046397503179613)
        ·
          refine ⟨130007115675392399063692355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346685641801046397503179613 130007115675392399063692355)
          ·
            refine ⟨195010673513088598595538533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130007115675392399063692355 195010673513088598595538533)
            ·
              refine ⟨36564501283704112236663475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195010673513088598595538533 36564501283704112236663475)
              ·
                refine ⟨54846751925556168354995213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36564501283704112236663475 54846751925556168354995213)
                ·
                  refine ⟨20567531972083563133123205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54846751925556168354995213 20567531972083563133123205)
                  ·
                    refine ⟨3856412244765668087460601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20567531972083563133123205 3856412244765668087460601)
                    ·
                      refine ⟨2892309183574251065595451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856412244765668087460601 2892309183574251065595451)
                      ·
                        rfl

theorem cell23_5632752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 4, 2].length) (baseStart_5632752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632752 prefixEnd_5632752 := by exact prefixLift 5632752
  have htrace : WordTrace (prefixWord ++ tailWord_5632752) baseStart_5632752 baseEnd_5632752 := by
    simpa [prefixWord, tailWord_5632752, baseEnd_5632752] using wordTrace_append hprefix tailTrace_5632752
  have hstable : (prefixWord ++ tailWord_5632752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632752).length < 2 ^ (prefixWord ++ tailWord_5632752).sum := by decide
  have hdescent : baseEnd_5632752 < baseStart_5632752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632755 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3]
def baseStart_5632755 : Nat := 118140960795 + 5632755 * 2 ^ 59
def prefixEnd_5632755 : Nat := 4983230072969 + 3 ^ 40 * 5632755 * 2
def baseEnd_5632755 : Nat := 2892310724016214553857937

theorem tailTrace_5632755 : CollatzResearch.WordTrace tailWord_5632755 prefixEnd_5632755 2892310724016214553857937 := by
  unfold tailWord_5632755
  simp only [CollatzResearch.WordTrace]
  refine ⟨205443452708498107810539719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136962301805665405207026479 205443452708498107810539719)
  ·
    refine ⟨308165179062747161715809579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205443452708498107810539719 308165179062747161715809579)
    ·
      refine ⟨462247768594120742573714369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308165179062747161715809579 462247768594120742573714369)
      ·
        refine ⟨346685826445590556930285777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462247768594120742573714369 346685826445590556930285777)
        ·
          refine ⟨260014369834192917697714333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346685826445590556930285777 260014369834192917697714333)
          ·
            refine ⟨97505388687822344136642875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260014369834192917697714333 97505388687822344136642875)
            ·
              refine ⟨146258083031733516204964313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97505388687822344136642875 146258083031733516204964313)
              ·
                refine ⟨109693562273800137153723235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146258083031733516204964313 109693562273800137153723235)
                ·
                  refine ⟨164540343410700205730584853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109693562273800137153723235 164540343410700205730584853)
                  ·
                    refine ⟨7712828597376572143621165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164540343410700205730584853 7712828597376572143621165)
                    ·
                      refine ⟨2892310724016214553857937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712828597376572143621165 2892310724016214553857937)
                      ·
                        rfl

theorem cell23_5632755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_5632755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632755 prefixEnd_5632755 := by exact prefixLift 5632755
  have htrace : WordTrace (prefixWord ++ tailWord_5632755) baseStart_5632755 baseEnd_5632755 := by
    simpa [prefixWord, tailWord_5632755, baseEnd_5632755] using wordTrace_append hprefix tailTrace_5632755
  have hstable : (prefixWord ++ tailWord_5632755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632755).length < 2 ^ (prefixWord ++ tailWord_5632755).sum := by decide
  have hdescent : baseEnd_5632755 < baseStart_5632755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632772 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5632772 : Nat := 118140960795 + 5632772 * 2 ^ 59
def prefixEnd_5632772 : Nat := 4983230072969 + 3 ^ 40 * 5632772 * 2
def baseEnd_5632772 : Nat := 2892319453187340987345359

theorem tailTrace_5632772 : CollatzResearch.WordTrace tailWord_5632772 prefixEnd_5632772 2892319453187340987345359 := by
  unfold tailWord_5632772
  simp only [CollatzResearch.WordTrace]
  refine ⟨102722036374718259856954285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136962715166291013142605713 102722036374718259856954285)
  ·
    refine ⟨38520763640519347446357857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102722036374718259856954285 38520763640519347446357857)
    ·
      refine ⟨28890572730389510584768393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38520763640519347446357857 28890572730389510584768393)
      ·
        refine ⟨21667929547792132938576295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28890572730389510584768393 21667929547792132938576295)
        ·
          refine ⟨32501894321688199407864443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21667929547792132938576295 32501894321688199407864443)
          ·
            refine ⟨48752841482532299111796665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32501894321688199407864443 48752841482532299111796665)
            ·
              refine ⟨36564631111899224333847499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48752841482532299111796665 36564631111899224333847499)
              ·
                refine ⟨54846946667848836500771249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36564631111899224333847499 54846946667848836500771249)
                ·
                  refine ⟨41135210000886627375578437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54846946667848836500771249 41135210000886627375578437)
                  ·
                    refine ⟨7712851875166242632920957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41135210000886627375578437 7712851875166242632920957)
                    ·
                      refine ⟨2892319453187340987345359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7712851875166242632920957 2892319453187340987345359)
                      ·
                        rfl

theorem cell23_5632772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5632772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632772 prefixEnd_5632772 := by exact prefixLift 5632772
  have htrace : WordTrace (prefixWord ++ tailWord_5632772) baseStart_5632772 baseEnd_5632772 := by
    simpa [prefixWord, tailWord_5632772, baseEnd_5632772] using wordTrace_append hprefix tailTrace_5632772
  have hstable : (prefixWord ++ tailWord_5632772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632772).length < 2 ^ (prefixWord ++ tailWord_5632772).sum := by decide
  have hdescent : baseEnd_5632772 < baseStart_5632772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632820 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_5632820 : Nat := 118140960795 + 5632820 * 2 ^ 59
def prefixEnd_5632820 : Nat := 4983230072969 + 3 ^ 40 * 5632820 * 2
def baseEnd_5632820 : Nat := 2892344100258756799545139

theorem tailTrace_5632820 : CollatzResearch.WordTrace tailWord_5632820 prefixEnd_5632820 2892344100258756799545139 := by
  unfold tailWord_5632820
  simp only [CollatzResearch.WordTrace]
  refine ⟨102722911726631311955827957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136963882302175082607770609 102722911726631311955827957)
  ·
    refine ⟨9630272974371685495858871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102722911726631311955827957 9630272974371685495858871)
    ·
      refine ⟨14445409461557528243788307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630272974371685495858871 14445409461557528243788307)
      ·
        refine ⟨21668114192336292365682461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445409461557528243788307 21668114192336292365682461)
        ·
          refine ⟨8125542822126109637130923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21668114192336292365682461 8125542822126109637130923)
          ·
            refine ⟨12188314233189164455696385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125542822126109637130923 12188314233189164455696385)
            ·
              refine ⟨9141235674891873341772289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12188314233189164455696385 9141235674891873341772289)
              ·
                refine ⟨6855926756168905006329217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9141235674891873341772289 6855926756168905006329217)
                ·
                  refine ⟨5141945067126678754746913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6855926756168905006329217 5141945067126678754746913)
                  ·
                    refine ⟨3856458800345009066060185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5141945067126678754746913 3856458800345009066060185)
                    ·
                      refine ⟨2892344100258756799545139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856458800345009066060185 2892344100258756799545139)
                      ·
                        rfl

theorem cell23_5632820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_5632820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632820 prefixEnd_5632820 := by exact prefixLift 5632820
  have htrace : WordTrace (prefixWord ++ tailWord_5632820) baseStart_5632820 baseEnd_5632820 := by
    simpa [prefixWord, tailWord_5632820, baseEnd_5632820] using wordTrace_append hprefix tailTrace_5632820
  have hstable : (prefixWord ++ tailWord_5632820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632820).length < 2 ^ (prefixWord ++ tailWord_5632820).sum := by decide
  have hdescent : baseEnd_5632820 < baseStart_5632820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632872 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5632872 : Nat := 118140960795 + 5632872 * 2 ^ 59
def prefixEnd_5632872 : Nat := 4983230072969 + 3 ^ 40 * 5632872 * 2
def baseEnd_5632872 : Nat := 2892370801252790596094899

theorem tailTrace_5632872 : CollatzResearch.WordTrace tailWord_5632872 prefixEnd_5632872 2892370801252790596094899 := by
  unfold tailWord_5632872
  simp only [CollatzResearch.WordTrace]
  refine ⟨102723860024537118396274435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136965146699382824528365913 102723860024537118396274435)
  ·
    refine ⟨154085790036805677594411653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102723860024537118396274435 154085790036805677594411653)
    ·
      refine ⟨28891085631901064548952185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154085790036805677594411653 28891085631901064548952185)
      ·
        refine ⟨21668314223925798411714139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28891085631901064548952185 21668314223925798411714139)
        ·
          refine ⟨32502471335888697617571209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21668314223925798411714139 32502471335888697617571209)
          ·
            refine ⟨24376853501916523213178407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32502471335888697617571209 24376853501916523213178407)
            ·
              refine ⟨36565280252874784819767611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24376853501916523213178407 36565280252874784819767611)
              ·
                refine ⟨54847920379312177229651417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36565280252874784819767611 54847920379312177229651417)
                ·
                  refine ⟨41135940284484132922238563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54847920379312177229651417 41135940284484132922238563)
                  ·
                    refine ⟨61703910426726199383357845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41135940284484132922238563 61703910426726199383357845)
                    ·
                      refine ⟨2892370801252790596094899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61703910426726199383357845 2892370801252790596094899)
                      ·
                        rfl

theorem cell23_5632872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5632872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632872 prefixEnd_5632872 := by exact prefixLift 5632872
  have htrace : WordTrace (prefixWord ++ tailWord_5632872) baseStart_5632872 baseEnd_5632872 := by
    simpa [prefixWord, tailWord_5632872, baseEnd_5632872] using wordTrace_append hprefix tailTrace_5632872
  have hstable : (prefixWord ++ tailWord_5632872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632872).length < 2 ^ (prefixWord ++ tailWord_5632872).sum := by decide
  have hdescent : baseEnd_5632872 < baseStart_5632872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632886 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_5632886 : Nat := 118140960795 + 5632886 * 2 ^ 59
def prefixEnd_5632886 : Nat := 4983230072969 + 3 ^ 40 * 5632886 * 2
def baseEnd_5632886 : Nat := 964125996660651180439945

theorem tailTrace_5632886 : CollatzResearch.WordTrace tailWord_5632886 prefixEnd_5632886 964125996660651180439945 := by
  unfold tailWord_5632886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840514416938969823972407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136965487114015678122372341 12840514416938969823972407)
  ·
    refine ⟨19260771625408454735958611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12840514416938969823972407 19260771625408454735958611)
    ·
      refine ⟨28891157438112682103937917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19260771625408454735958611 28891157438112682103937917)
      ·
        refine ⟨10834184039292255788976719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28891157438112682103937917 10834184039292255788976719)
        ·
          refine ⟨16251276058938383683465079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10834184039292255788976719 16251276058938383683465079)
          ·
            refine ⟨24376914088407575525197619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16251276058938383683465079 24376914088407575525197619)
            ·
              refine ⟨36565371132611363287796429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24376914088407575525197619 36565371132611363287796429)
              ·
                refine ⟨13712014174729261232923661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36565371132611363287796429 13712014174729261232923661)
                ·
                  refine ⟨5142005315523472962346373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13712014174729261232923661 5142005315523472962346373)
                  ·
                    refine ⟨964125996660651180439945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5142005315523472962346373 964125996660651180439945)
                    ·
                      rfl

theorem cell23_5632886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_5632886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632886 prefixEnd_5632886 := by exact prefixLift 5632886
  have htrace : WordTrace (prefixWord ++ tailWord_5632886) baseStart_5632886 baseEnd_5632886 := by
    simpa [prefixWord, tailWord_5632886, baseEnd_5632886] using wordTrace_append hprefix tailTrace_5632886
  have hstable : (prefixWord ++ tailWord_5632886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632886).length < 2 ^ (prefixWord ++ tailWord_5632886).sum := by decide
  have hdescent : baseEnd_5632886 < baseStart_5632886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632899 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 6]
def baseStart_5632899 : Nat := 118140960795 + 5632899 * 2 ^ 59
def prefixEnd_5632899 : Nat := 4983230072969 + 3 ^ 40 * 5632899 * 2
def baseEnd_5632899 : Nat := 321376073914495776717475

theorem tailTrace_5632899 : CollatzResearch.WordTrace tailWord_5632899 prefixEnd_5632899 321376073914495776717475 := by
  unfold tailWord_5632899
  simp only [CollatzResearch.WordTrace]
  refine ⟨205448704819976420403781751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136965803213317613602521167 205448704819976420403781751)
  ·
    refine ⟨308173057229964630605672627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205448704819976420403781751 308173057229964630605672627)
    ·
      refine ⟨462259585844946945908508941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308173057229964630605672627 462259585844946945908508941)
      ·
        refine ⟨173347344691855104715690853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462259585844946945908508941 173347344691855104715690853)
        ·
          refine ⟨32502627129722832134192035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173347344691855104715690853 32502627129722832134192035)
          ·
            refine ⟨48753940694584248201288053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32502627129722832134192035 48753940694584248201288053)
            ·
              refine ⟨4570681940117273268870755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48753940694584248201288053 4570681940117273268870755)
              ·
                refine ⟨6856022910175909903306133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570681940117273268870755 6856022910175909903306133)
                ·
                  refine ⟨321376073914495776717475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6856022910175909903306133 321376073914495776717475)
                  ·
                    rfl

theorem cell23_5632899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 6].length) (baseStart_5632899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632899 prefixEnd_5632899 := by exact prefixLift 5632899
  have htrace : WordTrace (prefixWord ++ tailWord_5632899) baseStart_5632899 baseEnd_5632899 := by
    simpa [prefixWord, tailWord_5632899, baseEnd_5632899] using wordTrace_append hprefix tailTrace_5632899
  have hstable : (prefixWord ++ tailWord_5632899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632899).length < 2 ^ (prefixWord ++ tailWord_5632899).sum := by decide
  have hdescent : baseEnd_5632899 < baseStart_5632899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632919 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 5, 2]
def baseStart_5632919 : Nat := 118140960795 + 5632919 * 2 ^ 59
def prefixEnd_5632919 : Nat := 4983230072969 + 3 ^ 40 * 5632919 * 2
def baseEnd_5632919 : Nat := 2892394934843551912207183

theorem tailTrace_5632919 : CollatzResearch.WordTrace tailWord_5632919 prefixEnd_5632919 2892394934843551912207183 := by
  unfold tailWord_5632919
  simp only [CollatzResearch.WordTrace]
  refine ⟨205449434279903963819509811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136966289519935975879673207 205449434279903963819509811)
  ·
    refine ⟨308174151419855945729264717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205449434279903963819509811 308174151419855945729264717)
    ·
      refine ⟨115565306782445979648474269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308174151419855945729264717 115565306782445979648474269)
      ·
        refine ⟨43336990043417242368177851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115565306782445979648474269 43336990043417242368177851)
        ·
          refine ⟨65005485065125863552266777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43336990043417242368177851 65005485065125863552266777)
          ·
            refine ⟨48754113798844397664200083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65005485065125863552266777 48754113798844397664200083)
            ·
              refine ⟨73131170698266596496300125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48754113798844397664200083 73131170698266596496300125)
              ·
                refine ⟨27424189011849973686112547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73131170698266596496300125 27424189011849973686112547)
                ·
                  refine ⟨41136283517774960529168821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27424189011849973686112547 41136283517774960529168821)
                  ·
                    refine ⟨3856526579791402549609577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41136283517774960529168821 3856526579791402549609577)
                    ·
                      refine ⟨2892394934843551912207183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856526579791402549609577 2892394934843551912207183)
                      ·
                        rfl

theorem cell23_5632919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_5632919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632919 prefixEnd_5632919 := by exact prefixLift 5632919
  have htrace : WordTrace (prefixWord ++ tailWord_5632919) baseStart_5632919 baseEnd_5632919 := by
    simpa [prefixWord, tailWord_5632919, baseEnd_5632919] using wordTrace_append hprefix tailTrace_5632919
  have hstable : (prefixWord ++ tailWord_5632919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632919).length < 2 ^ (prefixWord ++ tailWord_5632919).sum := by decide
  have hdescent : baseEnd_5632919 < baseStart_5632919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632949 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5632949 : Nat := 118140960795 + 5632949 * 2 ^ 59
def prefixEnd_5632949 : Nat := 4983230072969 + 3 ^ 40 * 5632949 * 2
def baseEnd_5632949 : Nat := 2892410339263186794832045

theorem tailTrace_5632949 : CollatzResearch.WordTrace tailWord_5632949 prefixEnd_5632949 2892410339263186794832045 := by
  unfold tailWord_5632949
  simp only [CollatzResearch.WordTrace]
  refine ⟨205450528469795278943101901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136967018979863519295401267 205450528469795278943101901)
  ·
    refine ⟨77043948176173229603663213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205450528469795278943101901 77043948176173229603663213)
    ·
      refine ⟨28891480566064961101373705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77043948176173229603663213 28891480566064961101373705)
      ·
        refine ⟨21668610424548720826030279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28891480566064961101373705 21668610424548720826030279)
        ·
          refine ⟨32502915636823081239045419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21668610424548720826030279 32502915636823081239045419)
          ·
            refine ⟨48754373455234621858568129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32502915636823081239045419 48754373455234621858568129)
            ·
              refine ⟨36565780091425966393926097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48754373455234621858568129 36565780091425966393926097)
              ·
                refine ⟨27424335068569474795444573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36565780091425966393926097 27424335068569474795444573)
                ·
                  refine ⟨10284125650713553048291715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27424335068569474795444573 10284125650713553048291715)
                  ·
                    refine ⟨15426188476070329572437573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10284125650713553048291715 15426188476070329572437573)
                    ·
                      refine ⟨2892410339263186794832045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15426188476070329572437573 2892410339263186794832045)
                      ·
                        rfl

theorem cell23_5632949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5632949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632949 prefixEnd_5632949 := by exact prefixLift 5632949
  have htrace : WordTrace (prefixWord ++ tailWord_5632949) baseStart_5632949 baseEnd_5632949 := by
    simpa [prefixWord, tailWord_5632949, baseEnd_5632949] using wordTrace_append hprefix tailTrace_5632949
  have hstable : (prefixWord ++ tailWord_5632949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632949).length < 2 ^ (prefixWord ++ tailWord_5632949).sum := by decide
  have hdescent : baseEnd_5632949 < baseStart_5632949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632950 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_5632950 : Nat := 118140960795 + 5632950 * 2 ^ 59
def prefixEnd_5632950 : Nat := 4983230072969 + 3 ^ 40 * 5632950 * 2
def baseEnd_5632950 : Nat := 321378983638204587879949

theorem tailTrace_5632950 : CollatzResearch.WordTrace tailWord_5632950 prefixEnd_5632950 321378983638204587879949 := by
  unfold tailWord_5632950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840660308924478507118019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136967043295194437409258869 12840660308924478507118019)
  ·
    refine ⟨19260990463386717760677029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12840660308924478507118019 19260990463386717760677029)
    ·
      refine ⟨3611435711885009580126943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19260990463386717760677029 3611435711885009580126943)
      ·
        refine ⟨5417153567827514370190415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611435711885009580126943 5417153567827514370190415)
        ·
          refine ⟨8125730351741271555285623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417153567827514370190415 8125730351741271555285623)
          ·
            refine ⟨12188595527611907332928435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125730351741271555285623 12188595527611907332928435)
            ·
              refine ⟨18282893291417860999392653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12188595527611907332928435 18282893291417860999392653)
              ·
                refine ⟨6856084984281697874772245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18282893291417860999392653 6856084984281697874772245)
                ·
                  refine ⟨321378983638204587879949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6856084984281697874772245 321378983638204587879949)
                  ·
                    rfl

theorem cell23_5632950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_5632950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632950 prefixEnd_5632950 := by exact prefixLift 5632950
  have htrace : WordTrace (prefixWord ++ tailWord_5632950) baseStart_5632950 baseEnd_5632950 := by
    simpa [prefixWord, tailWord_5632950, baseEnd_5632950] using wordTrace_append hprefix tailTrace_5632950
  have hstable : (prefixWord ++ tailWord_5632950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632950).length < 2 ^ (prefixWord ++ tailWord_5632950).sum := by decide
  have hdescent : baseEnd_5632950 < baseStart_5632950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632972 : List Nat := [2, 2, 1, 4, 1, 1, 1, 11]
def baseStart_5632972 : Nat := 118140960795 + 5632972 * 2 ^ 59
def prefixEnd_5632972 : Nat := 4983230072969 + 3 ^ 40 * 5632972 * 2
def baseEnd_5632972 : Nat := 107126746271045933512757

theorem tailTrace_5632972 : CollatzResearch.WordTrace tailWord_5632972 prefixEnd_5632972 107126746271045933512757 := by
  unfold tailWord_5632972
  simp only [CollatzResearch.WordTrace]
  refine ⟨102725683674355976935594585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136967578232474635914126113 102725683674355976935594585)
  ·
    refine ⟨77044262755766982701695939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102725683674355976935594585 77044262755766982701695939)
    ·
      refine ⟨115566394133650474052543909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77044262755766982701695939 115566394133650474052543909)
      ·
        refine ⟨21668698900059463884851983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115566394133650474052543909 21668698900059463884851983)
        ·
          refine ⟨32503048350089195827277975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21668698900059463884851983 32503048350089195827277975)
          ·
            refine ⟨48754572525133793740916963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32503048350089195827277975 48754572525133793740916963)
            ·
              refine ⟨73131858787700690611375445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48754572525133793740916963 73131858787700690611375445)
              ·
                refine ⟨107126746271045933512757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 73131858787700690611375445 107126746271045933512757)
                ·
                  rfl

theorem cell23_5632972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 11].length) (baseStart_5632972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632972 prefixEnd_5632972 := by exact prefixLift 5632972
  have htrace : WordTrace (prefixWord ++ tailWord_5632972) baseStart_5632972 baseEnd_5632972 := by
    simpa [prefixWord, tailWord_5632972, baseEnd_5632972] using wordTrace_append hprefix tailTrace_5632972
  have hstable : (prefixWord ++ tailWord_5632972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632972).length < 2 ^ (prefixWord ++ tailWord_5632972).sum := by decide
  have hdescent : baseEnd_5632972 < baseStart_5632972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632986 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_5632986 : Nat := 118140960795 + 5632986 * 2 ^ 59
def prefixEnd_5632986 : Nat := 4983230072969 + 3 ^ 40 * 5632986 * 2
def baseEnd_5632986 : Nat := 2892429338047403150069375

theorem tailTrace_5632986 : CollatzResearch.WordTrace tailWord_5632986 prefixEnd_5632986 2892429338047403150069375 := by
  unfold tailWord_5632986
  simp only [CollatzResearch.WordTrace]
  refine ⟨51362969492665308565549703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136967918647107489508132541 51362969492665308565549703)
  ·
    refine ⟨77044454238997962848324555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51362969492665308565549703 77044454238997962848324555)
    ·
      refine ⟨115566681358496944272486833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77044454238997962848324555 115566681358496944272486833)
      ·
        refine ⟨86675011018872708204365125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115566681358496944272486833 86675011018872708204365125)
        ·
          refine ⟨16251564566038632788318461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86675011018872708204365125 16251564566038632788318461)
          ·
            refine ⟨6094336712264487295619423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16251564566038632788318461 6094336712264487295619423)
            ·
              refine ⟨9141505068396730943429135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094336712264487295619423 9141505068396730943429135)
              ·
                refine ⟨13712257602595096415143703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9141505068396730943429135 13712257602595096415143703)
                ·
                  refine ⟨20568386403892644622715555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13712257602595096415143703 20568386403892644622715555)
                  ·
                    refine ⟨30852579605838966934073333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20568386403892644622715555 30852579605838966934073333)
                    ·
                      refine ⟨2892429338047403150069375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30852579605838966934073333 2892429338047403150069375)
                      ·
                        rfl

theorem cell23_5632986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_5632986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632986 prefixEnd_5632986 := by exact prefixLift 5632986
  have htrace : WordTrace (prefixWord ++ tailWord_5632986) baseStart_5632986 baseEnd_5632986 := by
    simpa [prefixWord, tailWord_5632986, baseEnd_5632986] using wordTrace_append hprefix tailTrace_5632986
  have hstable : (prefixWord ++ tailWord_5632986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632986).length < 2 ^ (prefixWord ++ tailWord_5632986).sum := by decide
  have hdescent : baseEnd_5632986 < baseStart_5632986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5632994 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_5632994 : Nat := 118140960795 + 5632994 * 2 ^ 59
def prefixEnd_5632994 : Nat := 4983230072969 + 3 ^ 40 * 5632994 * 2
def baseEnd_5632994 : Nat := 2892433445892639118769339

theorem tailTrace_5632994 : CollatzResearch.WordTrace tailWord_5632994 prefixEnd_5632994 2892433445892639118769339 := by
  unfold tailWord_5632994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51363042438658062907122509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136968113169754834418993357 51363042438658062907122509)
  ·
    refine ⟨19261140914496773590170941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51363042438658062907122509 19261140914496773590170941)
    ·
      refine ⟨7222927842936290096314103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19261140914496773590170941 7222927842936290096314103)
      ·
        refine ⟨10834391764404435144471155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222927842936290096314103 10834391764404435144471155)
        ·
          refine ⟨16251587646606652716706733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10834391764404435144471155 16251587646606652716706733)
          ·
            refine ⟨6094345367477494768765025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16251587646606652716706733 6094345367477494768765025)
            ·
              refine ⟨4570759025608121076573769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6094345367477494768765025 4570759025608121076573769)
              ·
                refine ⟨3428069269206090807430327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570759025608121076573769 3428069269206090807430327)
                ·
                  refine ⟨5142103903809136211145491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428069269206090807430327 5142103903809136211145491)
                  ·
                    refine ⟨7713155855713704316718237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5142103903809136211145491 7713155855713704316718237)
                    ·
                      refine ⟨2892433445892639118769339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713155855713704316718237 2892433445892639118769339)
                      ·
                        rfl

theorem cell23_5632994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_5632994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5632994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5632994 prefixEnd_5632994 := by exact prefixLift 5632994
  have htrace : WordTrace (prefixWord ++ tailWord_5632994) baseStart_5632994 baseEnd_5632994 := by
    simpa [prefixWord, tailWord_5632994, baseEnd_5632994] using wordTrace_append hprefix tailTrace_5632994
  have hstable : (prefixWord ++ tailWord_5632994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5632994).length < 2 ^ (prefixWord ++ tailWord_5632994).sum := by decide
  have hdescent : baseEnd_5632994 < baseStart_5632994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5632994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633006 : List Nat := [4, 1, 2, 1, 4, 2, 1, 8]
def baseStart_5633006 : Nat := 118140960795 + 5633006 * 2 ^ 59
def prefixEnd_5633006 : Nat := 4983230072969 + 3 ^ 40 * 5633006 * 2
def baseEnd_5633006 : Nat := 107127392876314558215529

theorem tailTrace_5633006 : CollatzResearch.WordTrace tailWord_5633006 prefixEnd_5633006 107127392876314558215529 := by
  unfold tailWord_5633006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681575928823597209740859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136968404953725851785284581 25681575928823597209740859)
  ·
    refine ⟨38522363893235395814611289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25681575928823597209740859 38522363893235395814611289)
    ·
      refine ⟨28891772919926546860958467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38522363893235395814611289 28891772919926546860958467)
      ·
        refine ⟨43337659379889820291437701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28891772919926546860958467 43337659379889820291437701)
        ·
          refine ⟨8125811133729341304644569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43337659379889820291437701 8125811133729341304644569)
          ·
            refine ⟨6094358350297005978483427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8125811133729341304644569 6094358350297005978483427)
            ·
              refine ⟨9141537525445508967725141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094358350297005978483427 9141537525445508967725141)
              ·
                refine ⟨107127392876314558215529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9141537525445508967725141 107127392876314558215529)
                ·
                  rfl

theorem cell23_5633006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_5633006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633006 prefixEnd_5633006 := by exact prefixLift 5633006
  have htrace : WordTrace (prefixWord ++ tailWord_5633006) baseStart_5633006 baseEnd_5633006 := by
    simpa [prefixWord, tailWord_5633006, baseEnd_5633006] using wordTrace_append hprefix tailTrace_5633006
  have hstable : (prefixWord ++ tailWord_5633006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633006).length < 2 ^ (prefixWord ++ tailWord_5633006).sum := by decide
  have hdescent : baseEnd_5633006 < baseStart_5633006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633119 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_5633119 : Nat := 118140960795 + 5633119 * 2 ^ 59
def prefixEnd_5633119 : Nat := 4983230072969 + 3 ^ 40 * 5633119 * 2
def baseEnd_5633119 : Nat := 2892497630974451129706263

theorem tailTrace_5633119 : CollatzResearch.WordTrace tailWord_5633119 prefixEnd_5633119 2892497630974451129706263 := by
  unfold tailWord_5633119
  simp only [CollatzResearch.WordTrace]
  refine ⟨205456728879179397976790411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136971152586119598651193607 205456728879179397976790411)
  ·
    refine ⟨308185093318769096965185617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205456728879179397976790411 308185093318769096965185617)
    ·
      refine ⟨231138819989076822723889213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308185093318769096965185617 231138819989076822723889213)
      ·
        refine ⟨86677057495903808521458455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231138819989076822723889213 86677057495903808521458455)
        ·
          refine ⟨130015586243855712782187683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86677057495903808521458455 130015586243855712782187683)
          ·
            refine ⟨195023379365783569173281525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130015586243855712782187683 195023379365783569173281525)
            ·
              refine ⟨18283441815542209609995143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195023379365783569173281525 18283441815542209609995143)
              ·
                refine ⟨27425162723313314414992715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18283441815542209609995143 27425162723313314414992715)
                ·
                  refine ⟨41137744084969971622489073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27425162723313314414992715 41137744084969971622489073)
                  ·
                    refine ⟨30853308063727478716866805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41137744084969971622489073 30853308063727478716866805)
                    ·
                      refine ⟨2892497630974451129706263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30853308063727478716866805 2892497630974451129706263)
                      ·
                        rfl

theorem cell23_5633119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_5633119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633119 prefixEnd_5633119 := by exact prefixLift 5633119
  have htrace : WordTrace (prefixWord ++ tailWord_5633119) baseStart_5633119 baseEnd_5633119 := by
    simpa [prefixWord, tailWord_5633119, baseEnd_5633119] using wordTrace_append hprefix tailTrace_5633119
  have hstable : (prefixWord ++ tailWord_5633119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633119).length < 2 ^ (prefixWord ++ tailWord_5633119).sum := by decide
  have hdescent : baseEnd_5633119 < baseStart_5633119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633159 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5633159 : Nat := 118140960795 + 5633159 * 2 ^ 59
def prefixEnd_5633159 : Nat := 4983230072969 + 3 ^ 40 * 5633159 * 2
def baseEnd_5633159 : Nat := 2892518170200630973206079

theorem tailTrace_5633159 : CollatzResearch.WordTrace tailWord_5633159 prefixEnd_5633159 2892518170200630973206079 := by
  unfold tailWord_5633159
  simp only [CollatzResearch.WordTrace]
  refine ⟨205458187799034484808246531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136972125199356323205497687 205458187799034484808246531)
  ·
    refine ⟨308187281698551727212369797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205458187799034484808246531 308187281698551727212369797)
    ·
      refine ⟨57785115318478448852319337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308187281698551727212369797 57785115318478448852319337)
      ·
        refine ⟨43338836488858836639239503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57785115318478448852319337 43338836488858836639239503)
        ·
          refine ⟨65008254733288254958859255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43338836488858836639239503 65008254733288254958859255)
          ·
            refine ⟨97512382099932382438288883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65008254733288254958859255 97512382099932382438288883)
            ·
              refine ⟨146268573149898573657433325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97512382099932382438288883 146268573149898573657433325)
              ·
                refine ⟨54850714931211965121537497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146268573149898573657433325 54850714931211965121537497)
                ·
                  refine ⟨41138036198408973841153123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54850714931211965121537497 41138036198408973841153123)
                  ·
                    refine ⟨61707054297613460761729685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41138036198408973841153123 61707054297613460761729685)
                    ·
                      refine ⟨2892518170200630973206079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61707054297613460761729685 2892518170200630973206079)
                      ·
                        rfl

theorem cell23_5633159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5633159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633159 prefixEnd_5633159 := by exact prefixLift 5633159
  have htrace : WordTrace (prefixWord ++ tailWord_5633159) baseStart_5633159 baseEnd_5633159 := by
    simpa [prefixWord, tailWord_5633159, baseEnd_5633159] using wordTrace_append hprefix tailTrace_5633159
  have hstable : (prefixWord ++ tailWord_5633159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633159).length < 2 ^ (prefixWord ++ tailWord_5633159).sum := by decide
  have hdescent : baseEnd_5633159 < baseStart_5633159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633197 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_5633197 : Nat := 118140960795 + 5633197 * 2 ^ 59
def prefixEnd_5633197 : Nat := 4983230072969 + 3 ^ 40 * 5633197 * 2
def baseEnd_5633197 : Nat := 2892537682465501824530905

theorem tailTrace_5633197 : CollatzResearch.WordTrace tailWord_5633197 prefixEnd_5633197 2892537682465501824530905 := by
  unfold tailWord_5633197
  simp only [CollatzResearch.WordTrace]
  refine ⟨205459573772896817298129845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136973049181931211532086563 205459573772896817298129845)
  ·
    refine ⟨19261835041209076621699673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205459573772896817298129845 19261835041209076621699673)
    ·
      refine ⟨14446376280906807466274755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19261835041209076621699673 14446376280906807466274755)
      ·
        refine ⟨21669564421360211199412133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446376280906807466274755 21669564421360211199412133)
        ·
          refine ⟨4063043329005039599889775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21669564421360211199412133 4063043329005039599889775)
          ·
            refine ⟨6094564993507559399834663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063043329005039599889775 6094564993507559399834663)
            ·
              refine ⟨9141847490261339099751995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094564993507559399834663 9141847490261339099751995)
              ·
                refine ⟨13712771235392008649627993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9141847490261339099751995 13712771235392008649627993)
                ·
                  refine ⟨10284578426544006487220995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13712771235392008649627993 10284578426544006487220995)
                  ·
                    refine ⟨15426867639816009730831493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10284578426544006487220995 15426867639816009730831493)
                    ·
                      refine ⟨2892537682465501824530905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15426867639816009730831493 2892537682465501824530905)
                      ·
                        rfl

theorem cell23_5633197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_5633197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633197 prefixEnd_5633197 := by exact prefixLift 5633197
  have htrace : WordTrace (prefixWord ++ tailWord_5633197) baseStart_5633197 baseEnd_5633197 := by
    simpa [prefixWord, tailWord_5633197, baseEnd_5633197] using wordTrace_append hprefix tailTrace_5633197
  have hstable : (prefixWord ++ tailWord_5633197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633197).length < 2 ^ (prefixWord ++ tailWord_5633197).sum := by decide
  have hdescent : baseEnd_5633197 < baseStart_5633197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633220 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 6]
def baseStart_5633220 : Nat := 118140960795 + 5633220 * 2 ^ 59
def prefixEnd_5633220 : Nat := 4983230072969 + 3 ^ 40 * 5633220 * 2
def baseEnd_5633220 : Nat := 321394388057839470504811

theorem tailTrace_5633220 : CollatzResearch.WordTrace tailWord_5633220 prefixEnd_5633220 321394388057839470504811 := by
  unfold tailWord_5633220
  simp only [CollatzResearch.WordTrace]
  refine ⟨102730206325906746113108557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136973608434542328150811409 102730206325906746113108557)
  ·
    refine ⟨38523827372215029792415709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102730206325906746113108557 38523827372215029792415709)
    ·
      refine ⟨14446435264580636172155891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38523827372215029792415709 14446435264580636172155891)
      ·
        refine ⟨21669652896870954258233837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446435264580636172155891 21669652896870954258233837)
        ·
          refine ⟨8126119836326607846837689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21669652896870954258233837 8126119836326607846837689)
          ·
            refine ⟨6094589877244955885128267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8126119836326607846837689 6094589877244955885128267)
            ·
              refine ⟨9141884815867433827692401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094589877244955885128267 9141884815867433827692401)
              ·
                refine ⟨6856413611900575370769301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9141884815867433827692401 6856413611900575370769301)
                ·
                  refine ⟨321394388057839470504811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6856413611900575370769301 321394388057839470504811)
                  ·
                    rfl

theorem cell23_5633220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_5633220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633220 prefixEnd_5633220 := by exact prefixLift 5633220
  have htrace : WordTrace (prefixWord ++ tailWord_5633220) baseStart_5633220 baseEnd_5633220 := by
    simpa [prefixWord, tailWord_5633220, baseEnd_5633220] using wordTrace_append hprefix tailTrace_5633220
  have hstable : (prefixWord ++ tailWord_5633220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633220).length < 2 ^ (prefixWord ++ tailWord_5633220).sum := by decide
  have hdescent : baseEnd_5633220 < baseStart_5633220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633223 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_5633223 : Nat := 118140960795 + 5633223 * 2 ^ 59
def prefixEnd_5633223 : Nat := 4983230072969 + 3 ^ 40 * 5633223 * 2
def baseEnd_5633223 : Nat := 2892551032962518722805785

theorem tailTrace_5633223 : CollatzResearch.WordTrace tailWord_5633223 prefixEnd_5633223 2892551032962518722805785 := by
  unfold tailWord_5633223
  simp only [CollatzResearch.WordTrace]
  refine ⟨205460522070802623738576323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136973681380535082492384215 205460522070802623738576323)
  ·
    refine ⟨308190783106203935607864485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205460522070802623738576323 308190783106203935607864485)
    ·
      refine ⟨57785771832413237926474591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308190783106203935607864485 57785771832413237926474591)
      ·
        refine ⟨86678657748619856889711887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57785771832413237926474591 86678657748619856889711887)
        ·
          refine ⟨130017986622929785334567831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86678657748619856889711887 130017986622929785334567831)
          ·
            refine ⟨195026979934394678001851747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130017986622929785334567831 195026979934394678001851747)
            ·
              refine ⟨292540469901592017002777621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195026979934394678001851747 292540469901592017002777621)
              ·
                refine ⟨13712834526637125797005201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292540469901592017002777621 13712834526637125797005201)
                ·
                  refine ⟨10284625894977844347753901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13712834526637125797005201 10284625894977844347753901)
                  ·
                    refine ⟨3856734710616691630407713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10284625894977844347753901 3856734710616691630407713)
                    ·
                      refine ⟨2892551032962518722805785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856734710616691630407713 2892551032962518722805785)
                      ·
                        rfl

theorem cell23_5633223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_5633223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633223 prefixEnd_5633223 := by exact prefixLift 5633223
  have htrace : WordTrace (prefixWord ++ tailWord_5633223) baseStart_5633223 baseEnd_5633223 := by
    simpa [prefixWord, tailWord_5633223, baseEnd_5633223] using wordTrace_append hprefix tailTrace_5633223
  have hstable : (prefixWord ++ tailWord_5633223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633223).length < 2 ^ (prefixWord ++ tailWord_5633223).sum := by decide
  have hdescent : baseEnd_5633223 < baseStart_5633223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633256 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5633256 : Nat := 118140960795 + 5633256 * 2 ^ 59
def prefixEnd_5633256 : Nat := 4983230072969 + 3 ^ 40 * 5633256 * 2
def baseEnd_5633256 : Nat := 2892567977824117093693133

theorem tailTrace_5633256 : CollatzResearch.WordTrace tailWord_5633256 prefixEnd_5633256 2892567977824117093693133 := by
  unfold tailWord_5633256
  simp only [CollatzResearch.WordTrace]
  refine ⟨102730862839841535187263811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136974483786455380249685081 102730862839841535187263811)
  ·
    refine ⟨154096294259762302780895717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102730862839841535187263811 154096294259762302780895717)
    ·
      refine ⟨28893055173705431771417947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154096294259762302780895717 28893055173705431771417947)
      ·
        refine ⟨43339582760558147657126921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28893055173705431771417947 43339582760558147657126921)
        ·
          refine ⟨32504687070418610742845191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43339582760558147657126921 32504687070418610742845191)
          ·
            refine ⟨48757030605627916114267787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32504687070418610742845191 48757030605627916114267787)
            ·
              refine ⟨73135545908441874171401681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48757030605627916114267787 73135545908441874171401681)
              ·
                refine ⟨54851659431331405628551261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73135545908441874171401681 54851659431331405628551261)
                ·
                  refine ⟨20569372286749277110706723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54851659431331405628551261 20569372286749277110706723)
                  ·
                    refine ⟨30854058430123915666060085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20569372286749277110706723 30854058430123915666060085)
                    ·
                      refine ⟨2892567977824117093693133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30854058430123915666060085 2892567977824117093693133)
                      ·
                        rfl

theorem cell23_5633256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5633256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633256 prefixEnd_5633256 := by exact prefixLift 5633256
  have htrace : WordTrace (prefixWord ++ tailWord_5633256) baseStart_5633256 baseEnd_5633256 := by
    simpa [prefixWord, tailWord_5633256, baseEnd_5633256] using wordTrace_append hprefix tailTrace_5633256
  have hstable : (prefixWord ++ tailWord_5633256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633256).length < 2 ^ (prefixWord ++ tailWord_5633256).sum := by decide
  have hdescent : baseEnd_5633256 < baseStart_5633256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633273 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_5633273 : Nat := 118140960795 + 5633273 * 2 ^ 59
def prefixEnd_5633273 : Nat := 4983230072969 + 3 ^ 40 * 5633273 * 2
def baseEnd_5633273 : Nat := 2892576706995243527180555

theorem tailTrace_5633273 : CollatzResearch.WordTrace tailWord_5633273 prefixEnd_5633273 2892576706995243527180555 := by
  unfold tailWord_5633273
  simp only [CollatzResearch.WordTrace]
  refine ⟨205462345720621482277896473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136974897147080988185264315 205462345720621482277896473)
  ·
    refine ⟨154096759290466111708422355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205462345720621482277896473 154096759290466111708422355)
    ·
      refine ⟨231145138935699167562633533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154096759290466111708422355 231145138935699167562633533)
      ·
        refine ⟨86679427100887187835987575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231145138935699167562633533 86679427100887187835987575)
        ·
          refine ⟨130019140651330781753981363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86679427100887187835987575 130019140651330781753981363)
          ·
            refine ⟨195028710976996172630972045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130019140651330781753981363 195028710976996172630972045)
            ·
              refine ⟨73135766616373564736614517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195028710976996172630972045 73135766616373564736614517)
              ·
                refine ⟨6856478120285021694057611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73135766616373564736614517 6856478120285021694057611)
                ·
                  refine ⟨10284717180427532541086417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6856478120285021694057611 10284717180427532541086417)
                  ·
                    refine ⟨7713537885320649405814813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10284717180427532541086417 7713537885320649405814813)
                    ·
                      refine ⟨2892576706995243527180555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713537885320649405814813 2892576706995243527180555)
                      ·
                        rfl

theorem cell23_5633273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_5633273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633273 prefixEnd_5633273 := by exact prefixLift 5633273
  have htrace : WordTrace (prefixWord ++ tailWord_5633273) baseStart_5633273 baseEnd_5633273 := by
    simpa [prefixWord, tailWord_5633273, baseEnd_5633273] using wordTrace_append hprefix tailTrace_5633273
  have hstable : (prefixWord ++ tailWord_5633273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633273).length < 2 ^ (prefixWord ++ tailWord_5633273).sum := by decide
  have hdescent : baseEnd_5633273 < baseStart_5633273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633303 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_5633303 : Nat := 118140960795 + 5633303 * 2 ^ 59
def prefixEnd_5633303 : Nat := 4983230072969 + 3 ^ 40 * 5633303 * 2
def baseEnd_5633303 : Nat := 2892592111414878409805417

theorem tailTrace_5633303 : CollatzResearch.WordTrace tailWord_5633303 prefixEnd_5633303 2892592111414878409805417 := by
  unfold tailWord_5633303
  simp only [CollatzResearch.WordTrace]
  refine ⟨205463439910512797401488563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136975626607008531600992375 205463439910512797401488563)
  ·
    refine ⟨308195159865769196102232845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205463439910512797401488563 308195159865769196102232845)
    ·
      refine ⟨115573184949663448538337317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308195159865769196102232845 115573184949663448538337317)
      ·
        refine ⟨21669972178061896600938247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115573184949663448538337317 21669972178061896600938247)
        ·
          refine ⟨32504958267092844901407371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21669972178061896600938247 32504958267092844901407371)
          ·
            refine ⟨48757437400639267352111057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32504958267092844901407371 48757437400639267352111057)
            ·
              refine ⟨36568078050479450514083293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48757437400639267352111057 36568078050479450514083293)
              ·
                refine ⟨13713029268929793942781235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36568078050479450514083293 13713029268929793942781235)
                ·
                  refine ⟨20569543903394690914171853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713029268929793942781235 20569543903394690914171853)
                  ·
                    refine ⟨7713578963773009092814445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20569543903394690914171853 7713578963773009092814445)
                    ·
                      refine ⟨2892592111414878409805417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713578963773009092814445 2892592111414878409805417)
                      ·
                        rfl

theorem cell23_5633303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_5633303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633303 prefixEnd_5633303 := by exact prefixLift 5633303
  have htrace : WordTrace (prefixWord ++ tailWord_5633303) baseStart_5633303 baseEnd_5633303 := by
    simpa [prefixWord, tailWord_5633303, baseEnd_5633303] using wordTrace_append hprefix tailTrace_5633303
  have hstable : (prefixWord ++ tailWord_5633303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633303).length < 2 ^ (prefixWord ++ tailWord_5633303).sum := by decide
  have hdescent : baseEnd_5633303 < baseStart_5633303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633320 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5633320 : Nat := 118140960795 + 5633320 * 2 ^ 59
def prefixEnd_5633320 : Nat := 4983230072969 + 3 ^ 40 * 5633320 * 2
def baseEnd_5633320 : Nat := 2892600840586004843292839

theorem tailTrace_5633320 : CollatzResearch.WordTrace tailWord_5633320 prefixEnd_5633320 2892600840586004843292839 := by
  unfold tailWord_5633320
  simp only [CollatzResearch.WordTrace]
  refine ⟨102732029975725604652428707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136976039967634139536571609 102732029975725604652428707)
  ·
    refine ⟨154098044963588406978643061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102732029975725604652428707 154098044963588406978643061)
    ·
      refine ⟨14446691715336413154247787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154098044963588406978643061 14446691715336413154247787)
      ·
        refine ⟨21670037573004619731371681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446691715336413154247787 21670037573004619731371681)
        ·
          refine ⟨16252528179753464798528761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21670037573004619731371681 16252528179753464798528761)
          ·
            refine ⟨12189396134815098598896571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16252528179753464798528761 12189396134815098598896571)
            ·
              refine ⟨18284094202222647898344857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12189396134815098598896571 18284094202222647898344857)
              ·
                refine ⟨13713070651666985923758643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18284094202222647898344857 13713070651666985923758643)
                ·
                  refine ⟨20569605977500478885637965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713070651666985923758643 20569605977500478885637965)
                  ·
                    refine ⟨7713602241562679582114237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20569605977500478885637965 7713602241562679582114237)
                    ·
                      refine ⟨2892600840586004843292839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713602241562679582114237 2892600840586004843292839)
                      ·
                        rfl

theorem cell23_5633320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5633320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633320 prefixEnd_5633320 := by exact prefixLift 5633320
  have htrace : WordTrace (prefixWord ++ tailWord_5633320) baseStart_5633320 baseEnd_5633320 := by
    simpa [prefixWord, tailWord_5633320, baseEnd_5633320] using wordTrace_append hprefix tailTrace_5633320
  have hstable : (prefixWord ++ tailWord_5633320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633320).length < 2 ^ (prefixWord ++ tailWord_5633320).sum := by decide
  have hdescent : baseEnd_5633320 < baseStart_5633320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633336 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_5633336 : Nat := 118140960795 + 5633336 * 2 ^ 59
def prefixEnd_5633336 : Nat := 4983230072969 + 3 ^ 40 * 5633336 * 2
def baseEnd_5633336 : Nat := 964203018758825593564255

theorem tailTrace_5633336 : CollatzResearch.WordTrace tailWord_5633336 prefixEnd_5633336 964203018758825593564255 := by
  unfold tailWord_5633336
  simp only [CollatzResearch.WordTrace]
  refine ⟨102732321759696622018719931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136976429012928829358293241 102732321759696622018719931)
  ·
    refine ⟨154098482639544933028079897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102732321759696622018719931 154098482639544933028079897)
    ·
      refine ⟨115573861979658699771059923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154098482639544933028079897 115573861979658699771059923)
      ·
        refine ⟨173360792969488049656589885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115573861979658699771059923 173360792969488049656589885)
        ·
          refine ⟨65010297363558018621221207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173360792969488049656589885 65010297363558018621221207)
          ·
            refine ⟨97515446045337027931831811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65010297363558018621221207 97515446045337027931831811)
            ·
              refine ⟨146273169068005541897747717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97515446045337027931831811 146273169068005541897747717)
              ·
                refine ⟨27426219200251039105827697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146273169068005541897747717 27426219200251039105827697)
                ·
                  refine ⟨20569664400188279329370773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27426219200251039105827697 20569664400188279329370773)
                  ·
                    refine ⟨964203018758825593564255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20569664400188279329370773 964203018758825593564255)
                    ·
                      rfl

theorem cell23_5633336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_5633336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633336 prefixEnd_5633336 := by exact prefixLift 5633336
  have htrace : WordTrace (prefixWord ++ tailWord_5633336) baseStart_5633336 baseEnd_5633336 := by
    simpa [prefixWord, tailWord_5633336, baseEnd_5633336] using wordTrace_append hprefix tailTrace_5633336
  have hstable : (prefixWord ++ tailWord_5633336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633336).length < 2 ^ (prefixWord ++ tailWord_5633336).sum := by decide
  have hdescent : baseEnd_5633336 < baseStart_5633336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633360 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2]
def baseStart_5633360 : Nat := 118140960795 + 5633360 * 2 ^ 59
def prefixEnd_5633360 : Nat := 4983230072969 + 3 ^ 40 * 5633360 * 2
def baseEnd_5633360 : Nat := 2892621379812184686792655

theorem tailTrace_5633360 : CollatzResearch.WordTrace tailWord_5633360 prefixEnd_5633360 2892621379812184686792655 := by
  unfold tailWord_5633360
  simp only [CollatzResearch.WordTrace]
  refine ⟨102732759435653148068156767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136977012580870864090875689 102732759435653148068156767)
  ·
    refine ⟨154099139153479722102235151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102732759435653148068156767 154099139153479722102235151)
    ·
      refine ⟨231148708730219583153352727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154099139153479722102235151 231148708730219583153352727)
      ·
        refine ⟨346723063095329374730029091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231148708730219583153352727 346723063095329374730029091)
        ·
          refine ⟨520084594642994062095043637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346723063095329374730029091 520084594642994062095043637)
          ·
            refine ⟨48757930747780693321410341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 520084594642994062095043637 48757930747780693321410341)
            ·
              refine ⟨9142112015208879997764439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48757930747780693321410341 9142112015208879997764439)
              ·
                refine ⟨13713168022813319996646659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142112015208879997764439 13713168022813319996646659)
                ·
                  refine ⟨20569752034219979994969989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713168022813319996646659 20569752034219979994969989)
                  ·
                    refine ⟨3856828506416246249056873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20569752034219979994969989 3856828506416246249056873)
                    ·
                      refine ⟨2892621379812184686792655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3856828506416246249056873 2892621379812184686792655)
                      ·
                        rfl

theorem cell23_5633360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 4, 2].length) (baseStart_5633360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633360 prefixEnd_5633360 := by exact prefixLift 5633360
  have htrace : WordTrace (prefixWord ++ tailWord_5633360) baseStart_5633360 baseEnd_5633360 := by
    simpa [prefixWord, tailWord_5633360, baseEnd_5633360] using wordTrace_append hprefix tailTrace_5633360
  have hstable : (prefixWord ++ tailWord_5633360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633360).length < 2 ^ (prefixWord ++ tailWord_5633360).sum := by decide
  have hdescent : baseEnd_5633360 < baseStart_5633360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633393 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_5633393 : Nat := 118140960795 + 5633393 * 2 ^ 59
def prefixEnd_5633393 : Nat := 4983230072969 + 3 ^ 40 * 5633393 * 2
def baseEnd_5633393 : Nat := 2892638324673783057680003

theorem tailTrace_5633393 : CollatzResearch.WordTrace tailWord_5633393 prefixEnd_5633393 2892638324673783057680003 := by
  unfold tailWord_5633393
  simp only [CollatzResearch.WordTrace]
  refine ⟨205466722480186742772264833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136977814986791161848176555 205466722480186742772264833)
  ·
    refine ⟨154100041860140057079198625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205466722480186742772264833 154100041860140057079198625)
    ·
      refine ⟨115575031395105042809398969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154100041860140057079198625 115575031395105042809398969)
      ·
        refine ⟨86681273546328782107049227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115575031395105042809398969 86681273546328782107049227)
        ·
          refine ⟨130021910319493173160573841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86681273546328782107049227 130021910319493173160573841)
          ·
            refine ⟨97516432739619879870430381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130021910319493173160573841 97516432739619879870430381)
            ·
              refine ⟨36568662277357454951411393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97516432739619879870430381 36568662277357454951411393)
              ·
                refine ⟨27426496708018091213558545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36568662277357454951411393 27426496708018091213558545)
                ·
                  refine ⟨20569872531013568410168909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27426496708018091213558545 20569872531013568410168909)
                  ·
                    refine ⟨7713702199130088153813341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20569872531013568410168909 7713702199130088153813341)
                    ·
                      refine ⟨2892638324673783057680003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713702199130088153813341 2892638324673783057680003)
                      ·
                        rfl

theorem cell23_5633393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_5633393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633393 prefixEnd_5633393 := by exact prefixLift 5633393
  have htrace : WordTrace (prefixWord ++ tailWord_5633393) baseStart_5633393 baseEnd_5633393 := by
    simpa [prefixWord, tailWord_5633393, baseEnd_5633393] using wordTrace_append hprefix tailTrace_5633393
  have hstable : (prefixWord ++ tailWord_5633393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633393).length < 2 ^ (prefixWord ++ tailWord_5633393).sum := by decide
  have hdescent : baseEnd_5633393 < baseStart_5633393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633433 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_5633433 : Nat := 118140960795 + 5633433 * 2 ^ 59
def prefixEnd_5633433 : Nat := 4983230072969 + 3 ^ 40 * 5633433 * 2
def baseEnd_5633433 : Nat := 2892658863899962901179819

theorem tailTrace_5633433 : CollatzResearch.WordTrace tailWord_5633433 prefixEnd_5633433 2892658863899962901179819 := by
  unfold tailWord_5633433
  simp only [CollatzResearch.WordTrace]
  refine ⟨205468181400041829603720953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136978787600027886402480635 205468181400041829603720953)
  ·
    refine ⟨154101136050031372202790715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205468181400041829603720953 154101136050031372202790715)
    ·
      refine ⟨231151704075047058304186073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154101136050031372202790715 231151704075047058304186073)
      ·
        refine ⟨173363778056285293728139555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231151704075047058304186073 173363778056285293728139555)
        ·
          refine ⟨260045667084427940592209333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173363778056285293728139555 260045667084427940592209333)
          ·
            refine ⟨24379281289165119430519625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260045667084427940592209333 24379281289165119430519625)
            ·
              refine ⟨18284460966873839572889719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24379281289165119430519625 18284460966873839572889719)
              ·
                refine ⟨27426691450310759359334579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18284460966873839572889719 27426691450310759359334579)
                ·
                  refine ⟨41140037175466139039001869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27426691450310759359334579 41140037175466139039001869)
                  ·
                    refine ⟨15427513940799802139625701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41140037175466139039001869 15427513940799802139625701)
                    ·
                      refine ⟨2892658863899962901179819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15427513940799802139625701 2892658863899962901179819)
                      ·
                        rfl

theorem cell23_5633433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_5633433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633433 prefixEnd_5633433 := by exact prefixLift 5633433
  have htrace : WordTrace (prefixWord ++ tailWord_5633433) baseStart_5633433 baseEnd_5633433 := by
    simpa [prefixWord, tailWord_5633433, baseEnd_5633433] using wordTrace_append hprefix tailTrace_5633433
  have hstable : (prefixWord ++ tailWord_5633433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633433).length < 2 ^ (prefixWord ++ tailWord_5633433).sum := by decide
  have hdescent : baseEnd_5633433 < baseStart_5633433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633470 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_5633470 : Nat := 118140960795 + 5633470 * 2 ^ 59
def prefixEnd_5633470 : Nat := 4983230072969 + 3 ^ 40 * 5633470 * 2
def baseEnd_5633470 : Nat := 2892677862684179256417149

theorem tailTrace_5633470 : CollatzResearch.WordTrace tailWord_5633470 prefixEnd_5633470 2892677862684179256417149 := by
  unfold tailWord_5633470
  simp only [CollatzResearch.WordTrace]
  refine ⟨25683691362613473115352233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136979687267271856615211909 25683691362613473115352233)
  ·
    refine ⟨19262768521960104836514175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25683691362613473115352233 19262768521960104836514175)
    ·
      refine ⟨28894152782940157254771263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19262768521960104836514175 28894152782940157254771263)
      ·
        refine ⟨43341229174410235882156895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28894152782940157254771263 43341229174410235882156895)
        ·
          refine ⟨65011843761615353823235343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43341229174410235882156895 65011843761615353823235343)
          ·
            refine ⟨97517765642423030734853015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65011843761615353823235343 97517765642423030734853015)
            ·
              refine ⟨146276648463634546102279523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97517765642423030734853015 146276648463634546102279523)
              ·
                refine ⟨219414972695451819153419285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146276648463634546102279523 219414972695451819153419285)
                ·
                  refine ⟨10285076845099304022816529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219414972695451819153419285 10285076845099304022816529)
                  ·
                    refine ⟨7713807633824478017112397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10285076845099304022816529 7713807633824478017112397)
                    ·
                      refine ⟨2892677862684179256417149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713807633824478017112397 2892677862684179256417149)
                      ·
                        rfl

theorem cell23_5633470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_5633470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633470 prefixEnd_5633470 := by exact prefixLift 5633470
  have htrace : WordTrace (prefixWord ++ tailWord_5633470) baseStart_5633470 baseEnd_5633470 := by
    simpa [prefixWord, tailWord_5633470, baseEnd_5633470] using wordTrace_append hprefix tailTrace_5633470
  have hstable : (prefixWord ++ tailWord_5633470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633470).length < 2 ^ (prefixWord ++ tailWord_5633470).sum := by decide
  have hdescent : baseEnd_5633470 < baseStart_5633470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633483 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3]
def baseStart_5633483 : Nat := 118140960795 + 5633483 * 2 ^ 59
def prefixEnd_5633483 : Nat := 4983230072969 + 3 ^ 40 * 5633483 * 2
def baseEnd_5633483 : Nat := 2892684537932687705554589

theorem tailTrace_5633483 : CollatzResearch.WordTrace tailWord_5633483 prefixEnd_5633483 2892684537932687705554589 := by
  unfold tailWord_5633483
  simp only [CollatzResearch.WordTrace]
  refine ⟨205470005049860688143041103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136980003366573792095360735 205470005049860688143041103)
  ·
    refine ⟨308205007574791032214561655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205470005049860688143041103 308205007574791032214561655)
    ·
      refine ⟨462307511362186548321842483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308205007574791032214561655 462307511362186548321842483)
      ·
        refine ⟨693461267043279822482763725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462307511362186548321842483 693461267043279822482763725)
        ·
          refine ⟨260047975141229933431036397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693461267043279822482763725 260047975141229933431036397)
          ·
            refine ⟨97517990677961225036638649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260047975141229933431036397 97517990677961225036638649)
            ·
              refine ⟨73138493008470918777478987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97517990677961225036638649 73138493008470918777478987)
              ·
                refine ⟨109707739512706378166218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73138493008470918777478987 109707739512706378166218481)
                ·
                  refine ⟨82280804634529783624663861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109707739512706378166218481 82280804634529783624663861)
                  ·
                    refine ⟨7713825434487167214812237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82280804634529783624663861 7713825434487167214812237)
                    ·
                      refine ⟨2892684537932687705554589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7713825434487167214812237 2892684537932687705554589)
                      ·
                        rfl

theorem cell23_5633483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3].length) (baseStart_5633483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633483 prefixEnd_5633483 := by exact prefixLift 5633483
  have htrace : WordTrace (prefixWord ++ tailWord_5633483) baseStart_5633483 baseEnd_5633483 := by
    simpa [prefixWord, tailWord_5633483, baseEnd_5633483] using wordTrace_append hprefix tailTrace_5633483
  have hstable : (prefixWord ++ tailWord_5633483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633483).length < 2 ^ (prefixWord ++ tailWord_5633483).sum := by decide
  have hdescent : baseEnd_5633483 < baseStart_5633483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633511 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 1, 4]
def baseStart_5633511 : Nat := 118140960795 + 5633511 * 2 ^ 59
def prefixEnd_5633511 : Nat := 4983230072969 + 3 ^ 40 * 5633511 * 2
def baseEnd_5633511 : Nat := 964232971797004532001487

theorem tailTrace_5633511 : CollatzResearch.WordTrace tailWord_5633511 prefixEnd_5633511 964232971797004532001487 := by
  unfold tailWord_5633511
  simp only [CollatzResearch.WordTrace]
  refine ⟨205471026293759248925060387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136980684195839499283373591 205471026293759248925060387)
  ·
    refine ⟨308206539440638873387590581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205471026293759248925060387 308206539440638873387590581)
    ·
      refine ⟨28894363072559894380086617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308206539440638873387590581 28894363072559894380086617)
      ·
        refine ⟨21670772304419920785064963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28894363072559894380086617 21670772304419920785064963)
        ·
          refine ⟨32506158456629881177597445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21670772304419920785064963 32506158456629881177597445)
          ·
            refine ⟨6094904710618102720799521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32506158456629881177597445 6094904710618102720799521)
            ·
              refine ⟨4571178532963577040599641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6094904710618102720799521 4571178532963577040599641)
              ·
                refine ⟨3428383899722682780449731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571178532963577040599641 3428383899722682780449731)
                ·
                  refine ⟨5142575849584024170674597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428383899722682780449731 5142575849584024170674597)
                  ·
                    refine ⟨964232971797004532001487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5142575849584024170674597 964232971797004532001487)
                    ·
                      rfl

theorem cell23_5633511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_5633511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633511 prefixEnd_5633511 := by exact prefixLift 5633511
  have htrace : WordTrace (prefixWord ++ tailWord_5633511) baseStart_5633511 baseEnd_5633511 := by
    simpa [prefixWord, tailWord_5633511, baseEnd_5633511] using wordTrace_append hprefix tailTrace_5633511
  have hstable : (prefixWord ++ tailWord_5633511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633511).length < 2 ^ (prefixWord ++ tailWord_5633511).sum := by decide
  have hdescent : baseEnd_5633511 < baseStart_5633511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633557 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_5633557 : Nat := 118140960795 + 5633557 * 2 ^ 59
def prefixEnd_5633557 : Nat := 4983230072969 + 3 ^ 40 * 5633557 * 2
def baseEnd_5633557 : Nat := 2892722535501120416029249

theorem tailTrace_5633557 : CollatzResearch.WordTrace tailWord_5633557 prefixEnd_5633557 2892722535501120416029249 := by
  unfold tailWord_5633557
  simp only [CollatzResearch.WordTrace]
  refine ⟨205472704051592598781234925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136981802701061732520823283 205472704051592598781234925)
  ·
    refine ⟨77052264019347224542963097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205472704051592598781234925 77052264019347224542963097)
    ·
      refine ⟨57789198014510418407222323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77052264019347224542963097 57789198014510418407222323)
      ·
        refine ⟨86683797021765627610833485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57789198014510418407222323 86683797021765627610833485)
        ·
          refine ⟨32506423883162110354062557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86683797021765627610833485 32506423883162110354062557)
          ·
            refine ⟨12189908956185791382773459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32506423883162110354062557 12189908956185791382773459)
            ·
              refine ⟨18284863434278687074160189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12189908956185791382773459 18284863434278687074160189)
              ·
                refine ⟨6856823787854507652810071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18284863434278687074160189 6856823787854507652810071)
                ·
                  refine ⟨10285235681781761479215107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6856823787854507652810071 10285235681781761479215107)
                  ·
                    refine ⟨15427853522672642218822661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10285235681781761479215107 15427853522672642218822661)
                    ·
                      refine ⟨2892722535501120416029249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15427853522672642218822661 2892722535501120416029249)
                      ·
                        rfl

theorem cell23_5633557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_5633557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633557 prefixEnd_5633557 := by exact prefixLift 5633557
  have htrace : WordTrace (prefixWord ++ tailWord_5633557) baseStart_5633557 baseEnd_5633557 := by
    simpa [prefixWord, tailWord_5633557, baseEnd_5633557] using wordTrace_append hprefix tailTrace_5633557
  have hstable : (prefixWord ++ tailWord_5633557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633557).length < 2 ^ (prefixWord ++ tailWord_5633557).sum := by decide
  have hdescent : baseEnd_5633557 < baseStart_5633557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633567 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 2, 4]
def baseStart_5633567 : Nat := 118140960795 + 5633567 * 2 ^ 59
def prefixEnd_5633567 : Nat := 4983230072969 + 3 ^ 40 * 5633567 * 2
def baseEnd_5633567 : Nat := 964242556769221792301401

theorem tailTrace_5633567 : CollatzResearch.WordTrace tailWord_5633567 prefixEnd_5633567 964242556769221792301401 := by
  unfold tailWord_5633567
  simp only [CollatzResearch.WordTrace]
  refine ⟨205473068781556370489098955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136982045854370913659399303 205473068781556370489098955)
  ·
    refine ⟨308209603172334555733648433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205473068781556370489098955 308209603172334555733648433)
    ·
      refine ⟨231157202379250916800236325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308209603172334555733648433 231157202379250916800236325)
      ·
        refine ⟨43341975446109546900044311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231157202379250916800236325 43341975446109546900044311)
        ·
          refine ⟨65012963169164320350066467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43341975446109546900044311 65012963169164320350066467)
          ·
            refine ⟨97519444753746480525099701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65012963169164320350066467 97519444753746480525099701)
            ·
              refine ⟨9142447945663732549228097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97519444753746480525099701 9142447945663732549228097)
              ·
                refine ⟨6856835959247799411921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9142447945663732549228097 6856835959247799411921073)
                ·
                  refine ⟨5142626969435849558940805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6856835959247799411921073 5142626969435849558940805)
                  ·
                    refine ⟨964242556769221792301401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5142626969435849558940805 964242556769221792301401)
                    ·
                      rfl

theorem cell23_5633567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_5633567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633567 prefixEnd_5633567 := by exact prefixLift 5633567
  have htrace : WordTrace (prefixWord ++ tailWord_5633567) baseStart_5633567 baseEnd_5633567 := by
    simpa [prefixWord, tailWord_5633567, baseEnd_5633567] using wordTrace_append hprefix tailTrace_5633567
  have hstable : (prefixWord ++ tailWord_5633567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633567).length < 2 ^ (prefixWord ++ tailWord_5633567).sum := by decide
  have hdescent : baseEnd_5633567 < baseStart_5633567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633570 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5633570 : Nat := 118140960795 + 5633570 * 2 ^ 59
def prefixEnd_5633570 : Nat := 4983230072969 + 3 ^ 40 * 5633570 * 2
def baseEnd_5633570 : Nat := 2892729210749628865166689

theorem tailTrace_5633570 : CollatzResearch.WordTrace tailWord_5633570 prefixEnd_5633570 2892729210749628865166689 := by
  unfold tailWord_5633570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51368294550136375500364541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136982118800363668000972109 51368294550136375500364541)
  ·
    refine ⟨19263110456301140812636703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51368294550136375500364541 19263110456301140812636703)
    ·
      refine ⟨28894665684451711218955055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19263110456301140812636703 28894665684451711218955055)
      ·
        refine ⟨43341998526677566828432583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28894665684451711218955055 43341998526677566828432583)
        ·
          refine ⟨65012997790016350242648875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43341998526677566828432583 65012997790016350242648875)
          ·
            refine ⟨97519496685024525363973313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65012997790016350242648875 97519496685024525363973313)
            ·
              refine ⟨73139622513768394022979985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97519496685024525363973313 73139622513768394022979985)
              ·
                refine ⟨54854716885326295517234989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73139622513768394022979985 54854716885326295517234989)
                ·
                  refine ⟨20570518831997360818963121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54854716885326295517234989 20570518831997360818963121)
                  ·
                    refine ⟨15427889123998020614222341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20570518831997360818963121 15427889123998020614222341)
                    ·
                      refine ⟨2892729210749628865166689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15427889123998020614222341 2892729210749628865166689)
                      ·
                        rfl

theorem cell23_5633570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5633570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633570 prefixEnd_5633570 := by exact prefixLift 5633570
  have htrace : WordTrace (prefixWord ++ tailWord_5633570) baseStart_5633570 baseEnd_5633570 := by
    simpa [prefixWord, tailWord_5633570, baseEnd_5633570] using wordTrace_append hprefix tailTrace_5633570
  have hstable : (prefixWord ++ tailWord_5633570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633570).length < 2 ^ (prefixWord ++ tailWord_5633570).sum := by decide
  have hdescent : baseEnd_5633570 < baseStart_5633570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633573 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_5633573 : Nat := 118140960795 + 5633573 * 2 ^ 59
def prefixEnd_5633573 : Nat := 4983230072969 + 3 ^ 40 * 5633573 * 2
def baseEnd_5633573 : Nat := 2892730751191592353429175

theorem tailTrace_5633573 : CollatzResearch.WordTrace tailWord_5633573 prefixEnd_5633573 2892730751191592353429175 := by
  unfold tailWord_5633573
  simp only [CollatzResearch.WordTrace]
  refine ⟨205473287619534633513817373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136982191746356422342544915 205473287619534633513817373)
  ·
    refine ⟨77052482857325487567681515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205473287619534633513817373 77052482857325487567681515)
    ·
      refine ⟨115578724285988231351522273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77052482857325487567681515 115578724285988231351522273)
      ·
        refine ⟨86684043214491173513641705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115578724285988231351522273 86684043214491173513641705)
        ·
          refine ⟨65013032410868380135231279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86684043214491173513641705 65013032410868380135231279)
          ·
            refine ⟨97519548616302570202846919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65013032410868380135231279 97519548616302570202846919)
            ·
              refine ⟨146279322924453855304270379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97519548616302570202846919 146279322924453855304270379)
              ·
                refine ⟨219418984386680782956405569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146279322924453855304270379 219418984386680782956405569)
                ·
                  refine ⟨164564238290010587217304177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219418984386680782956405569 164564238290010587217304177)
                  ·
                    refine ⟨123423178717507940412978133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164564238290010587217304177 123423178717507940412978133)
                    ·
                      refine ⟨2892730751191592353429175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123423178717507940412978133 2892730751191592353429175)
                      ·
                        rfl

theorem cell23_5633573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_5633573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633573 prefixEnd_5633573 := by exact prefixLift 5633573
  have htrace : WordTrace (prefixWord ++ tailWord_5633573) baseStart_5633573 baseEnd_5633573 := by
    simpa [prefixWord, tailWord_5633573, baseEnd_5633573] using wordTrace_append hprefix tailTrace_5633573
  have hstable : (prefixWord ++ tailWord_5633573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633573).length < 2 ^ (prefixWord ++ tailWord_5633573).sum := by decide
  have hdescent : baseEnd_5633573 < baseStart_5633573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633587 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 4]
def baseStart_5633587 : Nat := 118140960795 + 5633587 * 2 ^ 59
def prefixEnd_5633587 : Nat := 4983230072969 + 3 ^ 40 * 5633587 * 2
def baseEnd_5633587 : Nat := 2892737939920755298654111

theorem tailTrace_5633587 : CollatzResearch.WordTrace tailWord_5633587 prefixEnd_5633587 2892737939920755298654111 := by
  unfold tailWord_5633587
  simp only [CollatzResearch.WordTrace]
  refine ⟨205473798241483913904827015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136982532160989275936551343 205473798241483913904827015)
  ·
    refine ⟨308210697362225870857240523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205473798241483913904827015 308210697362225870857240523)
    ·
      refine ⟨462316046043338806285860785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308210697362225870857240523 462316046043338806285860785)
      ·
        refine ⟨346737034532504104714395589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462316046043338806285860785 346737034532504104714395589)
        ·
          refine ⟨65013193974844519633949173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346737034532504104714395589 65013193974844519633949173)
          ·
            refine ⟨6094986935141673715682735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65013193974844519633949173 6094986935141673715682735)
            ·
              refine ⟨9142480402712510573524103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094986935141673715682735 9142480402712510573524103)
              ·
                refine ⟨13713720604068765860286155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142480402712510573524103 13713720604068765860286155)
                ·
                  refine ⟨20570580906103148790429233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713720604068765860286155 20570580906103148790429233)
                  ·
                    refine ⟨15427935679577361592821925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20570580906103148790429233 15427935679577361592821925)
                    ·
                      refine ⟨2892737939920755298654111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15427935679577361592821925 2892737939920755298654111)
                      ·
                        rfl

theorem cell23_5633587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_5633587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633587 prefixEnd_5633587 := by exact prefixLift 5633587
  have htrace : WordTrace (prefixWord ++ tailWord_5633587) baseStart_5633587 baseEnd_5633587 := by
    simpa [prefixWord, tailWord_5633587, baseEnd_5633587] using wordTrace_append hprefix tailTrace_5633587
  have hstable : (prefixWord ++ tailWord_5633587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633587).length < 2 ^ (prefixWord ++ tailWord_5633587).sum := by decide
  have hdescent : baseEnd_5633587 < baseStart_5633587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633620 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_5633620 : Nat := 118140960795 + 5633620 * 2 ^ 59
def prefixEnd_5633620 : Nat := 4983230072969 + 3 ^ 40 * 5633620 * 2
def baseEnd_5633620 : Nat := 2892754884782353669541459

theorem tailTrace_5633620 : CollatzResearch.WordTrace tailWord_5633620 prefixEnd_5633620 2892754884782353669541459 := by
  unfold tailWord_5633620
  simp only [CollatzResearch.WordTrace]
  refine ⟨102737500925182180270389157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136983334566909573693852209 102737500925182180270389157)
  ·
    refine ⟨19263281423471658800697967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102737500925182180270389157 19263281423471658800697967)
    ·
      refine ⟨28894922135207488201046951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19263281423471658800697967 28894922135207488201046951)
      ·
        refine ⟨43342383202811232301570427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28894922135207488201046951 43342383202811232301570427)
        ·
          refine ⟨65013574804216848452355641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43342383202811232301570427 65013574804216848452355641)
          ·
            refine ⟨48760181103162636339266731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65013574804216848452355641 48760181103162636339266731)
            ·
              refine ⟨73140271654743954508900097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48760181103162636339266731 73140271654743954508900097)
              ·
                refine ⟨54855203741057965881675073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73140271654743954508900097 54855203741057965881675073)
                ·
                  refine ⟨41141402805793474411256305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54855203741057965881675073 41141402805793474411256305)
                  ·
                    refine ⟨30856052104345105808442229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41141402805793474411256305 30856052104345105808442229)
                    ·
                      refine ⟨2892754884782353669541459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30856052104345105808442229 2892754884782353669541459)
                      ·
                        rfl

theorem cell23_5633620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_5633620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633620 prefixEnd_5633620 := by exact prefixLift 5633620
  have htrace : WordTrace (prefixWord ++ tailWord_5633620) baseStart_5633620 baseEnd_5633620 := by
    simpa [prefixWord, tailWord_5633620, baseEnd_5633620] using wordTrace_append hprefix tailTrace_5633620
  have hstable : (prefixWord ++ tailWord_5633620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633620).length < 2 ^ (prefixWord ++ tailWord_5633620).sum := by decide
  have hdescent : baseEnd_5633620 < baseStart_5633620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633647 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 1, 4, 2]
def baseStart_5633647 : Nat := 118140960795 + 5633647 * 2 ^ 59
def prefixEnd_5633647 : Nat := 4983230072969 + 3 ^ 40 * 5633647 * 2
def baseEnd_5633647 : Nat := 2892768748760025063903835

theorem tailTrace_5633647 : CollatzResearch.WordTrace tailWord_5633647 prefixEnd_5633647 2892768748760025063903835 := by
  unfold tailWord_5633647
  simp only [CollatzResearch.WordTrace]
  refine ⟨205475986621266544152011195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136983991080844362768007463 205475986621266544152011195)
  ·
    refine ⟨308213979931899816228016793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205475986621266544152011195 308213979931899816228016793)
    ·
      refine ⟨231160484948924862171012595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308213979931899816228016793 231160484948924862171012595)
      ·
        refine ⟨346740727423387293256518893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231160484948924862171012595 346740727423387293256518893)
        ·
          refine ⟨130027772783770234971194585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346740727423387293256518893 130027772783770234971194585)
          ·
            refine ⟨97520829587827676228395939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130027772783770234971194585 97520829587827676228395939)
            ·
              refine ⟨146281244381741514342593909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97520829587827676228395939 146281244381741514342593909)
              ·
                refine ⟨13713866660788266969618179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146281244381741514342593909 13713866660788266969618179)
                ·
                  refine ⟨20570799991182400454427269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713866660788266969618179 20570799991182400454427269)
                  ·
                    refine ⟨3857024998346700085205113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20570799991182400454427269 3857024998346700085205113)
                    ·
                      refine ⟨2892768748760025063903835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857024998346700085205113 2892768748760025063903835)
                      ·
                        rfl

theorem cell23_5633647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4, 2].length) (baseStart_5633647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633647 prefixEnd_5633647 := by exact prefixLift 5633647
  have htrace : WordTrace (prefixWord ++ tailWord_5633647) baseStart_5633647 baseEnd_5633647 := by
    simpa [prefixWord, tailWord_5633647, baseEnd_5633647] using wordTrace_append hprefix tailTrace_5633647
  have hstable : (prefixWord ++ tailWord_5633647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633647).length < 2 ^ (prefixWord ++ tailWord_5633647).sum := by decide
  have hdescent : baseEnd_5633647 < baseStart_5633647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633660 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_5633660 : Nat := 118140960795 + 5633660 * 2 ^ 59
def prefixEnd_5633660 : Nat := 4983230072969 + 3 ^ 40 * 5633660 * 2
def baseEnd_5633660 : Nat := 2892775424008533513041275

theorem tailTrace_5633660 : CollatzResearch.WordTrace tailWord_5633660 prefixEnd_5633660 2892775424008533513041275 := by
  unfold tailWord_5633660
  simp only [CollatzResearch.WordTrace]
  refine ⟨102738230385109723686117217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136984307180146298248156289 102738230385109723686117217)
  ·
    refine ⟨77053672788832292764587913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102738230385109723686117217 77053672788832292764587913)
    ·
      refine ⟨57790254591624219573440935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77053672788832292764587913 57790254591624219573440935)
      ·
        refine ⟨86685381887436329360161403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57790254591624219573440935 86685381887436329360161403)
        ·
          refine ⟨130028072831154494040242105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86685381887436329360161403 130028072831154494040242105)
          ·
            refine ⟨97521054623365870530181579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130028072831154494040242105 97521054623365870530181579)
            ·
              refine ⟨146281581935048805795272369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97521054623365870530181579 146281581935048805795272369)
              ·
                refine ⟨109711186451286604346454277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146281581935048805795272369 109711186451286604346454277)
                ·
                  refine ⟨20570847459616238314960177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109711186451286604346454277 20570847459616238314960177)
                  ·
                    refine ⟨15428135594712178736220133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20570847459616238314960177 15428135594712178736220133)
                    ·
                      refine ⟨2892775424008533513041275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15428135594712178736220133 2892775424008533513041275)
                      ·
                        rfl

theorem cell23_5633660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_5633660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633660 prefixEnd_5633660 := by exact prefixLift 5633660
  have htrace : WordTrace (prefixWord ++ tailWord_5633660) baseStart_5633660 baseEnd_5633660 := by
    simpa [prefixWord, tailWord_5633660, baseEnd_5633660] using wordTrace_append hprefix tailTrace_5633660
  have hstable : (prefixWord ++ tailWord_5633660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633660).length < 2 ^ (prefixWord ++ tailWord_5633660).sum := by decide
  have hdescent : baseEnd_5633660 < baseStart_5633660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633668 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_5633668 : Nat := 118140960795 + 5633668 * 2 ^ 59
def prefixEnd_5633668 : Nat := 4983230072969 + 3 ^ 40 * 5633668 * 2
def baseEnd_5633668 : Nat := 2892779531853769481741239

theorem tailTrace_5633668 : CollatzResearch.WordTrace tailWord_5633668 prefixEnd_5633668 2892779531853769481741239 := by
  unfold tailWord_5633668
  simp only [CollatzResearch.WordTrace]
  refine ⟨102738376277095232369262829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136984501702793643159017105 102738376277095232369262829)
  ·
    refine ⟨38526891103910712138473561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102738376277095232369262829 38526891103910712138473561)
    ·
      refine ⟨28895168327933034103855171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38526891103910712138473561 28895168327933034103855171)
      ·
        refine ⟨43342752491899551155782757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28895168327933034103855171 43342752491899551155782757)
        ·
          refine ⟨8126766092231165841709267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43342752491899551155782757 8126766092231165841709267)
          ·
            refine ⟨12190149138346748762563901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8126766092231165841709267 12190149138346748762563901)
            ·
              refine ⟨4571305926880030785961463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12190149138346748762563901 4571305926880030785961463)
              ·
                refine ⟨6856958890320046178942195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571305926880030785961463 6856958890320046178942195)
                ·
                  refine ⟨10285438335480069268413293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6856958890320046178942195 10285438335480069268413293)
                  ·
                    refine ⟨3857039375805025975654985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10285438335480069268413293 3857039375805025975654985)
                    ·
                      refine ⟨2892779531853769481741239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857039375805025975654985 2892779531853769481741239)
                      ·
                        rfl

theorem cell23_5633668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_5633668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633668 prefixEnd_5633668 := by exact prefixLift 5633668
  have htrace : WordTrace (prefixWord ++ tailWord_5633668) baseStart_5633668 baseEnd_5633668 := by
    simpa [prefixWord, tailWord_5633668, baseEnd_5633668] using wordTrace_append hprefix tailTrace_5633668
  have hstable : (prefixWord ++ tailWord_5633668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633668).length < 2 ^ (prefixWord ++ tailWord_5633668).sum := by decide
  have hdescent : baseEnd_5633668 < baseStart_5633668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633680 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_5633680 : Nat := 118140960795 + 5633680 * 2 ^ 59
def prefixEnd_5633680 : Nat := 4983230072969 + 3 ^ 40 * 5633680 * 2
def baseEnd_5633680 : Nat := 2892785693621623434791183

theorem tailTrace_5633680 : CollatzResearch.WordTrace tailWord_5633680 prefixEnd_5633680 2892785693621623434791183 := by
  unfold tailWord_5633680
  simp only [CollatzResearch.WordTrace]
  refine ⟨102738595115073495393981247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136984793486764660525308329 102738595115073495393981247)
  ·
    refine ⟨154107892672610243090971871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102738595115073495393981247 154107892672610243090971871)
    ·
      refine ⟨231161839008915364636457807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154107892672610243090971871 231161839008915364636457807)
      ·
        refine ⟨346742758513373046954686711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231161839008915364636457807 346742758513373046954686711)
        ·
          refine ⟨520114137770059570432030067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346742758513373046954686711 520114137770059570432030067)
          ·
            refine ⟨780171206655089355648045101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520114137770059570432030067 780171206655089355648045101)
            ·
              refine ⟨292564202495658508368016913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780171206655089355648045101 292564202495658508368016913)
              ·
                refine ⟨219423151871743881276012685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292564202495658508368016913 219423151871743881276012685)
                ·
                  refine ⟨82283681951903955478504757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219423151871743881276012685 82283681951903955478504757)
                  ·
                    refine ⟨7714095182990995826109821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82283681951903955478504757 7714095182990995826109821)
                    ·
                      refine ⟨2892785693621623434791183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714095182990995826109821 2892785693621623434791183)
                      ·
                        rfl

theorem cell23_5633680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_5633680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633680 prefixEnd_5633680 := by exact prefixLift 5633680
  have htrace : WordTrace (prefixWord ++ tailWord_5633680) baseStart_5633680 baseEnd_5633680 := by
    simpa [prefixWord, tailWord_5633680, baseEnd_5633680] using wordTrace_append hprefix tailTrace_5633680
  have hstable : (prefixWord ++ tailWord_5633680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633680).length < 2 ^ (prefixWord ++ tailWord_5633680).sum := by decide
  have hdescent : baseEnd_5633680 < baseStart_5633680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633694 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5633694 : Nat := 118140960795 + 5633694 * 2 ^ 59
def prefixEnd_5633694 : Nat := 4983230072969 + 3 ^ 40 * 5633694 * 2
def baseEnd_5633694 : Nat := 2892792882350786380016119

theorem tailTrace_5633694 : CollatzResearch.WordTrace tailWord_5633694 prefixEnd_5633694 2892792882350786380016119 := by
  unfold tailWord_5633694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25684712606512033897371517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136985133901397514119314757 25684712606512033897371517)
  ·
    refine ⟨9631767227442012711514319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25684712606512033897371517 9631767227442012711514319)
    ·
      refine ⟨14447650841163019067271479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631767227442012711514319 14447650841163019067271479)
      ·
        refine ⟨21671476261744528600907219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447650841163019067271479 21671476261744528600907219)
        ·
          refine ⟨32507214392616792901360829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21671476261744528600907219 32507214392616792901360829)
          ·
            refine ⟨12190205397231297338010311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32507214392616792901360829 12190205397231297338010311)
            ·
              refine ⟨18285308095846946007015467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12190205397231297338010311 18285308095846946007015467)
              ·
                refine ⟨27427962143770419010523201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18285308095846946007015467 27427962143770419010523201)
                ·
                  refine ⟨20570971607827814257892401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27427962143770419010523201 20570971607827814257892401)
                  ·
                    refine ⟨15428228705870860693419301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20570971607827814257892401 15428228705870860693419301)
                    ·
                      refine ⟨2892792882350786380016119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15428228705870860693419301 2892792882350786380016119)
                      ·
                        rfl

theorem cell23_5633694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5633694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633694 prefixEnd_5633694 := by exact prefixLift 5633694
  have htrace : WordTrace (prefixWord ++ tailWord_5633694) baseStart_5633694 baseEnd_5633694 := by
    simpa [prefixWord, tailWord_5633694, baseEnd_5633694] using wordTrace_append hprefix tailTrace_5633694
  have hstable : (prefixWord ++ tailWord_5633694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633694).length < 2 ^ (prefixWord ++ tailWord_5633694).sum := by decide
  have hdescent : baseEnd_5633694 < baseStart_5633694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633697 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5633697 : Nat := 118140960795 + 5633697 * 2 ^ 59
def prefixEnd_5633697 : Nat := 4983230072969 + 3 ^ 40 * 5633697 * 2
def baseEnd_5633697 : Nat := 2892794422792749868278605

theorem tailTrace_5633697 : CollatzResearch.WordTrace tailWord_5633697 prefixEnd_5633697 2892794422792749868278605 := by
  unfold tailWord_5633697
  simp only [CollatzResearch.WordTrace]
  refine ⟨205477810271085402691331345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136985206847390268460887563 205477810271085402691331345)
  ·
    refine ⟨154108357703314052018498509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205477810271085402691331345 154108357703314052018498509)
    ·
      refine ⟨57790634138742769506936941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154108357703314052018498509 57790634138742769506936941)
      ·
        refine ⟨21671487802028538565101353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57790634138742769506936941 21671487802028538565101353)
        ·
          refine ⟨16253615851521403923826015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21671487802028538565101353 16253615851521403923826015)
          ·
            refine ⟨24380423777282105885739023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16253615851521403923826015 24380423777282105885739023)
            ·
              refine ⟨36570635665923158828608535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24380423777282105885739023 36570635665923158828608535)
              ·
                refine ⟨54855953498884738242912803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36570635665923158828608535 54855953498884738242912803)
                ·
                  refine ⟨82283930248327107364369205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54855953498884738242912803 82283930248327107364369205)
                  ·
                    refine ⟨7714118460780666315409613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82283930248327107364369205 7714118460780666315409613)
                    ·
                      refine ⟨2892794422792749868278605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714118460780666315409613 2892794422792749868278605)
                      ·
                        rfl

theorem cell23_5633697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5633697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633697 prefixEnd_5633697 := by exact prefixLift 5633697
  have htrace : WordTrace (prefixWord ++ tailWord_5633697) baseStart_5633697 baseEnd_5633697 := by
    simpa [prefixWord, tailWord_5633697, baseEnd_5633697] using wordTrace_append hprefix tailTrace_5633697
  have hstable : (prefixWord ++ tailWord_5633697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633697).length < 2 ^ (prefixWord ++ tailWord_5633697).sum := by decide
  have hdescent : baseEnd_5633697 < baseStart_5633697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633698 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5633698 : Nat := 118140960795 + 5633698 * 2 ^ 59
def prefixEnd_5633698 : Nat := 4983230072969 + 3 ^ 40 * 5633698 * 2
def baseEnd_5633698 : Nat := 2892794936273404364366101

theorem tailTrace_5633698 : CollatzResearch.WordTrace tailWord_5633698 prefixEnd_5633698 2892794936273404364366101 := by
  unfold tailWord_5633698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51369461686020444965529437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136985231162721186574745165 51369461686020444965529437)
  ·
    refine ⟨19263548132257666862073539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51369461686020444965529437 19263548132257666862073539)
    ·
      refine ⟨28895322198386500293110309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19263548132257666862073539 28895322198386500293110309)
      ·
        refine ⟨5417872912197468804958183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28895322198386500293110309 5417872912197468804958183)
        ·
          refine ⟨8126809368296203207437275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417872912197468804958183 8126809368296203207437275)
          ·
            refine ⟨12190214052444304811155913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8126809368296203207437275 12190214052444304811155913)
            ·
              refine ⟨9142660539333228608366935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12190214052444304811155913 9142660539333228608366935)
              ·
                refine ⟨13713990808999842912550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142660539333228608366935 13713990808999842912550403)
                ·
                  refine ⟨20570986213499764368825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13713990808999842912550403 20570986213499764368825605)
                  ·
                    refine ⟨3857059915031205819154801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20570986213499764368825605 3857059915031205819154801)
                    ·
                      refine ⟨2892794936273404364366101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857059915031205819154801 2892794936273404364366101)
                      ·
                        rfl

theorem cell23_5633698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5633698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633698 prefixEnd_5633698 := by exact prefixLift 5633698
  have htrace : WordTrace (prefixWord ++ tailWord_5633698) baseStart_5633698 baseEnd_5633698 := by
    simpa [prefixWord, tailWord_5633698, baseEnd_5633698] using wordTrace_append hprefix tailTrace_5633698
  have hstable : (prefixWord ++ tailWord_5633698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633698).length < 2 ^ (prefixWord ++ tailWord_5633698).sum := by decide
  have hdescent : baseEnd_5633698 < baseStart_5633698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633754 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_5633754 : Nat := 118140960795 + 5633754 * 2 ^ 59
def prefixEnd_5633754 : Nat := 4983230072969 + 3 ^ 40 * 5633754 * 2
def baseEnd_5633754 : Nat := 2892823691190056145265843

theorem tailTrace_5633754 : CollatzResearch.WordTrace tailWord_5633754 prefixEnd_5633754 2892823691190056145265843 := by
  unfold tailWord_5633754
  simp only [CollatzResearch.WordTrace]
  refine ⟨51369972307969725356539079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136986592821252600950770877 51369972307969725356539079)
  ·
    refine ⟨77054958461954588034808619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51369972307969725356539079 77054958461954588034808619)
    ·
      refine ⟨115582437692931882052212929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77054958461954588034808619 115582437692931882052212929)
      ·
        refine ⟨86686828269698911539159697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115582437692931882052212929 86686828269698911539159697)
        ·
          refine ⟨65015121202274183654369773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86686828269698911539159697 65015121202274183654369773)
          ·
            refine ⟨24380670450852818870388665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65015121202274183654369773 24380670450852818870388665)
            ·
              refine ⟨18285502838139614152791499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24380670450852818870388665 18285502838139614152791499)
              ·
                refine ⟨27428254257209421229187249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18285502838139614152791499 27428254257209421229187249)
                ·
                  refine ⟨20571190692907065921890437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27428254257209421229187249 20571190692907065921890437)
                  ·
                    refine ⟨3857098254920074860354457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20571190692907065921890437 3857098254920074860354457)
                    ·
                      refine ⟨2892823691190056145265843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857098254920074860354457 2892823691190056145265843)
                      ·
                        rfl

theorem cell23_5633754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_5633754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633754 prefixEnd_5633754 := by exact prefixLift 5633754
  have htrace : WordTrace (prefixWord ++ tailWord_5633754) baseStart_5633754 baseEnd_5633754 := by
    simpa [prefixWord, tailWord_5633754, baseEnd_5633754] using wordTrace_append hprefix tailTrace_5633754
  have hstable : (prefixWord ++ tailWord_5633754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633754).length < 2 ^ (prefixWord ++ tailWord_5633754).sum := by decide
  have hdescent : baseEnd_5633754 < baseStart_5633754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633774 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_5633774 : Nat := 118140960795 + 5633774 * 2 ^ 59
def prefixEnd_5633774 : Nat := 4983230072969 + 3 ^ 40 * 5633774 * 2
def baseEnd_5633774 : Nat := 2892833960803146067015751

theorem tailTrace_5633774 : CollatzResearch.WordTrace tailWord_5633774 prefixEnd_5633774 2892833960803146067015751 := by
  unfold tailWord_5633774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685077336475805605235547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136987079127870963227922917 25685077336475805605235547)
  ·
    refine ⟨38527616004713708407853321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25685077336475805605235547 38527616004713708407853321)
    ·
      refine ⟨28895712003535281305889991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38527616004713708407853321 28895712003535281305889991)
      ·
        refine ⟨43343568005302921958834987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28895712003535281305889991 43343568005302921958834987)
        ·
          refine ⟨65015352007954382938252481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43343568005302921958834987 65015352007954382938252481)
          ·
            refine ⟨48761514005965787203689361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65015352007954382938252481 48761514005965787203689361)
            ·
              refine ⟨36571135504474340402767021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48761514005965787203689361 36571135504474340402767021)
              ·
                refine ⟨13714175814177877651037633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36571135504474340402767021 13714175814177877651037633)
                ·
                  refine ⟨10285631860633408238278225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13714175814177877651037633 10285631860633408238278225)
                  ·
                    refine ⟨7714223895475056178708669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10285631860633408238278225 7714223895475056178708669)
                    ·
                      refine ⟨2892833960803146067015751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714223895475056178708669 2892833960803146067015751)
                      ·
                        rfl

theorem cell23_5633774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_5633774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633774 prefixEnd_5633774 := by exact prefixLift 5633774
  have htrace : WordTrace (prefixWord ++ tailWord_5633774) baseStart_5633774 baseEnd_5633774 := by
    simpa [prefixWord, tailWord_5633774, baseEnd_5633774] using wordTrace_append hprefix tailTrace_5633774
  have hstable : (prefixWord ++ tailWord_5633774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633774).length < 2 ^ (prefixWord ++ tailWord_5633774).sum := by decide
  have hdescent : baseEnd_5633774 < baseStart_5633774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633794 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_5633794 : Nat := 118140960795 + 5633794 * 2 ^ 59
def prefixEnd_5633794 : Nat := 4983230072969 + 3 ^ 40 * 5633794 * 2
def baseEnd_5633794 : Nat := 321427136712915109862851

theorem tailTrace_5633794 : CollatzResearch.WordTrace tailWord_5633794 prefixEnd_5633794 321427136712915109862851 := by
  unfold tailWord_5633794
  simp only [CollatzResearch.WordTrace]
  refine ⟨51370337037933497064403109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136987565434489325505074957 51370337037933497064403109)
  ·
    refine ⟨9631938194612530699575583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51370337037933497064403109 9631938194612530699575583)
    ·
      refine ⟨14447907291918796049363375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631938194612530699575583 14447907291918796049363375)
      ·
        refine ⟨21671860937878194074045063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447907291918796049363375 21671860937878194074045063)
        ·
          refine ⟨32507791406817291111067595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21671860937878194074045063 32507791406817291111067595)
          ·
            refine ⟨48761687110225936666601393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32507791406817291111067595 48761687110225936666601393)
            ·
              refine ⟨36571265332669452499951045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48761687110225936666601393 36571265332669452499951045)
              ·
                refine ⟨6857112249875522343740821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36571265332669452499951045 6857112249875522343740821)
                ·
                  refine ⟨321427136712915109862851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6857112249875522343740821 321427136712915109862851)
                  ·
                    rfl

theorem cell23_5633794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_5633794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633794 prefixEnd_5633794 := by exact prefixLift 5633794
  have htrace : WordTrace (prefixWord ++ tailWord_5633794) baseStart_5633794 baseEnd_5633794 := by
    simpa [prefixWord, tailWord_5633794, baseEnd_5633794] using wordTrace_append hprefix tailTrace_5633794
  have hstable : (prefixWord ++ tailWord_5633794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633794).length < 2 ^ (prefixWord ++ tailWord_5633794).sum := by decide
  have hdescent : baseEnd_5633794 < baseStart_5633794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633841 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 1, 5]
def baseStart_5633841 : Nat := 118140960795 + 5633841 * 2 ^ 59
def prefixEnd_5633841 : Nat := 4983230072969 + 3 ^ 40 * 5633841 * 2
def baseEnd_5633841 : Nat := 964289454668999101625981

theorem tailTrace_5633841 : CollatzResearch.WordTrace tailWord_5633841 prefixEnd_5633841 964289454668999101625981 := by
  unfold tailWord_5633841
  simp only [CollatzResearch.WordTrace]
  refine ⟨205483062382563715284573377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136988708255042476856382251 205483062382563715284573377)
  ·
    refine ⟨154112296786922786463430033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205483062382563715284573377 154112296786922786463430033)
    ·
      refine ⟨115584222590192089847572525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154112296786922786463430033 115584222590192089847572525)
      ·
        refine ⟨43344083471322033692839697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115584222590192089847572525 43344083471322033692839697)
        ·
          refine ⟨32508062603491525269629773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43344083471322033692839697 32508062603491525269629773)
          ·
            refine ⟨12190523476309321976111165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32508062603491525269629773 12190523476309321976111165)
            ·
              refine ⟨4571446303615995741041687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12190523476309321976111165 4571446303615995741041687)
              ·
                refine ⟨6857169455423993611562531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571446303615995741041687 6857169455423993611562531)
                ·
                  refine ⟨10285754183135990417343797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6857169455423993611562531 10285754183135990417343797)
                  ·
                    refine ⟨964289454668999101625981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10285754183135990417343797 964289454668999101625981)
                    ·
                      rfl

theorem cell23_5633841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_5633841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633841 prefixEnd_5633841 := by exact prefixLift 5633841
  have htrace : WordTrace (prefixWord ++ tailWord_5633841) baseStart_5633841 baseEnd_5633841 := by
    simpa [prefixWord, tailWord_5633841, baseEnd_5633841] using wordTrace_append hprefix tailTrace_5633841
  have hstable : (prefixWord ++ tailWord_5633841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633841).length < 2 ^ (prefixWord ++ tailWord_5633841).sum := by decide
  have hdescent : baseEnd_5633841 < baseStart_5633841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633847 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_5633847 : Nat := 118140960795 + 5633847 * 2 ^ 59
def prefixEnd_5633847 : Nat := 4983230072969 + 3 ^ 40 * 5633847 * 2
def baseEnd_5633847 : Nat := 2892871444890924281402915

theorem tailTrace_5633847 : CollatzResearch.WordTrace tailWord_5633847 prefixEnd_5633847 2892871444890924281402915 := by
  unfold tailWord_5633847
  simp only [CollatzResearch.WordTrace]
  refine ⟨205483281220541978309291795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136988854147027985539527863 205483281220541978309291795)
  ·
    refine ⟨308224921830812967463937693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205483281220541978309291795 308224921830812967463937693)
    ·
      refine ⟨115584345686554862798976635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308224921830812967463937693 115584345686554862798976635)
      ·
        refine ⟨173376518529832294198464953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115584345686554862798976635 173376518529832294198464953)
        ·
          refine ⟨130032388897374220648848715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173376518529832294198464953 130032388897374220648848715)
          ·
            refine ⟨195048583346061330973273073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130032388897374220648848715 195048583346061330973273073)
            ·
              refine ⟨146286437509545998229954805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195048583346061330973273073 146286437509545998229954805)
              ·
                refine ⟨13714353516519937334058263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146286437509545998229954805 13714353516519937334058263)
                ·
                  refine ⟨20571530274779906001087395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13714353516519937334058263 20571530274779906001087395)
                  ·
                    refine ⟨30857295412169859001631093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20571530274779906001087395 30857295412169859001631093)
                    ·
                      refine ⟨2892871444890924281402915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30857295412169859001631093 2892871444890924281402915)
                      ·
                        rfl

theorem cell23_5633847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_5633847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633847 prefixEnd_5633847 := by exact prefixLift 5633847
  have htrace : WordTrace (prefixWord ++ tailWord_5633847) baseStart_5633847 baseEnd_5633847 := by
    simpa [prefixWord, tailWord_5633847, baseEnd_5633847] using wordTrace_append hprefix tailTrace_5633847
  have hstable : (prefixWord ++ tailWord_5633847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633847).length < 2 ^ (prefixWord ++ tailWord_5633847).sum := by decide
  have hdescent : baseEnd_5633847 < baseStart_5633847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633861 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_5633861 : Nat := 118140960795 + 5633861 * 2 ^ 59
def prefixEnd_5633861 : Nat := 4983230072969 + 3 ^ 40 * 5633861 * 2
def baseEnd_5633861 : Nat := 2892878633620087226627851

theorem tailTrace_5633861 : CollatzResearch.WordTrace tailWord_5633861 prefixEnd_5633861 2892878633620087226627851 := by
  unfold tailWord_5633861
  simp only [CollatzResearch.WordTrace]
  refine ⟨205483791842491258700301437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136989194561660839133534291 205483791842491258700301437)
  ·
    refine ⟨77056421940934222012613039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205483791842491258700301437 77056421940934222012613039)
    ·
      refine ⟨115584632911401333018919559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77056421940934222012613039 115584632911401333018919559)
      ·
        refine ⟨173376949367101999528379339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115584632911401333018919559 173376949367101999528379339)
        ·
          refine ⟨260065424050652999292569009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173376949367101999528379339 260065424050652999292569009)
          ·
            refine ⟨195049068037989749469426757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260065424050652999292569009 195049068037989749469426757)
            ·
              refine ⟨36571700257123078025517517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195049068037989749469426757 36571700257123078025517517)
              ·
                refine ⟨13714387596421154259569069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36571700257123078025517517 13714387596421154259569069)
                ·
                  refine ⟨5142895348657932847338401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13714387596421154259569069 5142895348657932847338401)
                  ·
                    refine ⟨3857171511493449635503801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5142895348657932847338401 3857171511493449635503801)
                    ·
                      refine ⟨2892878633620087226627851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857171511493449635503801 2892878633620087226627851)
                      ·
                        rfl

theorem cell23_5633861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_5633861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633861 prefixEnd_5633861 := by exact prefixLift 5633861
  have htrace : WordTrace (prefixWord ++ tailWord_5633861) baseStart_5633861 baseEnd_5633861 := by
    simpa [prefixWord, tailWord_5633861, baseEnd_5633861] using wordTrace_append hprefix tailTrace_5633861
  have hstable : (prefixWord ++ tailWord_5633861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633861).length < 2 ^ (prefixWord ++ tailWord_5633861).sum := by decide
  have hdescent : baseEnd_5633861 < baseStart_5633861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633864 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_5633864 : Nat := 118140960795 + 5633864 * 2 ^ 59
def prefixEnd_5633864 : Nat := 4983230072969 + 3 ^ 40 * 5633864 * 2
def baseEnd_5633864 : Nat := 2892880174062050714890337

theorem tailTrace_5633864 : CollatzResearch.WordTrace tailWord_5633864 prefixEnd_5633864 2892880174062050714890337 := by
  unfold tailWord_5633864
  simp only [CollatzResearch.WordTrace]
  refine ⟨102741950630740195106330323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136989267507653593475107097 102741950630740195106330323)
  ·
    refine ⟨154112925946110292659495485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102741950630740195106330323 154112925946110292659495485)
    ·
      refine ⟨57792347229791359747310807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154112925946110292659495485 57792347229791359747310807)
      ·
        refine ⟨86688520844687039620966211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57792347229791359747310807 86688520844687039620966211)
        ·
          refine ⟨130032781267030559431449317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86688520844687039620966211 130032781267030559431449317)
          ·
            refine ⟨24381146487568229893396747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130032781267030559431449317 24381146487568229893396747)
            ·
              refine ⟨36571719731352344840095121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24381146487568229893396747 36571719731352344840095121)
              ·
                refine ⟨27428789798514258630071341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36571719731352344840095121 27428789798514258630071341)
                ·
                  refine ⟨10285796174442846986276753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27428789798514258630071341 10285796174442846986276753)
                  ·
                    refine ⟨7714347130832135239707565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10285796174442846986276753 7714347130832135239707565)
                    ·
                      refine ⟨2892880174062050714890337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714347130832135239707565 2892880174062050714890337)
                      ·
                        rfl

theorem cell23_5633864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_5633864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633864 prefixEnd_5633864 := by exact prefixLift 5633864
  have htrace : WordTrace (prefixWord ++ tailWord_5633864) baseStart_5633864 baseEnd_5633864 := by
    simpa [prefixWord, tailWord_5633864, baseEnd_5633864] using wordTrace_append hprefix tailTrace_5633864
  have hstable : (prefixWord ++ tailWord_5633864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633864).length < 2 ^ (prefixWord ++ tailWord_5633864).sum := by decide
  have hdescent : baseEnd_5633864 < baseStart_5633864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633874 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5633874 : Nat := 118140960795 + 5633874 * 2 ^ 59
def prefixEnd_5633874 : Nat := 4983230072969 + 3 ^ 40 * 5633874 * 2
def baseEnd_5633874 : Nat := 2892885308868595675765291

theorem tailTrace_5633874 : CollatzResearch.WordTrace tailWord_5633874 prefixEnd_5633874 2892885308868595675765291 := by
  unfold tailWord_5633874
  simp only [CollatzResearch.WordTrace]
  refine ⟨51371066497861040480131169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136989510660962774613683117 51371066497861040480131169)
  ·
    refine ⟨38528299873395780360098377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51371066497861040480131169 38528299873395780360098377)
    ·
      refine ⟨28896224905046835270073783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38528299873395780360098377 28896224905046835270073783)
      ·
        refine ⟨43344337357570252905110675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28896224905046835270073783 43344337357570252905110675)
        ·
          refine ⟨65016506036355379357666013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43344337357570252905110675 65016506036355379357666013)
          ·
            refine ⟨24381189763633267259124755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65016506036355379357666013 24381189763633267259124755)
            ·
              refine ⟨36571784645449900888687133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24381189763633267259124755 36571784645449900888687133)
              ·
                refine ⟨13714419242043712833257675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36571784645449900888687133 13714419242043712833257675)
                ·
                  refine ⟨20571628863065569249886513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13714419242043712833257675 20571628863065569249886513)
                  ·
                    refine ⟨15428721647299176937414885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20571628863065569249886513 15428721647299176937414885)
                    ·
                      refine ⟨2892885308868595675765291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15428721647299176937414885 2892885308868595675765291)
                      ·
                        rfl

theorem cell23_5633874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5633874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633874 prefixEnd_5633874 := by exact prefixLift 5633874
  have htrace : WordTrace (prefixWord ++ tailWord_5633874) baseStart_5633874 baseEnd_5633874 := by
    simpa [prefixWord, tailWord_5633874, baseEnd_5633874] using wordTrace_append hprefix tailTrace_5633874
  have hstable : (prefixWord ++ tailWord_5633874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633874).length < 2 ^ (prefixWord ++ tailWord_5633874).sum := by decide
  have hdescent : baseEnd_5633874 < baseStart_5633874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633895 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_5633895 : Nat := 118140960795 + 5633895 * 2 ^ 59
def prefixEnd_5633895 : Nat := 4983230072969 + 3 ^ 40 * 5633895 * 2
def baseEnd_5633895 : Nat := 2892896091962340093602695

theorem tailTrace_5633895 : CollatzResearch.WordTrace tailWord_5633895 prefixEnd_5633895 2892896091962340093602695 := by
  unfold tailWord_5633895
  simp only [CollatzResearch.WordTrace]
  refine ⟨205485031924368082507039139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136990021282912055004692759 205485031924368082507039139)
  ·
    refine ⟨308227547886552123760558709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205485031924368082507039139 308227547886552123760558709)
    ·
      refine ⟨28896332614364261602552379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308227547886552123760558709 28896332614364261602552379)
      ·
        refine ⟨43344498921546392403828569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28896332614364261602552379 43344498921546392403828569)
        ·
          refine ⟨32508374191159794302871427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43344498921546392403828569 32508374191159794302871427)
          ·
            refine ⟨48762561286739691454307141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32508374191159794302871427 48762561286739691454307141)
            ·
              refine ⟨9142980241263692147682589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48762561286739691454307141 9142980241263692147682589)
              ·
                refine ⟨3428617590473884555380971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9142980241263692147682589 3428617590473884555380971)
                ·
                  refine ⟨5142926385710826833071457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428617590473884555380971 5142926385710826833071457)
                  ·
                    refine ⟨3857194789283120124803593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5142926385710826833071457 3857194789283120124803593)
                    ·
                      refine ⟨2892896091962340093602695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857194789283120124803593 2892896091962340093602695)
                      ·
                        rfl

theorem cell23_5633895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_5633895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633895 prefixEnd_5633895 := by exact prefixLift 5633895
  have htrace : WordTrace (prefixWord ++ tailWord_5633895) baseStart_5633895 baseEnd_5633895 := by
    simpa [prefixWord, tailWord_5633895, baseEnd_5633895] using wordTrace_append hprefix tailTrace_5633895
  have hstable : (prefixWord ++ tailWord_5633895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633895).length < 2 ^ (prefixWord ++ tailWord_5633895).sum := by decide
  have hdescent : baseEnd_5633895 < baseStart_5633895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633928 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5633928 : Nat := 118140960795 + 5633928 * 2 ^ 59
def prefixEnd_5633928 : Nat := 4983230072969 + 3 ^ 40 * 5633928 * 2
def baseEnd_5633928 : Nat := 2892913036823938464490043

theorem tailTrace_5633928 : CollatzResearch.WordTrace tailWord_5633928 prefixEnd_5633928 2892913036823938464490043 := by
  unfold tailWord_5633928
  simp only [CollatzResearch.WordTrace]
  refine ⟨102743117766624264571495219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136990823688832352761993625 102743117766624264571495219)
  ·
    refine ⟨154114676649936396857242829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102743117766624264571495219 154114676649936396857242829)
    ·
      refine ⟨57793003743726148821466061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154114676649936396857242829 57793003743726148821466061)
      ·
        refine ⟨21672376403897305808049773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57793003743726148821466061 21672376403897305808049773)
        ·
          refine ⟨8127141151461489678018665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21672376403897305808049773 8127141151461489678018665)
          ·
            refine ⟨6095355863596117258513999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8127141151461489678018665 6095355863596117258513999)
            ·
              refine ⟨9143033795394175887770999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095355863596117258513999 9143033795394175887770999)
              ·
                refine ⟨13714550693091263831656499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9143033795394175887770999 13714550693091263831656499)
                ·
                  refine ⟨20571826039636895747484749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13714550693091263831656499 20571826039636895747484749)
                  ·
                    refine ⟨7714434764863835905306781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20571826039636895747484749 7714434764863835905306781)
                    ·
                      refine ⟨2892913036823938464490043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714434764863835905306781 2892913036823938464490043)
                      ·
                        rfl

theorem cell23_5633928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5633928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633928 prefixEnd_5633928 := by exact prefixLift 5633928
  have htrace : WordTrace (prefixWord ++ tailWord_5633928) baseStart_5633928 baseEnd_5633928 := by
    simpa [prefixWord, tailWord_5633928, baseEnd_5633928] using wordTrace_append hprefix tailTrace_5633928
  have hstable : (prefixWord ++ tailWord_5633928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633928).length < 2 ^ (prefixWord ++ tailWord_5633928).sum := by decide
  have hdescent : baseEnd_5633928 < baseStart_5633928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633957 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 9]
def baseStart_5633957 : Nat := 118140960795 + 5633957 * 2 ^ 59
def prefixEnd_5633957 : Nat := 4983230072969 + 3 ^ 40 * 5633957 * 2
def baseEnd_5633957 : Nat := 321436436418102094558601

theorem tailTrace_5633957 : CollatzResearch.WordTrace tailWord_5633957 prefixEnd_5633957 321436436418102094558601 := by
  unfold tailWord_5633957
  simp only [CollatzResearch.WordTrace]
  refine ⟨205487293250143467095796125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136991528833428978063864083 205487293250143467095796125)
  ·
    refine ⟨77057734968803800160923547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205487293250143467095796125 77057734968803800160923547)
    ·
      refine ⟨115586602453205700241385321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77057734968803800160923547 115586602453205700241385321)
      ·
        refine ⟨86689951839904275181038991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115586602453205700241385321 86689951839904275181038991)
        ·
          refine ⟨130034927759856412771558487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86689951839904275181038991 130034927759856412771558487)
          ·
            refine ⟨195052391639784619157337731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130034927759856412771558487 195052391639784619157337731)
            ·
              refine ⟨292578587459676928736006597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195052391639784619157337731 292578587459676928736006597)
              ·
                refine ⟨54858485148689424138001237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292578587459676928736006597 54858485148689424138001237)
                ·
                  refine ⟨321436436418102094558601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54858485148689424138001237 321436436418102094558601)
                  ·
                    rfl

theorem cell23_5633957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_5633957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633957 prefixEnd_5633957 := by exact prefixLift 5633957
  have htrace : WordTrace (prefixWord ++ tailWord_5633957) baseStart_5633957 baseEnd_5633957 := by
    simpa [prefixWord, tailWord_5633957, baseEnd_5633957] using wordTrace_append hprefix tailTrace_5633957
  have hstable : (prefixWord ++ tailWord_5633957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633957).length < 2 ^ (prefixWord ++ tailWord_5633957).sum := by decide
  have hdescent : baseEnd_5633957 < baseStart_5633957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633967 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_5633967 : Nat := 118140960795 + 5633967 * 2 ^ 59
def prefixEnd_5633967 : Nat := 4983230072969 + 3 ^ 40 * 5633967 * 2
def baseEnd_5633967 : Nat := 2892933062569463811902363

theorem tailTrace_5633967 : CollatzResearch.WordTrace tailWord_5633967 prefixEnd_5633967 2892933062569463811902363 := by
  unfold tailWord_5633967
  simp only [CollatzResearch.WordTrace]
  refine ⟨205487657980107238803660155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136991771986738159202440103 205487657980107238803660155)
  ·
    refine ⟨308231486970160858205490233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205487657980107238803660155 308231486970160858205490233)
    ·
      refine ⟨231173615227620643654117675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308231486970160858205490233 231173615227620643654117675)
      ·
        refine ⟨346760422841430965481176513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231173615227620643654117675 346760422841430965481176513)
        ·
          refine ⟨260070317131073224110882385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346760422841430965481176513 260070317131073224110882385)
          ·
            refine ⟨195052737848304918083161789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260070317131073224110882385 195052737848304918083161789)
            ·
              refine ⟨73144776693114344281185671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195052737848304918083161789 73144776693114344281185671)
              ·
                refine ⟨109717165039671516421778507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73144776693114344281185671 109717165039671516421778507)
                ·
                  refine ⟨164575747559507274632667761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109717165039671516421778507 164575747559507274632667761)
                  ·
                    refine ⟨123431810669630455974500821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164575747559507274632667761 123431810669630455974500821)
                    ·
                      refine ⟨2892933062569463811902363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123431810669630455974500821 2892933062569463811902363)
                      ·
                        rfl

theorem cell23_5633967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_5633967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633967 prefixEnd_5633967 := by exact prefixLift 5633967
  have htrace : WordTrace (prefixWord ++ tailWord_5633967) baseStart_5633967 baseEnd_5633967 := by
    simpa [prefixWord, tailWord_5633967, baseEnd_5633967] using wordTrace_append hprefix tailTrace_5633967
  have hstable : (prefixWord ++ tailWord_5633967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633967).length < 2 ^ (prefixWord ++ tailWord_5633967).sum := by decide
  have hdescent : baseEnd_5633967 < baseStart_5633967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5633984 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_5633984 : Nat := 118140960795 + 5633984 * 2 ^ 59
def prefixEnd_5633984 : Nat := 4983230072969 + 3 ^ 40 * 5633984 * 2
def baseEnd_5633984 : Nat := 2892941791740590245389785

theorem tailTrace_5633984 : CollatzResearch.WordTrace tailWord_5633984 prefixEnd_5633984 2892941791740590245389785 := by
  unfold tailWord_5633984
  simp only [CollatzResearch.WordTrace]
  refine ⟨102744139010522825353514503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136992185347363767138019337 102744139010522825353514503)
  ·
    refine ⟨154116208515784238030271755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102744139010522825353514503 154116208515784238030271755)
    ·
      refine ⟨231174312773676357045407633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154116208515784238030271755 231174312773676357045407633)
      ·
        refine ⟨173380734580257267784055725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231174312773676357045407633 173380734580257267784055725)
        ·
          refine ⟨65017775467596475419020897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173380734580257267784055725 65017775467596475419020897)
          ·
            refine ⟨48763331600697356564265673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65017775467596475419020897 48763331600697356564265673)
            ·
              refine ⟨36572498700523017423199255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48763331600697356564265673 36572498700523017423199255)
              ·
                refine ⟨54858748050784526134798883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36572498700523017423199255 54858748050784526134798883)
                ·
                  refine ⟨82288122076176789202198325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54858748050784526134798883 82288122076176789202198325)
                  ·
                    refine ⟨7714511444641573987706093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82288122076176789202198325 7714511444641573987706093)
                    ·
                      refine ⟨2892941791740590245389785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714511444641573987706093 2892941791740590245389785)
                      ·
                        rfl

theorem cell23_5633984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_5633984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5633984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5633984 prefixEnd_5633984 := by exact prefixLift 5633984
  have htrace : WordTrace (prefixWord ++ tailWord_5633984) baseStart_5633984 baseEnd_5633984 := by
    simpa [prefixWord, tailWord_5633984, baseEnd_5633984] using wordTrace_append hprefix tailTrace_5633984
  have hstable : (prefixWord ++ tailWord_5633984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5633984).length < 2 ^ (prefixWord ++ tailWord_5633984).sum := by decide
  have hdescent : baseEnd_5633984 < baseStart_5633984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5633984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634024 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5634024 : Nat := 118140960795 + 5634024 * 2 ^ 59
def prefixEnd_5634024 : Nat := 4983230072969 + 3 ^ 40 * 5634024 * 2
def baseEnd_5634024 : Nat := 2892962330966770088889601

theorem tailTrace_5634024 : CollatzResearch.WordTrace tailWord_5634024 prefixEnd_5634024 2892962330966770088889601 := by
  unfold tailWord_5634024
  simp only [CollatzResearch.WordTrace]
  refine ⟨102744868470450368769242563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136993157960600491692323417 102744868470450368769242563)
  ·
    refine ⟨154117302705675553153863845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102744868470450368769242563 154117302705675553153863845)
    ·
      refine ⟨28896994257314166216349471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154117302705675553153863845 28896994257314166216349471)
      ·
        refine ⟨43345491385971249324524207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28896994257314166216349471 43345491385971249324524207)
        ·
          refine ⟨65018237078956873986786311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43345491385971249324524207 65018237078956873986786311)
          ·
            refine ⟨97527355618435310980179467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65018237078956873986786311 97527355618435310980179467)
            ·
              refine ⟨146291033427652966470269201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97527355618435310980179467 146291033427652966470269201)
              ·
                refine ⟨109718275070739724852701901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146291033427652966470269201 109718275070739724852701901)
                ·
                  refine ⟨41144353151527396819763213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109718275070739724852701901 41144353151527396819763213)
                  ·
                    refine ⟨15429132431822773807411205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41144353151527396819763213 15429132431822773807411205)
                    ·
                      refine ⟨2892962330966770088889601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15429132431822773807411205 2892962330966770088889601)
                      ·
                        rfl

theorem cell23_5634024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5634024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634024 prefixEnd_5634024 := by exact prefixLift 5634024
  have htrace : WordTrace (prefixWord ++ tailWord_5634024) baseStart_5634024 baseEnd_5634024 := by
    simpa [prefixWord, tailWord_5634024, baseEnd_5634024] using wordTrace_append hprefix tailTrace_5634024
  have hstable : (prefixWord ++ tailWord_5634024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634024).length < 2 ^ (prefixWord ++ tailWord_5634024).sum := by decide
  have hdescent : baseEnd_5634024 < baseStart_5634024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634041 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 6, 2]
def baseStart_5634041 : Nat := 118140960795 + 5634041 * 2 ^ 59
def prefixEnd_5634041 : Nat := 4983230072969 + 3 ^ 40 * 5634041 * 2
def baseEnd_5634041 : Nat := 2892971060137896522377023

theorem tailTrace_5634041 : CollatzResearch.WordTrace tailWord_5634041 prefixEnd_5634041 2892971060137896522377023 := by
  unfold tailWord_5634041
  simp only [CollatzResearch.WordTrace]
  refine ⟨205490356981839149441853977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136993571321226099627902651 205490356981839149441853977)
  ·
    refine ⟨154117767736379362081390483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205490356981839149441853977 154117767736379362081390483)
    ·
      refine ⟨231176651604569043122085725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154117767736379362081390483 231176651604569043122085725)
      ·
        refine ⟨86691244351713391170782147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231176651604569043122085725 86691244351713391170782147)
        ·
          refine ⟨130036866527570086756173221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86691244351713391170782147 130036866527570086756173221)
          ·
            refine ⟨24381912473919391266782479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130036866527570086756173221 24381912473919391266782479)
            ·
              refine ⟨36572868710879086900173719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24381912473919391266782479 36572868710879086900173719)
              ·
                refine ⟨54859303066318630350260579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36572868710879086900173719 54859303066318630350260579)
                ·
                  refine ⟨82288954599477945525390869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54859303066318630350260579 82288954599477945525390869)
                  ·
                    refine ⟨3857294746850528696502697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82288954599477945525390869 3857294746850528696502697)
                    ·
                      refine ⟨2892971060137896522377023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857294746850528696502697 2892971060137896522377023)
                      ·
                        rfl

theorem cell23_5634041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_5634041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634041 prefixEnd_5634041 := by exact prefixLift 5634041
  have htrace : WordTrace (prefixWord ++ tailWord_5634041) baseStart_5634041 baseEnd_5634041 := by
    simpa [prefixWord, tailWord_5634041, baseEnd_5634041] using wordTrace_append hprefix tailTrace_5634041
  have hstable : (prefixWord ++ tailWord_5634041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634041).length < 2 ^ (prefixWord ++ tailWord_5634041).sum := by decide
  have hdescent : baseEnd_5634041 < baseStart_5634041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634081 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 8]
def baseStart_5634081 : Nat := 118140960795 + 5634081 * 2 ^ 59
def prefixEnd_5634081 : Nat := 4983230072969 + 3 ^ 40 * 5634081 * 2
def baseEnd_5634081 : Nat := 321443511040452929541871

theorem tailTrace_5634081 : CollatzResearch.WordTrace tailWord_5634081 prefixEnd_5634081 321443511040452929541871 := by
  unfold tailWord_5634081
  simp only [CollatzResearch.WordTrace]
  refine ⟨205491815901694236273310097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136994543934462824182206731 205491815901694236273310097)
  ·
    refine ⟨154118861926270677204982573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205491815901694236273310097 154118861926270677204982573)
    ·
      refine ⟨57794573222351503951868465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154118861926270677204982573 57794573222351503951868465)
      ·
        refine ⟨43345929916763627963901349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57794573222351503951868465 43345929916763627963901349)
        ·
          refine ⟨8127361859393180243231503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43345929916763627963901349 8127361859393180243231503)
          ·
            refine ⟨12191042789089770364847255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127361859393180243231503 12191042789089770364847255)
            ·
              refine ⟨18286564183634655547270883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12191042789089770364847255 18286564183634655547270883)
              ·
                refine ⟨27429846275451983320906325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18286564183634655547270883 27429846275451983320906325)
                ·
                  refine ⟨321443511040452929541871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27429846275451983320906325 321443511040452929541871)
                  ·
                    rfl

theorem cell23_5634081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_5634081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634081 prefixEnd_5634081 := by exact prefixLift 5634081
  have htrace : WordTrace (prefixWord ++ tailWord_5634081) baseStart_5634081 baseEnd_5634081 := by
    simpa [prefixWord, tailWord_5634081, baseEnd_5634081] using wordTrace_append hprefix tailTrace_5634081
  have hstable : (prefixWord ++ tailWord_5634081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634081).length < 2 ^ (prefixWord ++ tailWord_5634081).sum := by decide
  have hdescent : baseEnd_5634081 < baseStart_5634081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634098 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_5634098 : Nat := 118140960795 + 5634098 * 2 ^ 59
def prefixEnd_5634098 : Nat := 4983230072969 + 3 ^ 40 * 5634098 * 2
def baseEnd_5634098 : Nat := 321444480948355866596029

theorem tailTrace_5634098 : CollatzResearch.WordTrace tailWord_5634098 prefixEnd_5634098 321444480948355866596029 := by
  unfold tailWord_5634098
  simp only [CollatzResearch.WordTrace]
  refine ⟨51373108985658162044169737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136994957295088432117785965 51373108985658162044169737)
  ·
    refine ⟨38529831739243621533127303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51373108985658162044169737 38529831739243621533127303)
    ·
      refine ⟨57794747608865432299690955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38529831739243621533127303 57794747608865432299690955)
      ·
        refine ⟨86692121413298148449536433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57794747608865432299690955 86692121413298148449536433)
        ·
          refine ⟨65019091059973611337152325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86692121413298148449536433 65019091059973611337152325)
          ·
            refine ⟨12191079573745052125716061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65019091059973611337152325 12191079573745052125716061)
            ·
              refine ⟨4571654840154394547143523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12191079573745052125716061 4571654840154394547143523)
              ·
                refine ⟨6857482260231591820715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571654840154394547143523 6857482260231591820715285)
                ·
                  refine ⟨321444480948355866596029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6857482260231591820715285 321444480948355866596029)
                  ·
                    rfl

theorem cell23_5634098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_5634098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634098 prefixEnd_5634098 := by exact prefixLift 5634098
  have htrace : WordTrace (prefixWord ++ tailWord_5634098) baseStart_5634098 baseEnd_5634098 := by
    simpa [prefixWord, tailWord_5634098, baseEnd_5634098] using wordTrace_append hprefix tailTrace_5634098
  have hstable : (prefixWord ++ tailWord_5634098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634098).length < 2 ^ (prefixWord ++ tailWord_5634098).sum := by decide
  have hdescent : baseEnd_5634098 < baseStart_5634098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634108 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_5634108 : Nat := 118140960795 + 5634108 * 2 ^ 59
def prefixEnd_5634108 : Nat := 4983230072969 + 3 ^ 40 * 5634108 * 2
def baseEnd_5634108 : Nat := 2893005463341747760239215

theorem tailTrace_5634108 : CollatzResearch.WordTrace tailWord_5634108 prefixEnd_5634108 2893005463341747760239215 := by
  unfold tailWord_5634108
  simp only [CollatzResearch.WordTrace]
  refine ⟨102746400336298209942271489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136995200448397613256361985 102746400336298209942271489)
  ·
    refine ⟨77059800252223657456703617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102746400336298209942271489 77059800252223657456703617)
    ·
      refine ⟨57794850189167743092527713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77059800252223657456703617 57794850189167743092527713)
      ·
        refine ⟨43346137641875807319395785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57794850189167743092527713 43346137641875807319395785)
        ·
          refine ⟨32509603231406855489546839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43346137641875807319395785 32509603231406855489546839)
          ·
            refine ⟨48764404847110283234320259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32509603231406855489546839 48764404847110283234320259)
            ·
              refine ⟨73146607270665424851480389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48764404847110283234320259 73146607270665424851480389)
              ·
                refine ⟨13714988863249767159652573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73146607270665424851480389 13714988863249767159652573)
                ·
                  refine ⟨5143120823718662684869715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13714988863249767159652573 5143120823718662684869715)
                  ·
                    refine ⟨7714681235577994027304573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143120823718662684869715 7714681235577994027304573)
                    ·
                      refine ⟨2893005463341747760239215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714681235577994027304573 2893005463341747760239215)
                      ·
                        rfl

theorem cell23_5634108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_5634108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634108 prefixEnd_5634108 := by exact prefixLift 5634108
  have htrace : WordTrace (prefixWord ++ tailWord_5634108) baseStart_5634108 baseEnd_5634108 := by
    simpa [prefixWord, tailWord_5634108, baseEnd_5634108] using wordTrace_append hprefix tailTrace_5634108
  have hstable : (prefixWord ++ tailWord_5634108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634108).length < 2 ^ (prefixWord ++ tailWord_5634108).sum := by decide
  have hdescent : baseEnd_5634108 < baseStart_5634108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634111 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 1, 5]
def baseStart_5634111 : Nat := 118140960795 + 5634111 * 2 ^ 59
def prefixEnd_5634111 : Nat := 4983230072969 + 3 ^ 40 * 5634111 * 2
def baseEnd_5634111 : Nat := 964335667927903749500567

theorem tailTrace_5634111 : CollatzResearch.WordTrace tailWord_5634111 prefixEnd_5634111 964335667927903749500567 := by
  unfold tailWord_5634111
  simp only [CollatzResearch.WordTrace]
  refine ⟨205492910091585551396902187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136995273394390367597934791 205492910091585551396902187)
  ·
    refine ⟨308239365137378327095353281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205492910091585551396902187 308239365137378327095353281)
    ·
      refine ⟨231179523853033745321514961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308239365137378327095353281 231179523853033745321514961)
      ·
        refine ⟨173384642889775308991136221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231179523853033745321514961 173384642889775308991136221)
        ·
          refine ⟨65019241083665740871676083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173384642889775308991136221 65019241083665740871676083)
          ·
            refine ⟨97528861625498611307514125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65019241083665740871676083 97528861625498611307514125)
            ·
              refine ⟨36573323109561979240317797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97528861625498611307514125 36573323109561979240317797)
              ·
                refine ⟨6857498083042871107559587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36573323109561979240317797 6857498083042871107559587)
                ·
                  refine ⟨10286247124564306661339381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6857498083042871107559587 10286247124564306661339381)
                  ·
                    refine ⟨964335667927903749500567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10286247124564306661339381 964335667927903749500567)
                    ·
                      rfl

theorem cell23_5634111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_5634111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634111 prefixEnd_5634111 := by exact prefixLift 5634111
  have htrace : WordTrace (prefixWord ++ tailWord_5634111) baseStart_5634111 baseEnd_5634111 := by
    simpa [prefixWord, tailWord_5634111, baseEnd_5634111] using wordTrace_append hprefix tailTrace_5634111
  have hstable : (prefixWord ++ tailWord_5634111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634111).length < 2 ^ (prefixWord ++ tailWord_5634111).sum := by decide
  have hdescent : baseEnd_5634111 < baseStart_5634111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634131 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 6, 2]
def baseStart_5634131 : Nat := 118140960795 + 5634131 * 2 ^ 59
def prefixEnd_5634131 : Nat := 4983230072969 + 3 ^ 40 * 5634131 * 2
def baseEnd_5634131 : Nat := 2893017273396801170251609

theorem tailTrace_5634131 : CollatzResearch.WordTrace tailWord_5634131 prefixEnd_5634131 2893017273396801170251609 := by
  unfold tailWord_5634131
  simp only [CollatzResearch.WordTrace]
  refine ⟨205493639551513094812630247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136995759701008729875086831 205493639551513094812630247)
  ·
    refine ⟨308240459327269642218945371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205493639551513094812630247 308240459327269642218945371)
    ·
      refine ⟨462360688990904463328418057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308240459327269642218945371 462360688990904463328418057)
      ·
        refine ⟨346770516743178347496313543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462360688990904463328418057 346770516743178347496313543)
        ·
          refine ⟨520155775114767521244470315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346770516743178347496313543 520155775114767521244470315)
          ·
            refine ⟨780233662672151281866705473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520155775114767521244470315 780233662672151281866705473)
            ·
              refine ⟨585175247004113461400029105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780233662672151281866705473 585175247004113461400029105)
              ·
                refine ⟨438881435253085096050021829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585175247004113461400029105 438881435253085096050021829)
                ·
                  refine ⟨82290269109953455509379093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438881435253085096050021829 82290269109953455509379093)
                  ·
                    refine ⟨3857356364529068227002145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82290269109953455509379093 3857356364529068227002145)
                    ·
                      refine ⟨2893017273396801170251609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857356364529068227002145 2893017273396801170251609)
                      ·
                        rfl

theorem cell23_5634131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6, 2].length) (baseStart_5634131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634131 prefixEnd_5634131 := by exact prefixLift 5634131
  have htrace : WordTrace (prefixWord ++ tailWord_5634131) baseStart_5634131 baseEnd_5634131 := by
    simpa [prefixWord, tailWord_5634131, baseEnd_5634131] using wordTrace_append hprefix tailTrace_5634131
  have hstable : (prefixWord ++ tailWord_5634131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634131).length < 2 ^ (prefixWord ++ tailWord_5634131).sum := by decide
  have hdescent : baseEnd_5634131 < baseStart_5634131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634151 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_5634151 : Nat := 118140960795 + 5634151 * 2 ^ 59
def prefixEnd_5634151 : Nat := 4983230072969 + 3 ^ 40 * 5634151 * 2
def baseEnd_5634151 : Nat := 2893027543009891092001517

theorem tailTrace_5634151 : CollatzResearch.WordTrace tailWord_5634151 prefixEnd_5634151 2893027543009891092001517 := by
  unfold tailWord_5634151
  simp only [CollatzResearch.WordTrace]
  refine ⟨205494369011440638228358307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136996246007627092152238871 205494369011440638228358307)
  ·
    refine ⟨308241553517160957342537461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205494369011440638228358307 308241553517160957342537461)
    ·
      refine ⟨28897645642233839750862887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308241553517160957342537461 28897645642233839750862887)
      ·
        refine ⟨43346468463350759626294331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28897645642233839750862887 43346468463350759626294331)
        ·
          refine ⟨65019702695026139439441497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43346468463350759626294331 65019702695026139439441497)
          ·
            refine ⟨48764777021269604579581123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65019702695026139439441497 48764777021269604579581123)
            ·
              refine ⟨73147165531904406869371685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48764777021269604579581123 73147165531904406869371685)
              ·
                refine ⟨13715093537232076288007191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73147165531904406869371685 13715093537232076288007191)
                ·
                  refine ⟨20572640305848114432010787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13715093537232076288007191 20572640305848114432010787)
                  ·
                    refine ⟨30858960458772171648016181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20572640305848114432010787 30858960458772171648016181)
                    ·
                      refine ⟨2893027543009891092001517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30858960458772171648016181 2893027543009891092001517)
                      ·
                        rfl

theorem cell23_5634151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_5634151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634151 prefixEnd_5634151 := by exact prefixLift 5634151
  have htrace : WordTrace (prefixWord ++ tailWord_5634151) baseStart_5634151 baseEnd_5634151 := by
    simpa [prefixWord, tailWord_5634151, baseEnd_5634151] using wordTrace_append hprefix tailTrace_5634151
  have hstable : (prefixWord ++ tailWord_5634151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634151).length < 2 ^ (prefixWord ++ tailWord_5634151).sum := by decide
  have hdescent : baseEnd_5634151 < baseStart_5634151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634161 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_5634161 : Nat := 118140960795 + 5634161 * 2 ^ 59
def prefixEnd_5634161 : Nat := 4983230072969 + 3 ^ 40 * 5634161 * 2
def baseEnd_5634161 : Nat := 2893032677816436052876471

theorem tailTrace_5634161 : CollatzResearch.WordTrace tailWord_5634161 prefixEnd_5634161 2893032677816436052876471 := by
  unfold tailWord_5634161
  simp only [CollatzResearch.WordTrace]
  refine ⟨205494733741404409936222337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136996489160936273290814891 205494733741404409936222337)
  ·
    refine ⟨154121050306053307452166753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205494733741404409936222337 154121050306053307452166753)
    ·
      refine ⟨115590787729539980589125065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154121050306053307452166753 115590787729539980589125065)
      ·
        refine ⟨86693090797154985441843799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115590787729539980589125065 86693090797154985441843799)
        ·
          refine ⟨130039636195732478162765699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86693090797154985441843799 130039636195732478162765699)
          ·
            refine ⟨195059454293598717244148549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130039636195732478162765699 195059454293598717244148549)
            ·
              refine ⟨36573647680049759483277853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195059454293598717244148549 36573647680049759483277853)
              ·
                refine ⟨13715117880018659806229195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36573647680049759483277853 13715117880018659806229195)
                ·
                  refine ⟨20572676820027989709343793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13715117880018659806229195 20572676820027989709343793)
                  ·
                    refine ⟨15429507615020992282007845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20572676820027989709343793 15429507615020992282007845)
                    ·
                      refine ⟨2893032677816436052876471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15429507615020992282007845 2893032677816436052876471)
                      ·
                        rfl

theorem cell23_5634161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_5634161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634161 prefixEnd_5634161 := by exact prefixLift 5634161
  have htrace : WordTrace (prefixWord ++ tailWord_5634161) baseStart_5634161 baseEnd_5634161 := by
    simpa [prefixWord, tailWord_5634161, baseEnd_5634161] using wordTrace_append hprefix tailTrace_5634161
  have hstable : (prefixWord ++ tailWord_5634161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634161).length < 2 ^ (prefixWord ++ tailWord_5634161).sum := by decide
  have hdescent : baseEnd_5634161 < baseStart_5634161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634185 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 1, 2, 3]
def baseStart_5634185 : Nat := 118140960795 + 5634185 * 2 ^ 59
def prefixEnd_5634185 : Nat := 4983230072969 + 3 ^ 40 * 5634185 * 2
def baseEnd_5634185 : Nat := 2893045001352143958976361

theorem tailTrace_5634185 : CollatzResearch.WordTrace tailWord_5634185 prefixEnd_5634185 2893045001352143958976361 := by
  unfold tailWord_5634185
  simp only [CollatzResearch.WordTrace]
  refine ⟨205495609093317462035096009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136997072728878308023397339 205495609093317462035096009)
  ·
    refine ⟨154121706819988096526322007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205495609093317462035096009 154121706819988096526322007)
    ·
      refine ⟨231182560229982144789483011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154121706819988096526322007 231182560229982144789483011)
      ·
        refine ⟨346773840344973217184224517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231182560229982144789483011 346773840344973217184224517)
        ·
          refine ⟨65020095064682478222042097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346773840344973217184224517 65020095064682478222042097)
          ·
            refine ⟨48765071298511858666531573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65020095064682478222042097 48765071298511858666531573)
            ·
              refine ⟨4571725434235486749987335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48765071298511858666531573 4571725434235486749987335)
              ·
                refine ⟨6857588151353230124981003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571725434235486749987335 6857588151353230124981003)
                ·
                  refine ⟨10286382227029845187471505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6857588151353230124981003 10286382227029845187471505)
                  ·
                    refine ⟨7714786670272383890603629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10286382227029845187471505 7714786670272383890603629)
                    ·
                      refine ⟨2893045001352143958976361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7714786670272383890603629 2893045001352143958976361)
                      ·
                        rfl

theorem cell23_5634185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 2, 3].length) (baseStart_5634185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634185 prefixEnd_5634185 := by exact prefixLift 5634185
  have htrace : WordTrace (prefixWord ++ tailWord_5634185) baseStart_5634185 baseEnd_5634185 := by
    simpa [prefixWord, tailWord_5634185, baseEnd_5634185] using wordTrace_append hprefix tailTrace_5634185
  have hstable : (prefixWord ++ tailWord_5634185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634185).length < 2 ^ (prefixWord ++ tailWord_5634185).sum := by decide
  have hdescent : baseEnd_5634185 < baseStart_5634185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634199 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 1, 2, 2]
def baseStart_5634199 : Nat := 118140960795 + 5634199 * 2 ^ 59
def prefixEnd_5634199 : Nat := 4983230072969 + 3 ^ 40 * 5634199 * 2
def baseEnd_5634199 : Nat := 2893052190081306904201297

theorem tailTrace_5634199 : CollatzResearch.WordTrace tailWord_5634199 prefixEnd_5634199 2893052190081306904201297 := by
  unfold tailWord_5634199
  simp only [CollatzResearch.WordTrace]
  refine ⟨205496119715266742426105651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136997413143511161617403767 205496119715266742426105651)
  ·
    refine ⟨308244179572900113639158477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205496119715266742426105651 308244179572900113639158477)
    ·
      refine ⟨115591567339837542614684429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308244179572900113639158477 115591567339837542614684429)
      ·
        refine ⟨43346837752439078480506661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115591567339837542614684429 43346837752439078480506661)
        ·
          refine ⟨8127532078582327215094999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43346837752439078480506661 8127532078582327215094999)
          ·
            refine ⟨12191298117873490822642499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127532078582327215094999 12191298117873490822642499)
            ·
              refine ⟨18286947176810236233963749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12191298117873490822642499 18286947176810236233963749)
              ·
                refine ⟨3428802595651919293868203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18286947176810236233963749 3428802595651919293868203)
                ·
                  refine ⟨5143203893477878940802305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428802595651919293868203 5143203893477878940802305)
                  ·
                    refine ⟨3857402920108409205601729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5143203893477878940802305 3857402920108409205601729)
                    ·
                      refine ⟨2893052190081306904201297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857402920108409205601729 2893052190081306904201297)
                      ·
                        rfl

theorem cell23_5634199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_5634199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634199 prefixEnd_5634199 := by exact prefixLift 5634199
  have htrace : WordTrace (prefixWord ++ tailWord_5634199) baseStart_5634199 baseEnd_5634199 := by
    simpa [prefixWord, tailWord_5634199, baseEnd_5634199] using wordTrace_append hprefix tailTrace_5634199
  have hstable : (prefixWord ++ tailWord_5634199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634199).length < 2 ^ (prefixWord ++ tailWord_5634199).sum := by decide
  have hdescent : baseEnd_5634199 < baseStart_5634199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634222 : List Nat := [4, 1, 4, 2, 1, 1, 3, 7]
def baseStart_5634222 : Nat := 118140960795 + 5634222 * 2 ^ 59
def prefixEnd_5634222 : Nat := 4983230072969 + 3 ^ 40 * 5634222 * 2
def baseEnd_5634222 : Nat := 107150518523568900526433

theorem tailTrace_5634222 : CollatzResearch.WordTrace tailWord_5634222 prefixEnd_5634222 107150518523568900526433 := by
  unfold tailWord_5634222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25687119824272927169274115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136997972396122278236128613 25687119824272927169274115)
  ·
    refine ⟨38530679736409390753911173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25687119824272927169274115 38530679736409390753911173)
    ·
      refine ⟨7224502450576760766358345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38530679736409390753911173 7224502450576760766358345)
      ·
        refine ⟨5418376837932570574768759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7224502450576760766358345 5418376837932570574768759)
        ·
          refine ⟨8127565256898855862153139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418376837932570574768759 8127565256898855862153139)
          ·
            refine ⟨12191347885348283793229709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127565256898855862153139 12191347885348283793229709)
            ·
              refine ⟨4571755457005606422461141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12191347885348283793229709 4571755457005606422461141)
              ·
                refine ⟨107150518523568900526433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4571755457005606422461141 107150518523568900526433)
                ·
                  rfl

theorem cell23_5634222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_5634222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634222 prefixEnd_5634222 := by exact prefixLift 5634222
  have htrace : WordTrace (prefixWord ++ tailWord_5634222) baseStart_5634222 baseEnd_5634222 := by
    simpa [prefixWord, tailWord_5634222, baseEnd_5634222] using wordTrace_append hprefix tailTrace_5634222
  have hstable : (prefixWord ++ tailWord_5634222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634222).length < 2 ^ (prefixWord ++ tailWord_5634222).sum := by decide
  have hdescent : baseEnd_5634222 < baseStart_5634222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634251 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_5634251 : Nat := 118140960795 + 5634251 * 2 ^ 59
def prefixEnd_5634251 : Nat := 4983230072969 + 3 ^ 40 * 5634251 * 2
def baseEnd_5634251 : Nat := 2893078891075340700751057

theorem tailTrace_5634251 : CollatzResearch.WordTrace tailWord_5634251 prefixEnd_5634251 2893078891075340700751057 := by
  unfold tailWord_5634251
  simp only [CollatzResearch.WordTrace]
  refine ⟨205498016311078355306998607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136998677540718903537999071 205498016311078355306998607)
  ·
    refine ⟨308247024466617532960497911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205498016311078355306998607 308247024466617532960497911)
    ·
      refine ⟨462370536699926299440746867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308247024466617532960497911 462370536699926299440746867)
      ·
        refine ⟨693555805049889449161120301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462370536699926299440746867 693555805049889449161120301)
        ·
          refine ⟨260083426893708543435420113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693555805049889449161120301 260083426893708543435420113)
          ·
            refine ⟨195062570170281407576565085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260083426893708543435420113 195062570170281407576565085)
            ·
              refine ⟨73148463813855527841211907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195062570170281407576565085 73148463813855527841211907)
              ·
                refine ⟨109722695720783291761817861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73148463813855527841211907 109722695720783291761817861)
                ·
                  refine ⟨20573005447646867205340849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109722695720783291761817861 20573005447646867205340849)
                  ·
                    refine ⟨15429754085735150404005637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20573005447646867205340849 15429754085735150404005637)
                    ·
                      refine ⟨2893078891075340700751057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15429754085735150404005637 2893078891075340700751057)
                      ·
                        rfl

theorem cell23_5634251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_5634251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634251 prefixEnd_5634251 := by exact prefixLift 5634251
  have htrace : WordTrace (prefixWord ++ tailWord_5634251) baseStart_5634251 baseEnd_5634251 := by
    simpa [prefixWord, tailWord_5634251, baseEnd_5634251] using wordTrace_append hprefix tailTrace_5634251
  have hstable : (prefixWord ++ tailWord_5634251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634251).length < 2 ^ (prefixWord ++ tailWord_5634251).sum := by decide
  have hdescent : baseEnd_5634251 < baseStart_5634251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634255 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 4, 2, 2]
def baseStart_5634255 : Nat := 118140960795 + 5634255 * 2 ^ 59
def prefixEnd_5634255 : Nat := 4983230072969 + 3 ^ 40 * 5634255 * 2
def baseEnd_5634255 : Nat := 2893080944997958685101039

theorem tailTrace_5634255 : CollatzResearch.WordTrace tailWord_5634255 prefixEnd_5634255 2893080944997958685101039 := by
  unfold tailWord_5634255
  simp only [CollatzResearch.WordTrace]
  refine ⟨205498162203063863990144219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136998774802042575993429479 205498162203063863990144219)
  ·
    refine ⟨308247243304595795985216329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205498162203063863990144219 308247243304595795985216329)
    ·
      refine ⟨231185432478446846988912247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308247243304595795985216329 231185432478446846988912247)
      ·
        refine ⟨346778148717670270483368371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231185432478446846988912247 346778148717670270483368371)
        ·
          refine ⟨520167223076505405725052557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346778148717670270483368371 520167223076505405725052557)
          ·
            refine ⟨195062708653689527146894709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 520167223076505405725052557 195062708653689527146894709)
            ·
              refine ⟨18287128936283393170021379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195062708653689527146894709 18287128936283393170021379)
              ·
                refine ⟨27430693404425089755032069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18287128936283393170021379 27430693404425089755032069)
                ·
                  refine ⟨5143255013329704329068513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27430693404425089755032069 5143255013329704329068513)
                  ·
                    refine ⟨3857441259997278246801385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5143255013329704329068513 3857441259997278246801385)
                    ·
                      refine ⟨2893080944997958685101039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857441259997278246801385 2893080944997958685101039)
                      ·
                        rfl

theorem cell23_5634255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 2, 2].length) (baseStart_5634255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634255 prefixEnd_5634255 := by exact prefixLift 5634255
  have htrace : WordTrace (prefixWord ++ tailWord_5634255) baseStart_5634255 baseEnd_5634255 := by
    simpa [prefixWord, tailWord_5634255, baseEnd_5634255] using wordTrace_append hprefix tailTrace_5634255
  have hstable : (prefixWord ++ tailWord_5634255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634255).length < 2 ^ (prefixWord ++ tailWord_5634255).sum := by decide
  have hdescent : baseEnd_5634255 < baseStart_5634255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634291 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 7]
def baseStart_5634291 : Nat := 118140960795 + 5634291 * 2 ^ 59
def prefixEnd_5634291 : Nat := 4983230072969 + 3 ^ 40 * 5634291 * 2
def baseEnd_5634291 : Nat := 964366476767173514750291

theorem tailTrace_5634291 : CollatzResearch.WordTrace tailWord_5634291 prefixEnd_5634291 964366476767173514750291 := by
  unfold tailWord_5634291
  simp only [CollatzResearch.WordTrace]
  refine ⟨205499475230933442138454727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136999650153955628092303151 205499475230933442138454727)
  ·
    refine ⟨308249212846400163207682091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205499475230933442138454727 308249212846400163207682091)
    ·
      refine ⟨462373819269600244811523137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308249212846400163207682091 462373819269600244811523137)
      ·
        refine ⟨346780364452200183608642353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462373819269600244811523137 346780364452200183608642353)
        ·
          refine ⟨260085273339150137706481765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346780364452200183608642353 260085273339150137706481765)
          ·
            refine ⟨48765988751090650819965331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260085273339150137706481765 48765988751090650819965331)
            ·
              refine ⟨73148983126635976229947997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48765988751090650819965331 73148983126635976229947997)
              ·
                refine ⟨27430868672488491086230499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73148983126635976229947997 27430868672488491086230499)
                ·
                  refine ⟨41146303008732736629345749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27430868672488491086230499 41146303008732736629345749)
                  ·
                    refine ⟨964366476767173514750291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41146303008732736629345749 964366476767173514750291)
                    ·
                      rfl

theorem cell23_5634291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_5634291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634291 prefixEnd_5634291 := by exact prefixLift 5634291
  have htrace : WordTrace (prefixWord ++ tailWord_5634291) baseStart_5634291 baseEnd_5634291 := by
    simpa [prefixWord, tailWord_5634291, baseEnd_5634291] using wordTrace_append hprefix tailTrace_5634291
  have hstable : (prefixWord ++ tailWord_5634291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634291).length < 2 ^ (prefixWord ++ tailWord_5634291).sum := by decide
  have hdescent : baseEnd_5634291 < baseStart_5634291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634301 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_5634301 : Nat := 118140960795 + 5634301 * 2 ^ 59
def prefixEnd_5634301 : Nat := 4983230072969 + 3 ^ 40 * 5634301 * 2
def baseEnd_5634301 : Nat := 2893104565108065505125827

theorem tailTrace_5634301 : CollatzResearch.WordTrace tailWord_5634301 prefixEnd_5634301 2893104565108065505125827 := by
  unfold tailWord_5634301
  simp only [CollatzResearch.WordTrace]
  refine ⟨205499839960897213846318757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136999893307264809230879171 205499839960897213846318757)
  ·
    refine ⟨38531219992668227596184767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205499839960897213846318757 38531219992668227596184767)
    ·
      refine ⟨57796829989002341394277151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38531219992668227596184767 57796829989002341394277151)
      ·
        refine ⟨86695244983503512091415727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57796829989002341394277151 86695244983503512091415727)
        ·
          refine ⟨130042867475255268137123591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86695244983503512091415727 130042867475255268137123591)
          ·
            refine ⟨195064301212882902205685387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130042867475255268137123591 195064301212882902205685387)
            ·
              refine ⟨292596451819324353308528081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195064301212882902205685387 292596451819324353308528081)
              ·
                refine ⟨219447338864493264981396061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292596451819324353308528081 219447338864493264981396061)
                ·
                  refine ⟨82292752074184974368023523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219447338864493264981396061 82292752074184974368023523)
                  ·
                    refine ⟨123439128111277461552035285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82292752074184974368023523 123439128111277461552035285)
                    ·
                      refine ⟨2893104565108065505125827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123439128111277461552035285 2893104565108065505125827)
                      ·
                        rfl

theorem cell23_5634301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_5634301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634301 prefixEnd_5634301 := by exact prefixLift 5634301
  have htrace : WordTrace (prefixWord ++ tailWord_5634301) baseStart_5634301 baseEnd_5634301 := by
    simpa [prefixWord, tailWord_5634301, baseEnd_5634301] using wordTrace_append hprefix tailTrace_5634301
  have hstable : (prefixWord ++ tailWord_5634301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634301).length < 2 ^ (prefixWord ++ tailWord_5634301).sum := by decide
  have hdescent : baseEnd_5634301 < baseStart_5634301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634312 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 5]
def baseStart_5634312 : Nat := 118140960795 + 5634312 * 2 ^ 59
def prefixEnd_5634312 : Nat := 4983230072969 + 3 ^ 40 * 5634312 * 2
def baseEnd_5634312 : Nat := 321456690377251662454253

theorem tailTrace_5634312 : CollatzResearch.WordTrace tailWord_5634312 prefixEnd_5634312 321456690377251662454253 := by
  unfold tailWord_5634312
  simp only [CollatzResearch.WordTrace]
  refine ⟨102750120581928681362484595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137000160775904908483312793 102750120581928681362484595)
  ·
    refine ⟨154125180872893022043726893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102750120581928681362484595 154125180872893022043726893)
    ·
      refine ⟨57796942827334883266397585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154125180872893022043726893 57796942827334883266397585)
      ·
        refine ⟨43347707120501162449798189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57796942827334883266397585 43347707120501162449798189)
        ·
          refine ⟨16255390170187935918674321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43347707120501162449798189 16255390170187935918674321)
          ·
            refine ⟨12191542627640951939005741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16255390170187935918674321 12191542627640951939005741)
            ·
              refine ⟨4571828485365356977127153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12191542627640951939005741 4571828485365356977127153)
              ·
                refine ⟨3428871364024017732845365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571828485365356977127153 3428871364024017732845365)
                ·
                  refine ⟨321456690377251662454253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3428871364024017732845365 321456690377251662454253)
                  ·
                    rfl

theorem cell23_5634312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 5].length) (baseStart_5634312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634312 prefixEnd_5634312 := by exact prefixLift 5634312
  have htrace : WordTrace (prefixWord ++ tailWord_5634312) baseStart_5634312 baseEnd_5634312 := by
    simpa [prefixWord, tailWord_5634312, baseEnd_5634312] using wordTrace_append hprefix tailTrace_5634312
  have hstable : (prefixWord ++ tailWord_5634312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634312).length < 2 ^ (prefixWord ++ tailWord_5634312).sum := by decide
  have hdescent : baseEnd_5634312 < baseStart_5634312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634318 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5634318 : Nat := 118140960795 + 5634318 * 2 ^ 59
def prefixEnd_5634318 : Nat := 4983230072969 + 3 ^ 40 * 5634318 * 2
def baseEnd_5634318 : Nat := 2893113294279191938613249

theorem tailTrace_5634318 : CollatzResearch.WordTrace tailWord_5634318 prefixEnd_5634318 2893113294279191938613249 := by
  unfold tailWord_5634318
  simp only [CollatzResearch.WordTrace]
  refine ⟨25687557500229453218710951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137000306667890417166458405 25687557500229453218710951)
  ·
    refine ⟨38531336250344179828066427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25687557500229453218710951 38531336250344179828066427)
    ·
      refine ⟨57797004375516269742099641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38531336250344179828066427 57797004375516269742099641)
      ·
        refine ⟨43347753281637202306574731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57797004375516269742099641 43347753281637202306574731)
        ·
          refine ⟨65021629922455803459862097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43347753281637202306574731 65021629922455803459862097)
          ·
            refine ⟨48766222441841852594896573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65021629922455803459862097 48766222441841852594896573)
            ·
              refine ⟨18287333415690694723086215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48766222441841852594896573 18287333415690694723086215)
              ·
                refine ⟨27431000123536042084629323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18287333415690694723086215 27431000123536042084629323)
                ·
                  refine ⟨41146500185304063126943985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27431000123536042084629323 41146500185304063126943985)
                  ·
                    refine ⟨30859875138978047345207989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41146500185304063126943985 30859875138978047345207989)
                    ·
                      refine ⟨2893113294279191938613249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30859875138978047345207989 2893113294279191938613249)
                      ·
                        rfl

theorem cell23_5634318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5634318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634318 prefixEnd_5634318 := by exact prefixLift 5634318
  have htrace : WordTrace (prefixWord ++ tailWord_5634318) baseStart_5634318 baseEnd_5634318 := by
    simpa [prefixWord, tailWord_5634318, baseEnd_5634318] using wordTrace_append hprefix tailTrace_5634318
  have hstable : (prefixWord ++ tailWord_5634318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634318).length < 2 ^ (prefixWord ++ tailWord_5634318).sum := by decide
  have hdescent : baseEnd_5634318 < baseStart_5634318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634328 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5634328 : Nat := 118140960795 + 5634328 * 2 ^ 59
def prefixEnd_5634328 : Nat := 4983230072969 + 3 ^ 40 * 5634328 * 2
def baseEnd_5634328 : Nat := 2893118429085736899488203

theorem tailTrace_5634328 : CollatzResearch.WordTrace tailWord_5634328 prefixEnd_5634328 2893118429085736899488203 := by
  unfold tailWord_5634328
  simp only [CollatzResearch.WordTrace]
  refine ⟨102750412365899698728775819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137000549821199598305034425 102750412365899698728775819)
  ·
    refine ⟨154125618548849548093163729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102750412365899698728775819 154125618548849548093163729)
    ·
      refine ⟨115594213911637161069872797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154125618548849548093163729 115594213911637161069872797)
      ·
        refine ⟨43347830216863935401202299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115594213911637161069872797 43347830216863935401202299)
        ·
          refine ⟨65021745325295903101803449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43347830216863935401202299 65021745325295903101803449)
          ·
            refine ⟨48766308993971927326352587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65021745325295903101803449 48766308993971927326352587)
            ·
              refine ⟨73149463490957890989528881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48766308993971927326352587 73149463490957890989528881)
              ·
                refine ⟨54862097618218418242146661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73149463490957890989528881 54862097618218418242146661)
                ·
                  refine ⟨10286643303415953420402499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54862097618218418242146661 10286643303415953420402499)
                  ·
                    refine ⟨15429964955123930130603749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10286643303415953420402499 15429964955123930130603749)
                    ·
                      refine ⟨2893118429085736899488203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15429964955123930130603749 2893118429085736899488203)
                      ·
                        rfl

theorem cell23_5634328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5634328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634328 prefixEnd_5634328 := by exact prefixLift 5634328
  have htrace : WordTrace (prefixWord ++ tailWord_5634328) baseStart_5634328 baseEnd_5634328 := by
    simpa [prefixWord, tailWord_5634328, baseEnd_5634328] using wordTrace_append hprefix tailTrace_5634328
  have hstable : (prefixWord ++ tailWord_5634328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634328).length < 2 ^ (prefixWord ++ tailWord_5634328).sum := by decide
  have hdescent : baseEnd_5634328 < baseStart_5634328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634348 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_5634348 : Nat := 118140960795 + 5634348 * 2 ^ 59
def prefixEnd_5634348 : Nat := 4983230072969 + 3 ^ 40 * 5634348 * 2
def baseEnd_5634348 : Nat := 2893128698698826821238111

theorem tailTrace_5634348 : CollatzResearch.WordTrace tailWord_5634348 prefixEnd_5634348 2893128698698826821238111 := by
  unfold tailWord_5634348
  simp only [CollatzResearch.WordTrace]
  refine ⟨102750777095863470436639849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137001036127817960582186465 102750777095863470436639849)
  ·
    refine ⟨77063082821897602827479887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102750777095863470436639849 77063082821897602827479887)
    ·
      refine ⟨115594624232846404241219831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77063082821897602827479887 115594624232846404241219831)
      ·
        refine ⟨173391936349269606361829747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115594624232846404241219831 173391936349269606361829747)
        ·
          refine ⟨260087904523904409542744621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173391936349269606361829747 260087904523904409542744621)
          ·
            refine ⟨97532964196464153578529233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260087904523904409542744621 97532964196464153578529233)
            ·
              refine ⟨73149723147348115183896925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97532964196464153578529233 73149723147348115183896925)
              ·
                refine ⟨27431146180255543193961347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73149723147348115183896925 27431146180255543193961347)
                ·
                  refine ⟨41146719270383314790942021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27431146180255543193961347 41146719270383314790942021)
                  ·
                    refine ⟨7715009863196871523301629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41146719270383314790942021 7715009863196871523301629)
                    ·
                      refine ⟨2893128698698826821238111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715009863196871523301629 2893128698698826821238111)
                      ·
                        rfl

theorem cell23_5634348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_5634348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634348 prefixEnd_5634348 := by exact prefixLift 5634348
  have htrace : WordTrace (prefixWord ++ tailWord_5634348) baseStart_5634348 baseEnd_5634348 := by
    simpa [prefixWord, tailWord_5634348, baseEnd_5634348] using wordTrace_append hprefix tailTrace_5634348
  have hstable : (prefixWord ++ tailWord_5634348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634348).length < 2 ^ (prefixWord ++ tailWord_5634348).sum := by decide
  have hdescent : baseEnd_5634348 < baseStart_5634348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634351 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 10]
def baseStart_5634351 : Nat := 118140960795 + 5634351 * 2 ^ 59
def prefixEnd_5634351 : Nat := 4983230072969 + 3 ^ 40 * 5634351 * 2
def baseEnd_5634351 : Nat := 321458915460087812166733

theorem tailTrace_5634351 : CollatzResearch.WordTrace tailWord_5634351 prefixEnd_5634351 321458915460087812166733 := by
  unfold tailWord_5634351
  simp only [CollatzResearch.WordTrace]
  refine ⟨205501663610716072385638907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137001109073810714923759271 205501663610716072385638907)
  ·
    refine ⟨308252495416074108578458361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205501663610716072385638907 308252495416074108578458361)
    ·
      refine ⟨231189371562055581433843771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308252495416074108578458361 231189371562055581433843771)
      ·
        refine ⟨346784057343083372150765657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231189371562055581433843771 346784057343083372150765657)
        ·
          refine ⟨260088043007312529113074243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346784057343083372150765657 260088043007312529113074243)
          ·
            refine ⟨390132064510968793669611365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260088043007312529113074243 390132064510968793669611365)
            ·
              refine ⟨73149762095806648813052131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 390132064510968793669611365 73149762095806648813052131)
              ·
                refine ⟨109724643143709973219578197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73149762095806648813052131 109724643143709973219578197)
                ·
                  refine ⟨321458915460087812166733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 109724643143709973219578197 321458915460087812166733)
                  ·
                    rfl

theorem cell23_5634351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 10].length) (baseStart_5634351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634351 prefixEnd_5634351 := by exact prefixLift 5634351
  have htrace : WordTrace (prefixWord ++ tailWord_5634351) baseStart_5634351 baseEnd_5634351 := by
    simpa [prefixWord, tailWord_5634351, baseEnd_5634351] using wordTrace_append hprefix tailTrace_5634351
  have hstable : (prefixWord ++ tailWord_5634351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634351).length < 2 ^ (prefixWord ++ tailWord_5634351).sum := by decide
  have hdescent : baseEnd_5634351 < baseStart_5634351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634378 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_5634378 : Nat := 118140960795 + 5634378 * 2 ^ 59
def prefixEnd_5634378 : Nat := 4983230072969 + 3 ^ 40 * 5634378 * 2
def baseEnd_5634378 : Nat := 2893144103118461703862973

theorem tailTrace_5634378 : CollatzResearch.WordTrace tailWord_5634378 prefixEnd_5634378 2893144103118461703862973 := by
  unfold tailWord_5634378
  simp only [CollatzResearch.WordTrace]
  refine ⟨51375662095404563999217947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137001765587745503997914525 51375662095404563999217947)
  ·
    refine ⟨77063493143106845998826921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51375662095404563999217947 77063493143106845998826921)
    ·
      refine ⟨57797619857330134499120191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77063493143106845998826921 57797619857330134499120191)
      ·
        refine ⟨86696429785995201748680287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57797619857330134499120191 86696429785995201748680287)
        ·
          refine ⟨130044644678992802623020431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86696429785995201748680287 130044644678992802623020431)
          ·
            refine ⟨195066967018489203934530647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130044644678992802623020431 195066967018489203934530647)
            ·
              refine ⟨292600450527733805901795971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195066967018489203934530647 292600450527733805901795971)
              ·
                refine ⟨438900675791600708852693957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292600450527733805901795971 438900675791600708852693957)
                ·
                  refine ⟨82293876710925132909880117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438900675791600708852693957 82293876710925132909880117)
                  ·
                    refine ⟨7715050941649231210301261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82293876710925132909880117 7715050941649231210301261)
                    ·
                      refine ⟨2893144103118461703862973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715050941649231210301261 2893144103118461703862973)
                      ·
                        rfl

theorem cell23_5634378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_5634378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634378 prefixEnd_5634378 := by exact prefixLift 5634378
  have htrace : WordTrace (prefixWord ++ tailWord_5634378) baseStart_5634378 baseEnd_5634378 := by
    simpa [prefixWord, tailWord_5634378, baseEnd_5634378] using wordTrace_append hprefix tailTrace_5634378
  have hstable : (prefixWord ++ tailWord_5634378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634378).length < 2 ^ (prefixWord ++ tailWord_5634378).sum := by decide
  have hdescent : baseEnd_5634378 < baseStart_5634378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634396 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5634396 : Nat := 118140960795 + 5634396 * 2 ^ 59
def prefixEnd_5634396 : Nat := 4983230072969 + 3 ^ 40 * 5634396 * 2
def baseEnd_5634396 : Nat := 2893153345770242633437891

theorem tailTrace_5634396 : CollatzResearch.WordTrace tailWord_5634396 prefixEnd_5634396 2893153345770242633437891 := by
  unfold tailWord_5634396
  simp only [CollatzResearch.WordTrace]
  refine ⟨102751652447776522535513521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137002203263702030047351361 102751652447776522535513521)
  ·
    refine ⟨77063739335832391901635141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102751652447776522535513521 77063739335832391901635141)
    ·
      refine ⟨14449451125468573481556589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77063739335832391901635141 14449451125468573481556589)
      ·
        refine ⟨5418544172050715055583721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14449451125468573481556589 5418544172050715055583721)
        ·
          refine ⟨4063908129038036291687791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418544172050715055583721 4063908129038036291687791)
          ·
            refine ⟨6095862193557054437531687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063908129038036291687791 6095862193557054437531687)
            ·
              refine ⟨9143793290335581656297531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095862193557054437531687 9143793290335581656297531)
              ·
                refine ⟨13715689935503372484446297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9143793290335581656297531 13715689935503372484446297)
                ·
                  refine ⟨10286767451627529363334723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13715689935503372484446297 10286767451627529363334723)
                  ·
                    refine ⟨15430151177441294045002085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10286767451627529363334723 15430151177441294045002085)
                    ·
                      refine ⟨2893153345770242633437891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15430151177441294045002085 2893153345770242633437891)
                      ·
                        rfl

theorem cell23_5634396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5634396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634396 prefixEnd_5634396 := by exact prefixLift 5634396
  have htrace : WordTrace (prefixWord ++ tailWord_5634396) baseStart_5634396 baseEnd_5634396 := by
    simpa [prefixWord, tailWord_5634396, baseEnd_5634396] using wordTrace_append hprefix tailTrace_5634396
  have hstable : (prefixWord ++ tailWord_5634396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634396).length < 2 ^ (prefixWord ++ tailWord_5634396).sum := by decide
  have hdescent : baseEnd_5634396 < baseStart_5634396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634429 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_5634429 : Nat := 118140960795 + 5634429 * 2 ^ 59
def prefixEnd_5634429 : Nat := 4983230072969 + 3 ^ 40 * 5634429 * 2
def baseEnd_5634429 : Nat := 2893170290631841004325239

theorem tailTrace_5634429 : CollatzResearch.WordTrace tailWord_5634429 prefixEnd_5634429 2893170290631841004325239 := by
  unfold tailWord_5634429
  simp only [CollatzResearch.WordTrace]
  refine ⟨205504508504433491706978341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137003005669622327804652227 205504508504433491706978341)
  ·
    refine ⟨38532095344581279695058439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205504508504433491706978341 38532095344581279695058439)
    ·
      refine ⟨57798143016871919542587659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38532095344581279695058439 57798143016871919542587659)
      ·
        refine ⟨86697214525307879313881489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57798143016871919542587659 86697214525307879313881489)
        ·
          refine ⟨65022910893980909485411117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86697214525307879313881489 65022910893980909485411117)
          ·
            refine ⟨24383591585242841057029169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65022910893980909485411117 24383591585242841057029169)
            ·
              refine ⟨18287693688932130792771877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24383591585242841057029169 18287693688932130792771877)
              ·
                refine ⟨3428942566674774523644727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18287693688932130792771877 3428942566674774523644727)
                ·
                  refine ⟨5143413850012161785467091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428942566674774523644727 5143413850012161785467091)
                  ·
                    refine ⟨7715120775018242678200637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143413850012161785467091 7715120775018242678200637)
                    ·
                      refine ⟨2893170290631841004325239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715120775018242678200637 2893170290631841004325239)
                      ·
                        rfl

theorem cell23_5634429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_5634429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634429 prefixEnd_5634429 := by exact prefixLift 5634429
  have htrace : WordTrace (prefixWord ++ tailWord_5634429) baseStart_5634429 baseEnd_5634429 := by
    simpa [prefixWord, tailWord_5634429, baseEnd_5634429] using wordTrace_append hprefix tailTrace_5634429
  have hstable : (prefixWord ++ tailWord_5634429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634429).length < 2 ^ (prefixWord ++ tailWord_5634429).sum := by decide
  have hdescent : baseEnd_5634429 < baseStart_5634429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634448 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_5634448 : Nat := 118140960795 + 5634448 * 2 ^ 59
def prefixEnd_5634448 : Nat := 4983230072969 + 3 ^ 40 * 5634448 * 2
def baseEnd_5634448 : Nat := 2893180046764276429987651

theorem tailTrace_5634448 : CollatzResearch.WordTrace tailWord_5634448 prefixEnd_5634448 2893180046764276429987651 := by
  unfold tailWord_5634448
  simp only [CollatzResearch.WordTrace]
  refine ⟨102752600745682328975959999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137003467660909771967946665 102752600745682328975959999)
  ·
    refine ⟨154128901118523493463939999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102752600745682328975959999 154128901118523493463939999)
    ·
      refine ⟨231193351677785240195909999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154128901118523493463939999 231193351677785240195909999)
      ·
        refine ⟨346790027516677860293864999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231193351677785240195909999 346790027516677860293864999)
        ·
          refine ⟨520185041275016790440797499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346790027516677860293864999 520185041275016790440797499)
          ·
            refine ⟨780277561912525185661196249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520185041275016790440797499 780277561912525185661196249)
            ·
              refine ⟨585208171434393889245897187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780277561912525185661196249 585208171434393889245897187)
              ·
                refine ⟨877812257151590833868845781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585208171434393889245897187 877812257151590833868845781)
                ·
                  refine ⟨20573724776990410168801073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 877812257151590833868845781 20573724776990410168801073)
                  ·
                    refine ⟨15430293582742807626600805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20573724776990410168801073 15430293582742807626600805)
                    ·
                      refine ⟨2893180046764276429987651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15430293582742807626600805 2893180046764276429987651)
                      ·
                        rfl

theorem cell23_5634448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_5634448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634448 prefixEnd_5634448 := by exact prefixLift 5634448
  have htrace : WordTrace (prefixWord ++ tailWord_5634448) baseStart_5634448 baseEnd_5634448 := by
    simpa [prefixWord, tailWord_5634448, baseEnd_5634448] using wordTrace_append hprefix tailTrace_5634448
  have hstable : (prefixWord ++ tailWord_5634448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634448).length < 2 ^ (prefixWord ++ tailWord_5634448).sum := by decide
  have hdescent : baseEnd_5634448 < baseStart_5634448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634455 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_5634455 : Nat := 118140960795 + 5634455 * 2 ^ 59
def prefixEnd_5634455 : Nat := 4983230072969 + 3 ^ 40 * 5634455 * 2
def baseEnd_5634455 : Nat := 2893183641128857902600119

theorem tailTrace_5634455 : CollatzResearch.WordTrace tailWord_5634455 prefixEnd_5634455 2893183641128857902600119 := by
  unfold tailWord_5634455
  simp only [CollatzResearch.WordTrace]
  refine ⟨205505456802339298147424819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137003637868226198764949879 205505456802339298147424819)
  ·
    refine ⟨308258185203508947221137229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205505456802339298147424819 308258185203508947221137229)
    ·
      refine ⟨115596819451315855207926461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308258185203508947221137229 115596819451315855207926461)
      ·
        refine ⟨43348807294243445702972423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115596819451315855207926461 43348807294243445702972423)
        ·
          refine ⟨65023210941365168554458635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43348807294243445702972423 65023210941365168554458635)
          ·
            refine ⟨97534816412047752831687953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65023210941365168554458635 97534816412047752831687953)
            ·
              refine ⟨73151112309035814623765965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97534816412047752831687953 73151112309035814623765965)
              ·
                refine ⟨27431667115888430483912237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73151112309035814623765965 27431667115888430483912237)
                ·
                  refine ⟨10286875168458161431467089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27431667115888430483912237 10286875168458161431467089)
                  ·
                    refine ⟨7715156376343621073600317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10286875168458161431467089 7715156376343621073600317)
                    ·
                      refine ⟨2893183641128857902600119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715156376343621073600317 2893183641128857902600119)
                      ·
                        rfl

theorem cell23_5634455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_5634455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634455 prefixEnd_5634455 := by exact prefixLift 5634455
  have htrace : WordTrace (prefixWord ++ tailWord_5634455) baseStart_5634455 baseEnd_5634455 := by
    simpa [prefixWord, tailWord_5634455, baseEnd_5634455] using wordTrace_append hprefix tailTrace_5634455
  have hstable : (prefixWord ++ tailWord_5634455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634455).length < 2 ^ (prefixWord ++ tailWord_5634455).sum := by decide
  have hdescent : baseEnd_5634455 < baseStart_5634455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634472 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5634472 : Nat := 118140960795 + 5634472 * 2 ^ 59
def prefixEnd_5634472 : Nat := 4983230072969 + 3 ^ 40 * 5634472 * 2
def baseEnd_5634472 : Nat := 2893192370299984336087541

theorem tailTrace_5634472 : CollatzResearch.WordTrace tailWord_5634472 prefixEnd_5634472 2893192370299984336087541 := by
  unfold tailWord_5634472
  simp only [CollatzResearch.WordTrace]
  refine ⟨102753038421638855025396835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137004051228851806700529113 102753038421638855025396835)
  ·
    refine ⟨154129557632458282538095253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102753038421638855025396835 154129557632458282538095253)
    ·
      refine ⟨7224823014021481993973215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154129557632458282538095253 7224823014021481993973215)
      ·
        refine ⟨10837234521032222990959823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7224823014021481993973215 10837234521032222990959823)
        ·
          refine ⟨16255851781548334486439735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10837234521032222990959823 16255851781548334486439735)
          ·
            refine ⟨24383777672322501729659603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16255851781548334486439735 24383777672322501729659603)
            ·
              refine ⟨36575666508483752594489405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24383777672322501729659603 36575666508483752594489405)
              ·
                refine ⟨13715874940681407222933527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36575666508483752594489405 13715874940681407222933527)
                ·
                  refine ⟨20573812411022110834400291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13715874940681407222933527 20573812411022110834400291)
                  ·
                    refine ⟨30860718616533166251600437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20573812411022110834400291 30860718616533166251600437)
                    ·
                      refine ⟨2893192370299984336087541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30860718616533166251600437 2893192370299984336087541)
                      ·
                        rfl

theorem cell23_5634472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5634472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634472 prefixEnd_5634472 := by exact prefixLift 5634472
  have htrace : WordTrace (prefixWord ++ tailWord_5634472) baseStart_5634472 baseEnd_5634472 := by
    simpa [prefixWord, tailWord_5634472, baseEnd_5634472] using wordTrace_append hprefix tailTrace_5634472
  have hstable : (prefixWord ++ tailWord_5634472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634472).length < 2 ^ (prefixWord ++ tailWord_5634472).sum := by decide
  have hdescent : baseEnd_5634472 < baseStart_5634472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634488 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_5634488 : Nat := 118140960795 + 5634488 * 2 ^ 59
def prefixEnd_5634488 : Nat := 4983230072969 + 3 ^ 40 * 5634488 * 2
def baseEnd_5634488 : Nat := 964400195330152091162489

theorem tailTrace_5634488 : CollatzResearch.WordTrace tailWord_5634488 prefixEnd_5634488 964400195330152091162489 := by
  unfold tailWord_5634488
  simp only [CollatzResearch.WordTrace]
  refine ⟨102753330205609872391688059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137004440274146496522250745 102753330205609872391688059)
  ·
    refine ⟨154129995308414808587532089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102753330205609872391688059 154129995308414808587532089)
    ·
      refine ⟨115597496481311106440649067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154129995308414808587532089 115597496481311106440649067)
      ·
        refine ⟨173396244721966659660973601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115597496481311106440649067 173396244721966659660973601)
        ·
          refine ⟨130047183541474994745730201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173396244721966659660973601 130047183541474994745730201)
          ·
            refine ⟨97535387656106246059297651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130047183541474994745730201 97535387656106246059297651)
            ·
              refine ⟨146303081484159369088946477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97535387656106246059297651 146303081484159369088946477)
              ·
                refine ⟨54863655556559763408354929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146303081484159369088946477 54863655556559763408354929)
                ·
                  refine ⟨41147741667419822556266197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54863655556559763408354929 41147741667419822556266197)
                  ·
                    refine ⟨964400195330152091162489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41147741667419822556266197 964400195330152091162489)
                    ·
                      rfl

theorem cell23_5634488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_5634488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634488 prefixEnd_5634488 := by exact prefixLift 5634488
  have htrace : WordTrace (prefixWord ++ tailWord_5634488) baseStart_5634488 baseEnd_5634488 := by
    simpa [prefixWord, tailWord_5634488, baseEnd_5634488] using wordTrace_append hprefix tailTrace_5634488
  have hstable : (prefixWord ++ tailWord_5634488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634488).length < 2 ^ (prefixWord ++ tailWord_5634488).sum := by decide
  have hdescent : baseEnd_5634488 < baseStart_5634488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634495 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 1, 9, 2]
def baseStart_5634495 : Nat := 118140960795 + 5634495 * 2 ^ 59
def prefixEnd_5634495 : Nat := 4983230072969 + 3 ^ 40 * 5634495 * 2
def baseEnd_5634495 : Nat := 2893204180355037746099935

theorem tailTrace_5634495 : CollatzResearch.WordTrace tailWord_5634495 prefixEnd_5634495 2893204180355037746099935 := by
  unfold tailWord_5634495
  simp only [CollatzResearch.WordTrace]
  refine ⟨205506915722194384978880939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137004610481462923319253959 205506915722194384978880939)
  ·
    refine ⟨308260373583291577468321409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205506915722194384978880939 308260373583291577468321409)
    ·
      refine ⟨231195280187468683101241057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308260373583291577468321409 231195280187468683101241057)
      ·
        refine ⟨173396460140601512325930793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231195280187468683101241057 173396460140601512325930793)
        ·
          refine ⟨130047345105451134244448095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173396460140601512325930793 130047345105451134244448095)
          ·
            refine ⟨195071017658176701366672143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130047345105451134244448095 195071017658176701366672143)
            ·
              refine ⟨292606526487265052050008215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195071017658176701366672143 292606526487265052050008215)
              ·
                refine ⟨438909789730897578075012323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292606526487265052050008215 438909789730897578075012323)
                ·
                  refine ⟨658364684596346367112518485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438909789730897578075012323 658364684596346367112518485)
                  ·
                    refine ⟨3857605573806716994799913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 658364684596346367112518485 3857605573806716994799913)
                    ·
                      refine ⟨2893204180355037746099935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857605573806716994799913 2893204180355037746099935)
                      ·
                        rfl

theorem cell23_5634495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_5634495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634495 prefixEnd_5634495 := by exact prefixLift 5634495
  have htrace : WordTrace (prefixWord ++ tailWord_5634495) baseStart_5634495 baseEnd_5634495 := by
    simpa [prefixWord, tailWord_5634495, baseEnd_5634495] using wordTrace_append hprefix tailTrace_5634495
  have hstable : (prefixWord ++ tailWord_5634495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634495).length < 2 ^ (prefixWord ++ tailWord_5634495).sum := by decide
  have hdescent : baseEnd_5634495 < baseStart_5634495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634535 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 2, 6]
def baseStart_5634535 : Nat := 118140960795 + 5634535 * 2 ^ 59
def prefixEnd_5634535 : Nat := 4983230072969 + 3 ^ 40 * 5634535 * 2
def baseEnd_5634535 : Nat := 964408239860405863199917

theorem tailTrace_5634535 : CollatzResearch.WordTrace tailWord_5634535 prefixEnd_5634535 964408239860405863199917 := by
  unfold tailWord_5634535
  simp only [CollatzResearch.WordTrace]
  refine ⟨205508374642049471810337059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137005583094699647873558039 205508374642049471810337059)
  ·
    refine ⟨308262561963074207715505589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205508374642049471810337059 308262561963074207715505589)
    ·
      refine ⟨28899615184038206973328649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308262561963074207715505589 28899615184038206973328649)
      ·
        refine ⟨21674711388028655229996487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28899615184038206973328649 21674711388028655229996487)
        ·
          refine ⟨32512067082042982844994731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21674711388028655229996487 32512067082042982844994731)
          ·
            refine ⟨48768100623064474267492097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32512067082042982844994731 48768100623064474267492097)
            ·
              refine ⟨36576075467298355700619073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48768100623064474267492097 36576075467298355700619073)
              ·
                refine ⟨27432056600473766775464305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36576075467298355700619073 27432056600473766775464305)
                ·
                  refine ⟨20574042450355325081598229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27432056600473766775464305 20574042450355325081598229)
                  ·
                    refine ⟨964408239860405863199917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20574042450355325081598229 964408239860405863199917)
                    ·
                      rfl

theorem cell23_5634535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_5634535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634535 prefixEnd_5634535 := by exact prefixLift 5634535
  have htrace : WordTrace (prefixWord ++ tailWord_5634535) baseStart_5634535 baseEnd_5634535 := by
    simpa [prefixWord, tailWord_5634535, baseEnd_5634535] using wordTrace_append hprefix tailTrace_5634535
  have hstable : (prefixWord ++ tailWord_5634535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634535).length < 2 ^ (prefixWord ++ tailWord_5634535).sum := by decide
  have hdescent : baseEnd_5634535 < baseStart_5634535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634545 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_5634545 : Nat := 118140960795 + 5634545 * 2 ^ 59
def prefixEnd_5634545 : Nat := 4983230072969 + 3 ^ 40 * 5634545 * 2
def baseEnd_5634545 : Nat := 2893229854387762550474705

theorem tailTrace_5634545 : CollatzResearch.WordTrace tailWord_5634545 prefixEnd_5634545 2893229854387762550474705 := by
  unfold tailWord_5634545
  simp only [CollatzResearch.WordTrace]
  refine ⟨205508739372013243518201089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137005826248008829012134059 205508739372013243518201089)
  ·
    refine ⟨154131554529009932638650817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205508739372013243518201089 154131554529009932638650817)
    ·
      refine ⟨115598665896757449478988113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154131554529009932638650817 115598665896757449478988113)
      ·
        refine ⟨86698999422568087109241085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115598665896757449478988113 86698999422568087109241085)
        ·
          refine ⟨32512124783463032665965407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86698999422568087109241085 32512124783463032665965407)
          ·
            refine ⟨48768187175194548998948111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32512124783463032665965407 48768187175194548998948111)
            ·
              refine ⟨73152280762791823498422167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48768187175194548998948111 73152280762791823498422167)
              ·
                refine ⟨109728421144187735247633251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73152280762791823498422167 109728421144187735247633251)
                ·
                  refine ⟨164592631716281602871449877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109728421144187735247633251 164592631716281602871449877)
                  ·
                    refine ⟨7715279611700700134599213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164592631716281602871449877 7715279611700700134599213)
                    ·
                      refine ⟨2893229854387762550474705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715279611700700134599213 2893229854387762550474705)
                      ·
                        rfl

theorem cell23_5634545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_5634545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634545 prefixEnd_5634545 := by exact prefixLift 5634545
  have htrace : WordTrace (prefixWord ++ tailWord_5634545) baseStart_5634545 baseEnd_5634545 := by
    simpa [prefixWord, tailWord_5634545, baseEnd_5634545] using wordTrace_append hprefix tailTrace_5634545
  have hstable : (prefixWord ++ tailWord_5634545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634545).length < 2 ^ (prefixWord ++ tailWord_5634545).sum := by decide
  have hdescent : baseEnd_5634545 < baseStart_5634545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634559 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 2, 2, 2]
def baseStart_5634559 : Nat := 118140960795 + 5634559 * 2 ^ 59
def prefixEnd_5634559 : Nat := 4983230072969 + 3 ^ 40 * 5634559 * 2
def baseEnd_5634559 : Nat := 2893237043116925495699641

theorem tailTrace_5634559 : CollatzResearch.WordTrace tailWord_5634559 prefixEnd_5634559 2893237043116925495699641 := by
  unfold tailWord_5634559
  simp only [CollatzResearch.WordTrace]
  refine ⟨205509249993962523909210731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137006166662641682606140487 205509249993962523909210731)
  ·
    refine ⟨308263874990943785863816097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205509249993962523909210731 308263874990943785863816097)
    ·
      refine ⟨231197906243207839397862073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308263874990943785863816097 231197906243207839397862073)
      ·
        refine ⟨173398429682405879548396555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231197906243207839397862073 173398429682405879548396555)
        ·
          refine ⟨260097644523608819322594833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173398429682405879548396555 260097644523608819322594833)
          ·
            refine ⟨195073233392706614491946125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260097644523608819322594833 195073233392706614491946125)
            ·
              refine ⟨73152462522264980434479797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195073233392706614491946125 73152462522264980434479797)
              ·
                refine ⟨6858043361462341915732481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73152462522264980434479797 6858043361462341915732481)
                ·
                  refine ⟨5143532521096756436799361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6858043361462341915732481 5143532521096756436799361)
                  ·
                    refine ⟨3857649390822567327599521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5143532521096756436799361 3857649390822567327599521)
                    ·
                      refine ⟨2893237043116925495699641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857649390822567327599521 2893237043116925495699641)
                      ·
                        rfl

theorem cell23_5634559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_5634559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634559 prefixEnd_5634559 := by exact prefixLift 5634559
  have htrace : WordTrace (prefixWord ++ tailWord_5634559) baseStart_5634559 baseEnd_5634559 := by
    simpa [prefixWord, tailWord_5634559, baseEnd_5634559] using wordTrace_append hprefix tailTrace_5634559
  have hstable : (prefixWord ++ tailWord_5634559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634559).length < 2 ^ (prefixWord ++ tailWord_5634559).sum := by decide
  have hdescent : baseEnd_5634559 < baseStart_5634559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_5634575 : Nat := 118140960795 + 5634575 * 2 ^ 59
def prefixEnd_5634575 : Nat := 4983230072969 + 3 ^ 40 * 5634575 * 2
def baseEnd_5634575 : Nat := 2893245258807397433099567

theorem tailTrace_5634575 : CollatzResearch.WordTrace tailWord_5634575 prefixEnd_5634575 2893245258807397433099567 := by
  unfold tailWord_5634575
  simp only [CollatzResearch.WordTrace]
  refine ⟨205509833561904558641793179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137006555707936372427862119 205509833561904558641793179)
  ·
    refine ⟨308264750342856837962689769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205509833561904558641793179 308264750342856837962689769)
    ·
      refine ⟨231198562757142628472017327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308264750342856837962689769 231198562757142628472017327)
      ·
        refine ⟨346797844135713942708025991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231198562757142628472017327 346797844135713942708025991)
        ·
          refine ⟨520196766203570914062038987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346797844135713942708025991 520196766203570914062038987)
          ·
            refine ⟨780295149305356371093058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520196766203570914062038987 780295149305356371093058481)
            ·
              refine ⟨585221361979017278319793861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780295149305356371093058481 585221361979017278319793861)
              ·
                refine ⟨109729005371065739684961349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585221361979017278319793861 109729005371065739684961349)
                ·
                  refine ⟨20574188507074826190930253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109729005371065739684961349 20574188507074826190930253)
                  ·
                    refine ⟨7715320690153059821598845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20574188507074826190930253 7715320690153059821598845)
                    ·
                      refine ⟨2893245258807397433099567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715320690153059821598845 2893245258807397433099567)
                      ·
                        rfl

theorem cell23_5634575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_5634575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634575 prefixEnd_5634575 := by exact prefixLift 5634575
  have htrace : WordTrace (prefixWord ++ tailWord_5634575) baseStart_5634575 baseEnd_5634575 := by
    simpa [prefixWord, tailWord_5634575, baseEnd_5634575] using wordTrace_append hprefix tailTrace_5634575
  have hstable : (prefixWord ++ tailWord_5634575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634575).length < 2 ^ (prefixWord ++ tailWord_5634575).sum := by decide
  have hdescent : baseEnd_5634575 < baseStart_5634575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634580 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5634580 : Nat := 118140960795 + 5634580 * 2 ^ 59
def prefixEnd_5634580 : Nat := 4983230072969 + 3 ^ 40 * 5634580 * 2
def baseEnd_5634580 : Nat := 2893247826210669913537045

theorem tailTrace_5634580 : CollatzResearch.WordTrace tailWord_5634580 prefixEnd_5634580 2893247826210669913537045 := by
  unfold tailWord_5634580
  simp only [CollatzResearch.WordTrace]
  refine ⟨102755007963443222247862597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137006677284590962997150129 102755007963443222247862597)
  ·
    refine ⟨19266563993145604171474237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102755007963443222247862597 19266563993145604171474237)
    ·
      refine ⟨7224961497429601564302839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19266563993145604171474237 7224961497429601564302839)
      ·
        refine ⟨10837442246144402346454259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7224961497429601564302839 10837442246144402346454259)
        ·
          refine ⟨16256163369216603519681389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10837442246144402346454259 16256163369216603519681389)
          ·
            refine ⟨6096061263456226319880521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16256163369216603519681389 6096061263456226319880521)
            ·
              refine ⟨4572045947592169739910391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6096061263456226319880521 4572045947592169739910391)
              ·
                refine ⟨6858068921388254609865587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4572045947592169739910391 6858068921388254609865587)
                ·
                  refine ⟨10287103382082381914798381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858068921388254609865587 10287103382082381914798381)
                  ·
                    refine ⟨3857663768280893218049393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10287103382082381914798381 3857663768280893218049393)
                    ·
                      refine ⟨2893247826210669913537045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857663768280893218049393 2893247826210669913537045)
                      ·
                        rfl

theorem cell23_5634580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5634580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634580 prefixEnd_5634580 := by exact prefixLift 5634580
  have htrace : WordTrace (prefixWord ++ tailWord_5634580) baseStart_5634580 baseEnd_5634580 := by
    simpa [prefixWord, tailWord_5634580, baseEnd_5634580] using wordTrace_append hprefix tailTrace_5634580
  have hstable : (prefixWord ++ tailWord_5634580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634580).length < 2 ^ (prefixWord ++ tailWord_5634580).sum := by decide
  have hdescent : baseEnd_5634580 < baseStart_5634580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634615 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_5634615 : Nat := 118140960795 + 5634615 * 2 ^ 59
def prefixEnd_5634615 : Nat := 4983230072969 + 3 ^ 40 * 5634615 * 2
def baseEnd_5634615 : Nat := 2893265798033577276599383

theorem tailTrace_5634615 : CollatzResearch.WordTrace tailWord_5634615 prefixEnd_5634615 2893265798033577276599383 := by
  unfold tailWord_5634615
  simp only [CollatzResearch.WordTrace]
  refine ⟨205511292481759645473249299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137007528321173096982166199 205511292481759645473249299)
  ·
    refine ⟨308266938722639468209873949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205511292481759645473249299 308266938722639468209873949)
    ·
      refine ⟨115600102020989800578702731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308266938722639468209873949 115600102020989800578702731)
      ·
        refine ⟨173400153031484700868054097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115600102020989800578702731 173400153031484700868054097)
        ·
          refine ⟨130050114773613525651040573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173400153031484700868054097 130050114773613525651040573)
          ·
            refine ⟨48768793040105072119140215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130050114773613525651040573 48768793040105072119140215)
            ·
              refine ⟨73153189560157608178710323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48768793040105072119140215 73153189560157608178710323)
              ·
                refine ⟨109729784340236412268065485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73153189560157608178710323 109729784340236412268065485)
                ·
                  refine ⟨41148669127588654600524557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109729784340236412268065485 41148669127588654600524557)
                  ·
                    refine ⟨15430750922845745475196709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41148669127588654600524557 15430750922845745475196709)
                    ·
                      refine ⟨2893265798033577276599383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15430750922845745475196709 2893265798033577276599383)
                      ·
                        rfl

theorem cell23_5634615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_5634615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634615 prefixEnd_5634615 := by exact prefixLift 5634615
  have htrace : WordTrace (prefixWord ++ tailWord_5634615) baseStart_5634615 baseEnd_5634615 := by
    simpa [prefixWord, tailWord_5634615, baseEnd_5634615] using wordTrace_append hprefix tailTrace_5634615
  have hstable : (prefixWord ++ tailWord_5634615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634615).length < 2 ^ (prefixWord ++ tailWord_5634615).sum := by decide
  have hdescent : baseEnd_5634615 < baseStart_5634615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634632 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_5634632 : Nat := 118140960795 + 5634632 * 2 ^ 59
def prefixEnd_5634632 : Nat := 4983230072969 + 3 ^ 40 * 5634632 * 2
def baseEnd_5634632 : Nat := 2893274527204703710086805

theorem tailTrace_5634632 : CollatzResearch.WordTrace tailWord_5634632 prefixEnd_5634632 2893274527204703710086805 := by
  unfold tailWord_5634632
  simp only [CollatzResearch.WordTrace]
  refine ⟨102755956261349028688309075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137007941681798704917745433 102755956261349028688309075)
  ·
    refine ⟨154133934392023543032463613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102755956261349028688309075 154133934392023543032463613)
    ·
      refine ⟨57800225397008828637173855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154133934392023543032463613 57800225397008828637173855)
      ·
        refine ⟨86700338095513242955760783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57800225397008828637173855 86700338095513242955760783)
        ·
          refine ⟨130050507143269864433641175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86700338095513242955760783 130050507143269864433641175)
          ·
            refine ⟨195075760714904796650461763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130050507143269864433641175 195075760714904796650461763)
            ·
              refine ⟨292613641072357194975692645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195075760714904796650461763 292613641072357194975692645)
              ·
                refine ⟨54865057701066974057942371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292613641072357194975692645 54865057701066974057942371)
                ·
                  refine ⟨82297586551600461086913557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54865057701066974057942371 82297586551600461086913557)
                  ·
                    refine ⟨3857699369606271613449073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82297586551600461086913557 3857699369606271613449073)
                    ·
                      refine ⟨2893274527204703710086805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857699369606271613449073 2893274527204703710086805)
                      ·
                        rfl

theorem cell23_5634632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_5634632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634632 prefixEnd_5634632 := by exact prefixLift 5634632
  have htrace : WordTrace (prefixWord ++ tailWord_5634632) baseStart_5634632 baseEnd_5634632 := by
    simpa [prefixWord, tailWord_5634632, baseEnd_5634632] using wordTrace_append hprefix tailTrace_5634632
  have hstable : (prefixWord ++ tailWord_5634632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634632).length < 2 ^ (prefixWord ++ tailWord_5634632).sum := by decide
  have hdescent : baseEnd_5634632 < baseStart_5634632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634645 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5634645 : Nat := 118140960795 + 5634645 * 2 ^ 59
def prefixEnd_5634645 : Nat := 4983230072969 + 3 ^ 40 * 5634645 * 2
def baseEnd_5634645 : Nat := 2893281202453212159224245

theorem tailTrace_5634645 : CollatzResearch.WordTrace tailWord_5634645 prefixEnd_5634645 2893281202453212159224245 := by
  unfold tailWord_5634645
  simp only [CollatzResearch.WordTrace]
  refine ⟨205512386671650960596841389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137008257781100640397894259 205512386671650960596841389)
  ·
    refine ⟨77067145001869110223815521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205512386671650960596841389 77067145001869110223815521)
    ·
      refine ⟨57800358751401832667861641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77067145001869110223815521 57800358751401832667861641)
      ·
        refine ⟨43350269063551374500896231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57800358751401832667861641 43350269063551374500896231)
        ·
          refine ⟨65025403595327061751344347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43350269063551374500896231 65025403595327061751344347)
          ·
            refine ⟨97538105392990592627016521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65025403595327061751344347 97538105392990592627016521)
            ·
              refine ⟨73153579044742944470262391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97538105392990592627016521 73153579044742944470262391)
              ·
                refine ⟨109730368567114416705393587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73153579044742944470262391 109730368567114416705393587)
                ·
                  refine ⟨164595552850671625058090381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109730368567114416705393587 164595552850671625058090381)
                  ·
                    refine ⟨61723332319001859396783893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164595552850671625058090381 61723332319001859396783893)
                    ·
                      refine ⟨2893281202453212159224245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61723332319001859396783893 2893281202453212159224245)
                      ·
                        rfl

theorem cell23_5634645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5634645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634645 prefixEnd_5634645 := by exact prefixLift 5634645
  have htrace : WordTrace (prefixWord ++ tailWord_5634645) baseStart_5634645 baseEnd_5634645 := by
    simpa [prefixWord, tailWord_5634645, baseEnd_5634645] using wordTrace_append hprefix tailTrace_5634645
  have hstable : (prefixWord ++ tailWord_5634645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634645).length < 2 ^ (prefixWord ++ tailWord_5634645).sum := by decide
  have hdescent : baseEnd_5634645 < baseStart_5634645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634743 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_5634743 : Nat := 118140960795 + 5634743 * 2 ^ 59
def prefixEnd_5634743 : Nat := 4983230072969 + 3 ^ 40 * 5634743 * 2
def baseEnd_5634743 : Nat := 2893331523557352775798795

theorem tailTrace_5634743 : CollatzResearch.WordTrace tailWord_5634743 prefixEnd_5634743 2893331523557352775798795 := by
  unfold tailWord_5634743
  simp only [CollatzResearch.WordTrace]
  refine ⟨205515961025295923333908883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137010640683530615555939255 205515961025295923333908883)
  ·
    refine ⟨308273941537943885000863325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205515961025295923333908883 308273941537943885000863325)
    ·
      refine ⟨115602728076728956875323747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308273941537943885000863325 115602728076728956875323747)
      ·
        refine ⟨173404092115093435312985621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115602728076728956875323747 173404092115093435312985621)
        ·
          refine ⟨8128316817895004780296201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173404092115093435312985621 8128316817895004780296201)
          ·
            refine ⟨6096237613421253585222151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8128316817895004780296201 6096237613421253585222151)
            ·
              refine ⟨9144356420131880377833227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096237613421253585222151 9144356420131880377833227)
              ·
                refine ⟨13716534630197820566749841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144356420131880377833227 13716534630197820566749841)
                ·
                  refine ⟨10287400972648365425062381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13716534630197820566749841 10287400972648365425062381)
                  ·
                    refine ⟨3857775364743137034398393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10287400972648365425062381 3857775364743137034398393)
                    ·
                      refine ⟨2893331523557352775798795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857775364743137034398393 2893331523557352775798795)
                      ·
                        rfl

theorem cell23_5634743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_5634743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634743 prefixEnd_5634743 := by exact prefixLift 5634743
  have htrace : WordTrace (prefixWord ++ tailWord_5634743) baseStart_5634743 baseEnd_5634743 := by
    simpa [prefixWord, tailWord_5634743, baseEnd_5634743] using wordTrace_append hprefix tailTrace_5634743
  have hstable : (prefixWord ++ tailWord_5634743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634743).length < 2 ^ (prefixWord ++ tailWord_5634743).sum := by decide
  have hdescent : baseEnd_5634743 < baseStart_5634743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634753 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_5634753 : Nat := 118140960795 + 5634753 * 2 ^ 59
def prefixEnd_5634753 : Nat := 4983230072969 + 3 ^ 40 * 5634753 * 2
def baseEnd_5634753 : Nat := 964445552787965912224583

theorem tailTrace_5634753 : CollatzResearch.WordTrace tailWord_5634753 prefixEnd_5634753 964445552787965912224583 := by
  unfold tailWord_5634753
  simp only [CollatzResearch.WordTrace]
  refine ⟨205516325755259695041772913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137010883836839796694515275 205516325755259695041772913)
  ·
    refine ⟨154137244316444771281329685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205516325755259695041772913 154137244316444771281329685)
    ·
      refine ⟨7225183327333348653812329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154137244316444771281329685 7225183327333348653812329)
      ·
        refine ⟨5418887495500011490359247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7225183327333348653812329 5418887495500011490359247)
        ·
          refine ⟨8128331243250017235538871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418887495500011490359247 8128331243250017235538871)
          ·
            refine ⟨12192496864875025853308307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8128331243250017235538871 12192496864875025853308307)
            ·
              refine ⟨18288745297312538779962461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12192496864875025853308307 18288745297312538779962461)
              ·
                refine ⟨6858279486492202042485923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18288745297312538779962461 6858279486492202042485923)
                ·
                  refine ⟨10287419229738303063728885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858279486492202042485923 10287419229738303063728885)
                  ·
                    refine ⟨964445552787965912224583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10287419229738303063728885 964445552787965912224583)
                    ·
                      rfl

theorem cell23_5634753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_5634753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634753 prefixEnd_5634753 := by exact prefixLift 5634753
  have htrace : WordTrace (prefixWord ++ tailWord_5634753) baseStart_5634753 baseEnd_5634753 := by
    simpa [prefixWord, tailWord_5634753, baseEnd_5634753] using wordTrace_append hprefix tailTrace_5634753
  have hstable : (prefixWord ++ tailWord_5634753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634753).length < 2 ^ (prefixWord ++ tailWord_5634753).sum := by decide
  have hdescent : baseEnd_5634753 < baseStart_5634753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634756 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_5634756 : Nat := 118140960795 + 5634756 * 2 ^ 59
def prefixEnd_5634756 : Nat := 4983230072969 + 3 ^ 40 * 5634756 * 2
def baseEnd_5634756 : Nat := 2893338198805861224936235

theorem tailTrace_5634756 : CollatzResearch.WordTrace tailWord_5634756 prefixEnd_5634756 2893338198805861224936235 := by
  unfold tailWord_5634756
  simp only [CollatzResearch.WordTrace]
  refine ⟨102758217587124413277066061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137010956782832551036088081 102758217587124413277066061)
  ·
    refine ⟨38534331595171654978899773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102758217587124413277066061 38534331595171654978899773)
    ·
      refine ⟨14450374348189370617087415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38534331595171654978899773 14450374348189370617087415)
      ·
        refine ⟨21675561522284055925631123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14450374348189370617087415 21675561522284055925631123)
        ·
          refine ⟨32513342283426083888446685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21675561522284055925631123 32513342283426083888446685)
          ·
            refine ⟨12192503356284781458167507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32513342283426083888446685 12192503356284781458167507)
            ·
              refine ⟨18288755034427172187251261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12192503356284781458167507 18288755034427172187251261)
              ·
                refine ⟨6858283137910189570219223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18288755034427172187251261 6858283137910189570219223)
                ·
                  refine ⟨10287424706865284355328835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858283137910189570219223 10287424706865284355328835)
                  ·
                    refine ⟨15431137060297926532993253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10287424706865284355328835 15431137060297926532993253)
                    ·
                      refine ⟨2893338198805861224936235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15431137060297926532993253 2893338198805861224936235)
                      ·
                        rfl

theorem cell23_5634756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_5634756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634756 prefixEnd_5634756 := by exact prefixLift 5634756
  have htrace : WordTrace (prefixWord ++ tailWord_5634756) baseStart_5634756 baseEnd_5634756 := by
    simpa [prefixWord, tailWord_5634756, baseEnd_5634756] using wordTrace_append hprefix tailTrace_5634756
  have hstable : (prefixWord ++ tailWord_5634756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634756).length < 2 ^ (prefixWord ++ tailWord_5634756).sum := by decide
  have hdescent : baseEnd_5634756 < baseStart_5634756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634762 : List Nat := [3, 1, 2, 1, 4, 2, 10]
def baseStart_5634762 : Nat := 118140960795 + 5634762 * 2 ^ 59
def prefixEnd_5634762 : Nat := 4983230072969 + 3 ^ 40 * 5634762 * 2
def baseEnd_5634762 : Nat := 35720262712219607425447

theorem tailTrace_5634762 : CollatzResearch.WordTrace tailWord_5634762 prefixEnd_5634762 35720262712219607425447 := by
  unfold tailWord_5634762
  simp only [CollatzResearch.WordTrace]
  refine ⟨51379163503056772394712635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137011102674818059719233693 51379163503056772394712635)
  ·
    refine ⟨77068745254585158592068953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51379163503056772394712635 77068745254585158592068953)
    ·
      refine ⟨57801558940938868944051715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77068745254585158592068953 57801558940938868944051715)
      ·
        refine ⟨86702338411408303416077573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57801558940938868944051715 86702338411408303416077573)
        ·
          refine ⟨16256688452139056890514545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86702338411408303416077573 16256688452139056890514545)
          ·
            refine ⟨12192516339104292667885909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16256688452139056890514545 12192516339104292667885909)
            ·
              refine ⟨35720262712219607425447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12192516339104292667885909 35720262712219607425447)
              ·
                rfl

theorem cell23_5634762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 10].length) (baseStart_5634762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634762 prefixEnd_5634762 := by exact prefixLift 5634762
  have htrace : WordTrace (prefixWord ++ tailWord_5634762) baseStart_5634762 baseEnd_5634762 := by
    simpa [prefixWord, tailWord_5634762, baseEnd_5634762] using wordTrace_append hprefix tailTrace_5634762
  have hstable : (prefixWord ++ tailWord_5634762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634762).length < 2 ^ (prefixWord ++ tailWord_5634762).sum := by decide
  have hdescent : baseEnd_5634762 < baseStart_5634762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634766 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_5634766 : Nat := 118140960795 + 5634766 * 2 ^ 59
def prefixEnd_5634766 : Nat := 4983230072969 + 3 ^ 40 * 5634766 * 2
def baseEnd_5634766 : Nat := 964447777870802061937063

theorem tailTrace_5634766 : CollatzResearch.WordTrace tailWord_5634766 prefixEnd_5634766 964447777870802061937063 := by
  unfold tailWord_5634766
  simp only [CollatzResearch.WordTrace]
  refine ⟨25689599988026574782749519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137011199936141732174664101 25689599988026574782749519)
  ·
    refine ⟨38534399982039862174124279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25689599988026574782749519 38534399982039862174124279)
    ·
      refine ⟨57801599973059793261186419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38534399982039862174124279 57801599973059793261186419)
      ·
        refine ⟨86702399959589689891779629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57801599973059793261186419 86702399959589689891779629)
        ·
          refine ⟨32513399984846133709417361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86702399959589689891779629 32513399984846133709417361)
          ·
            refine ⟨24385049988634600282063021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32513399984846133709417361 24385049988634600282063021)
            ·
              refine ⟨9144393745737975105773633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24385049988634600282063021 9144393745737975105773633)
              ·
                refine ⟨6858295309303481329330225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144393745737975105773633 6858295309303481329330225)
                ·
                  refine ⟨5143721481977610996997669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6858295309303481329330225 5143721481977610996997669)
                  ·
                    refine ⟨964447777870802061937063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5143721481977610996997669 964447777870802061937063)
                    ·
                      rfl

theorem cell23_5634766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_5634766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634766 prefixEnd_5634766 := by exact prefixLift 5634766
  have htrace : WordTrace (prefixWord ++ tailWord_5634766) baseStart_5634766 baseEnd_5634766 := by
    simpa [prefixWord, tailWord_5634766, baseEnd_5634766] using wordTrace_append hprefix tailTrace_5634766
  have hstable : (prefixWord ++ tailWord_5634766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634766).length < 2 ^ (prefixWord ++ tailWord_5634766).sum := by decide
  have hdescent : baseEnd_5634766 < baseStart_5634766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634806 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5634806 : Nat := 118140960795 + 5634806 * 2 ^ 59
def prefixEnd_5634806 : Nat := 4983230072969 + 3 ^ 40 * 5634806 * 2
def baseEnd_5634806 : Nat := 2893363872838586029311005

theorem tailTrace_5634806 : CollatzResearch.WordTrace tailWord_5634806 prefixEnd_5634806 2893363872838586029311005 := by
  unfold tailWord_5634806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12844891176504230318340767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137012172549378456728968181 12844891176504230318340767)
  ·
    refine ⟨19267336764756345477511151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12844891176504230318340767 19267336764756345477511151)
    ·
      refine ⟨28901005147134518216266727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19267336764756345477511151 28901005147134518216266727)
      ·
        refine ⟨43351507720701777324400091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28901005147134518216266727 43351507720701777324400091)
        ·
          refine ⟨65027261581052665986600137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43351507720701777324400091 65027261581052665986600137)
          ·
            refine ⟨48770446185789499489950103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65027261581052665986600137 48770446185789499489950103)
            ·
              refine ⟨73155669278684249234925155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48770446185789499489950103 73155669278684249234925155)
              ·
                refine ⟨109733503918026373852387733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73155669278684249234925155 109733503918026373852387733)
                ·
                  refine ⟨5143757996157486274330675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109733503918026373852387733 5143757996157486274330675)
                  ·
                    refine ⟨7715636994236229411496013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5143757996157486274330675 7715636994236229411496013)
                    ·
                      refine ⟨2893363872838586029311005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715636994236229411496013 2893363872838586029311005)
                      ·
                        rfl

theorem cell23_5634806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5634806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634806 prefixEnd_5634806 := by exact prefixLift 5634806
  have htrace : WordTrace (prefixWord ++ tailWord_5634806) baseStart_5634806 baseEnd_5634806 := by
    simpa [prefixWord, tailWord_5634806, baseEnd_5634806] using wordTrace_append hprefix tailTrace_5634806
  have hstable : (prefixWord ++ tailWord_5634806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634806).length < 2 ^ (prefixWord ++ tailWord_5634806).sum := by decide
  have hdescent : baseEnd_5634806 < baseStart_5634806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634850 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_5634850 : Nat := 118140960795 + 5634850 * 2 ^ 59
def prefixEnd_5634850 : Nat := 4983230072969 + 3 ^ 40 * 5634850 * 2
def baseEnd_5634850 : Nat := 2893386465987383857160803

theorem tailTrace_5634850 : CollatzResearch.WordTrace tailWord_5634850 prefixEnd_5634850 2893386465987383857160803 := by
  unfold tailWord_5634850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51379965908977070152013501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137013242423938853738702669 51379965908977070152013501)
  ·
    refine ⟨19267487215866401307005063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51379965908977070152013501 19267487215866401307005063)
    ·
      refine ⟨28901230823799601960507595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19267487215866401307005063 28901230823799601960507595)
      ·
        refine ⟨43351846235699402940761393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28901230823799601960507595 43351846235699402940761393)
        ·
          refine ⟨32513884676774552205571045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43351846235699402940761393 32513884676774552205571045)
          ·
            refine ⟨6096353376895228538544571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32513884676774552205571045 6096353376895228538544571)
            ·
              refine ⟨9144530065342842807816857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096353376895228538544571 9144530065342842807816857)
              ·
                refine ⟨6858397549007132105862643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144530065342842807816857 6858397549007132105862643)
                ·
                  refine ⟨10287596323510698158793965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858397549007132105862643 10287596323510698158793965)
                  ·
                    refine ⟨3857848621316511809547737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10287596323510698158793965 3857848621316511809547737)
                    ·
                      refine ⟨2893386465987383857160803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3857848621316511809547737 2893386465987383857160803)
                      ·
                        rfl

theorem cell23_5634850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_5634850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634850 prefixEnd_5634850 := by exact prefixLift 5634850
  have htrace : WordTrace (prefixWord ++ tailWord_5634850) baseStart_5634850 baseEnd_5634850 := by
    simpa [prefixWord, tailWord_5634850, baseEnd_5634850] using wordTrace_append hprefix tailTrace_5634850
  have hstable : (prefixWord ++ tailWord_5634850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634850).length < 2 ^ (prefixWord ++ tailWord_5634850).sum := by decide
  have hdescent : baseEnd_5634850 < baseStart_5634850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634893 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5634893 : Nat := 118140960795 + 5634893 * 2 ^ 59
def prefixEnd_5634893 : Nat := 4983230072969 + 3 ^ 40 * 5634893 * 2
def baseEnd_5634893 : Nat := 2893408545655527188923105

theorem tailTrace_5634893 : CollatzResearch.WordTrace tailWord_5634893 prefixEnd_5634893 2893408545655527188923105 := by
  unfold tailWord_5634893
  simp only [CollatzResearch.WordTrace]
  refine ⟨205521431974752498951869333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137014287983168332634579555 205521431974752498951869333)
  ·
    refine ⟨9633817123816523388368875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205521431974752498951869333 9633817123816523388368875)
    ·
      refine ⟨14450725685724785082553313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9633817123816523388368875 14450725685724785082553313)
      ·
        refine ⟨10838044264293588811914985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14450725685724785082553313 10838044264293588811914985)
        ·
          refine ⟨8128533198220191608936239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10838044264293588811914985 8128533198220191608936239)
          ·
            refine ⟨12192799797330287413404359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8128533198220191608936239 12192799797330287413404359)
            ·
              refine ⟨18289199695995431120106539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12192799797330287413404359 18289199695995431120106539)
              ·
                refine ⟨27433799543993146680159809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18289199695995431120106539 27433799543993146680159809)
                ·
                  refine ⟨20575349657994860010119857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27433799543993146680159809 20575349657994860010119857)
                  ·
                    refine ⟨15431512243496145007589893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20575349657994860010119857 15431512243496145007589893)
                    ·
                      refine ⟨2893408545655527188923105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15431512243496145007589893 2893408545655527188923105)
                      ·
                        rfl

theorem cell23_5634893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5634893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634893 prefixEnd_5634893 := by exact prefixLift 5634893
  have htrace : WordTrace (prefixWord ++ tailWord_5634893) baseStart_5634893 baseEnd_5634893 := by
    simpa [prefixWord, tailWord_5634893, baseEnd_5634893] using wordTrace_append hprefix tailTrace_5634893
  have hstable : (prefixWord ++ tailWord_5634893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634893).length < 2 ^ (prefixWord ++ tailWord_5634893).sum := by decide
  have hdescent : baseEnd_5634893 < baseStart_5634893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634916 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_5634916 : Nat := 118140960795 + 5634916 * 2 ^ 59
def prefixEnd_5634916 : Nat := 4983230072969 + 3 ^ 40 * 5634916 * 2
def baseEnd_5634916 : Nat := 964473451903526866311833

theorem tailTrace_5634916 : CollatzResearch.WordTrace tailWord_5634916 prefixEnd_5634916 964473451903526866311833 := by
  unfold tailWord_5634916
  simp only [CollatzResearch.WordTrace]
  refine ⟨102761135426834586939978301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137014847235779449253304401 102761135426834586939978301)
  ·
    refine ⟨38535425785062970102491863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102761135426834586939978301 38535425785062970102491863)
    ·
      refine ⟨57803138677594455153737795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38535425785062970102491863 57803138677594455153737795)
      ·
        refine ⟨86704708016391682730606693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57803138677594455153737795 86704708016391682730606693)
        ·
          refine ⟨16257132753073440511988755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86704708016391682730606693 16257132753073440511988755)
          ·
            refine ⟨24385699129610160767983133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16257132753073440511988755 24385699129610160767983133)
            ·
              refine ⟨9144637173603810287993675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24385699129610160767983133 9144637173603810287993675)
              ·
                refine ⟨13716955760405715431990513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144637173603810287993675 13716955760405715431990513)
                ·
                  refine ⟨10287716820304286573992885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13716955760405715431990513 10287716820304286573992885)
                  ·
                    refine ⟨964473451903526866311833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10287716820304286573992885 964473451903526866311833)
                    ·
                      rfl

theorem cell23_5634916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_5634916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634916 prefixEnd_5634916 := by exact prefixLift 5634916
  have htrace : WordTrace (prefixWord ++ tailWord_5634916) baseStart_5634916 baseEnd_5634916 := by
    simpa [prefixWord, tailWord_5634916, baseEnd_5634916] using wordTrace_append hprefix tailTrace_5634916
  have hstable : (prefixWord ++ tailWord_5634916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634916).length < 2 ^ (prefixWord ++ tailWord_5634916).sum := by decide
  have hdescent : baseEnd_5634916 < baseStart_5634916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5634969 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_5634969 : Nat := 118140960795 + 5634969 * 2 ^ 59
def prefixEnd_5634969 : Nat := 4983230072969 + 3 ^ 40 * 5634969 * 2
def baseEnd_5634969 : Nat := 2893447570185268891572755

theorem tailTrace_5634969 : CollatzResearch.WordTrace tailWord_5634969 prefixEnd_5634969 2893447570185268891572755 := by
  unfold tailWord_5634969
  simp only [CollatzResearch.WordTrace]
  refine ⟨205524203922477163931635961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137016135948318109287757307 205524203922477163931635961)
  ·
    refine ⟨154143152941857872948726971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205524203922477163931635961 154143152941857872948726971)
    ·
      refine ⟨231214729412786809423090457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154143152941857872948726971 231214729412786809423090457)
      ·
        refine ⟨173411047059590107067317843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231214729412786809423090457 173411047059590107067317843)
        ·
          refine ⟨260116570589385160600976765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173411047059590107067317843 260116570589385160600976765)
          ·
            refine ⟨97543713971019435225366287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260116570589385160600976765 97543713971019435225366287)
            ·
              refine ⟨146315570956529152838049431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97543713971019435225366287 146315570956529152838049431)
              ·
                refine ⟨219473356434793729257074147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146315570956529152838049431 219473356434793729257074147)
                ·
                  refine ⟨329210034652190593885611221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219473356434793729257074147 329210034652190593885611221)
                  ·
                    refine ⟨7715860187160717044194013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 329210034652190593885611221 7715860187160717044194013)
                    ·
                      refine ⟨2893447570185268891572755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7715860187160717044194013 2893447570185268891572755)
                      ·
                        rfl

theorem cell23_5634969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_5634969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5634969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5634969 prefixEnd_5634969 := by exact prefixLift 5634969
  have htrace : WordTrace (prefixWord ++ tailWord_5634969) baseStart_5634969 baseEnd_5634969 := by
    simpa [prefixWord, tailWord_5634969, baseEnd_5634969] using wordTrace_append hprefix tailTrace_5634969
  have hstable : (prefixWord ++ tailWord_5634969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5634969).length < 2 ^ (prefixWord ++ tailWord_5634969).sum := by decide
  have hdescent : baseEnd_5634969 < baseStart_5634969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5634969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635006 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_5635006 : Nat := 118140960795 + 5635006 * 2 ^ 59
def prefixEnd_5635006 : Nat := 4983230072969 + 3 ^ 40 * 5635006 * 2
def baseEnd_5635006 : Nat := 964488856323161748936695

theorem tailTrace_5635006 : CollatzResearch.WordTrace tailWord_5635006 prefixEnd_5635006 964488856323161748936695 := by
  unfold tailWord_5635006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25690694177917889906341609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137017035615562079500488581 25690694177917889906341609)
  ·
    refine ⟨19268020633438417429756207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25690694177917889906341609 19268020633438417429756207)
    ·
      refine ⟨28902030950157626144634311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19268020633438417429756207 28902030950157626144634311)
      ·
        refine ⟨43353046425236439216951467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28902030950157626144634311 43353046425236439216951467)
        ·
          refine ⟨65029569637854658825427201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43353046425236439216951467 65029569637854658825427201)
          ·
            refine ⟨48772177228390994119070401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65029569637854658825427201 48772177228390994119070401)
            ·
              refine ⟨36579132921293245589302801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48772177228390994119070401 36579132921293245589302801)
              ·
                refine ⟨27434349690969934191977101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36579132921293245589302801 27434349690969934191977101)
                ·
                  refine ⟨10287881134113725321991413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27434349690969934191977101 10287881134113725321991413)
                  ·
                    refine ⟨964488856323161748936695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10287881134113725321991413 964488856323161748936695)
                    ·
                      rfl

theorem cell23_5635006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_5635006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635006 prefixEnd_5635006 := by exact prefixLift 5635006
  have htrace : WordTrace (prefixWord ++ tailWord_5635006) baseStart_5635006 baseEnd_5635006 := by
    simpa [prefixWord, tailWord_5635006, baseEnd_5635006] using wordTrace_append hprefix tailTrace_5635006
  have hstable : (prefixWord ++ tailWord_5635006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635006).length < 2 ^ (prefixWord ++ tailWord_5635006).sum := by decide
  have hdescent : baseEnd_5635006 < baseStart_5635006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635023 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 1, 5]
def baseStart_5635023 : Nat := 118140960795 + 5635023 * 2 ^ 59
def prefixEnd_5635023 : Nat := 4983230072969 + 3 ^ 40 * 5635023 * 2
def baseEnd_5635023 : Nat := 964491766046870560099169

theorem tailTrace_5635023 : CollatzResearch.WordTrace tailWord_5635023 prefixEnd_5635023 964491766046870560099169 := by
  unfold tailWord_5635023
  simp only [CollatzResearch.WordTrace]
  refine ⟨205526173464281531154101723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137017448976187687436067815 205526173464281531154101723)
  ·
    refine ⟨308289260196422296731152585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205526173464281531154101723 308289260196422296731152585)
    ·
      refine ⟨231216945147316722548364439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308289260196422296731152585 231216945147316722548364439)
      ·
        refine ⟨346825417720975083822546659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231216945147316722548364439 346825417720975083822546659)
        ·
          refine ⟨520238126581462625733819989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346825417720975083822546659 520238126581462625733819989)
          ·
            refine ⟨6096540545876515145318203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 520238126581462625733819989 6096540545876515145318203)
            ·
              refine ⟨9144810818814772717977305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096540545876515145318203 9144810818814772717977305)
              ·
                refine ⟨6858608114111079538482979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144810818814772717977305 6858608114111079538482979)
                ·
                  refine ⟨10287912171166619307724469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858608114111079538482979 10287912171166619307724469)
                  ·
                    refine ⟨964491766046870560099169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10287912171166619307724469 964491766046870560099169)
                    ·
                      rfl

theorem cell23_5635023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_5635023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635023 prefixEnd_5635023 := by exact prefixLift 5635023
  have htrace : WordTrace (prefixWord ++ tailWord_5635023) baseStart_5635023 baseEnd_5635023 := by
    simpa [prefixWord, tailWord_5635023, baseEnd_5635023] using wordTrace_append hprefix tailTrace_5635023
  have hstable : (prefixWord ++ tailWord_5635023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635023).length < 2 ^ (prefixWord ++ tailWord_5635023).sum := by decide
  have hdescent : baseEnd_5635023 < baseStart_5635023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635070 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5635070 : Nat := 118140960795 + 5635070 * 2 ^ 59
def prefixEnd_5635070 : Nat := 4983230072969 + 3 ^ 40 * 5635070 * 2
def baseEnd_5635070 : Nat := 964499810577124332136597

theorem tailTrace_5635070 : CollatzResearch.WordTrace tailWord_5635070 prefixEnd_5635070 964499810577124332136597 := by
  unfold tailWord_5635070
  simp only [CollatzResearch.WordTrace]
  refine ⟨25690985961888907272632833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137018591796740838787375109 25690985961888907272632833)
  ·
    refine ⟨19268239471416680454474625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25690985961888907272632833 19268239471416680454474625)
    ·
      refine ⟨14451179603562510340855969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19268239471416680454474625 14451179603562510340855969)
      ·
        refine ⟨10838384702671882755641977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14451179603562510340855969 10838384702671882755641977)
        ·
          refine ⟨8128788527003912066731483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10838384702671882755641977 8128788527003912066731483)
          ·
            refine ⟨12193182790505868100097225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8128788527003912066731483 12193182790505868100097225)
            ·
              refine ⟨9144887092879401075072919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12193182790505868100097225 9144887092879401075072919)
              ·
                refine ⟨13717330639319101612609379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144887092879401075072919 13717330639319101612609379)
                ·
                  refine ⟨20575995958978652418914069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13717330639319101612609379 20575995958978652418914069)
                  ·
                    refine ⟨964499810577124332136597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20575995958978652418914069 964499810577124332136597)
                    ·
                      rfl

theorem cell23_5635070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5635070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635070 prefixEnd_5635070 := by exact prefixLift 5635070
  have htrace : WordTrace (prefixWord ++ tailWord_5635070) baseStart_5635070 baseEnd_5635070 := by
    simpa [prefixWord, tailWord_5635070, baseEnd_5635070] using wordTrace_append hprefix tailTrace_5635070
  have hstable : (prefixWord ++ tailWord_5635070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635070).length < 2 ^ (prefixWord ++ tailWord_5635070).sum := by decide
  have hdescent : baseEnd_5635070 < baseStart_5635070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635073 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_5635073 : Nat := 118140960795 + 5635073 * 2 ^ 59
def prefixEnd_5635073 : Nat := 4983230072969 + 3 ^ 40 * 5635073 * 2
def baseEnd_5635073 : Nat := 2893500972173336484672277

theorem tailTrace_5635073 : CollatzResearch.WordTrace tailWord_5635073 prefixEnd_5635073 2893500972173336484672277 := by
  unfold tailWord_5635073
  simp only [CollatzResearch.WordTrace]
  refine ⟨205527997114100389693421873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137018664742733593128947915 205527997114100389693421873)
  ·
    refine ⟨154145997835575292270066405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205527997114100389693421873 154145997835575292270066405)
    ·
      refine ⟨28902374594170367300637451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154145997835575292270066405 28902374594170367300637451)
      ·
        refine ⟨43353561891255550950956177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28902374594170367300637451 43353561891255550950956177)
        ·
          refine ⟨32515171418441663213217133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43353561891255550950956177 32515171418441663213217133)
          ·
            refine ⟨12193189281915623704956425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32515171418441663213217133 12193189281915623704956425)
            ·
              refine ⟨9144891961436717778717319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12193189281915623704956425 9144891961436717778717319)
              ·
                refine ⟨13717337942155076668075979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144891961436717778717319 13717337942155076668075979)
                ·
                  refine ⟨20576006913232615002113969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13717337942155076668075979 20576006913232615002113969)
                  ·
                    refine ⟨15432005184924461251585477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20576006913232615002113969 15432005184924461251585477)
                    ·
                      refine ⟨2893500972173336484672277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15432005184924461251585477 2893500972173336484672277)
                      ·
                        rfl

theorem cell23_5635073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_5635073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635073 prefixEnd_5635073 := by exact prefixLift 5635073
  have htrace : WordTrace (prefixWord ++ tailWord_5635073) baseStart_5635073 baseEnd_5635073 := by
    simpa [prefixWord, tailWord_5635073, baseEnd_5635073] using wordTrace_append hprefix tailTrace_5635073
  have hstable : (prefixWord ++ tailWord_5635073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635073).length < 2 ^ (prefixWord ++ tailWord_5635073).sum := by decide
  have hdescent : baseEnd_5635073 < baseStart_5635073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635093 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_5635093 : Nat := 118140960795 + 5635093 * 2 ^ 59
def prefixEnd_5635093 : Nat := 4983230072969 + 3 ^ 40 * 5635093 * 2
def baseEnd_5635093 : Nat := 2893511241786426406422185

theorem tailTrace_5635093 : CollatzResearch.WordTrace tailWord_5635093 prefixEnd_5635093 2893511241786426406422185 := by
  unfold tailWord_5635093
  simp only [CollatzResearch.WordTrace]
  refine ⟨205528726574027933109149933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137019151049351955406099955 205528726574027933109149933)
  ·
    refine ⟨77073272465260474915931225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205528726574027933109149933 77073272465260474915931225)
    ·
      refine ⟨57804954348945356186948419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77073272465260474915931225 57804954348945356186948419)
      ·
        refine ⟨86707431523418034280422629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57804954348945356186948419 86707431523418034280422629)
        ·
          refine ⟨16257643410640881427579243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86707431523418034280422629 16257643410640881427579243)
          ·
            refine ⟨24386465115961322141368865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16257643410640881427579243 24386465115961322141368865)
            ·
              refine ⟨18289848836970991606026649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24386465115961322141368865 18289848836970991606026649)
              ·
                refine ⟨13717386627728243704519987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18289848836970991606026649 13717386627728243704519987)
                ·
                  refine ⟨20576079941592365556779981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13717386627728243704519987 20576079941592365556779981)
                  ·
                    refine ⟨7716029978097137083792493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20576079941592365556779981 7716029978097137083792493)
                    ·
                      refine ⟨2893511241786426406422185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7716029978097137083792493 2893511241786426406422185)
                      ·
                        rfl

theorem cell23_5635093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_5635093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635093 prefixEnd_5635093 := by exact prefixLift 5635093
  have htrace : WordTrace (prefixWord ++ tailWord_5635093) baseStart_5635093 baseEnd_5635093 := by
    simpa [prefixWord, tailWord_5635093, baseEnd_5635093] using wordTrace_append hprefix tailTrace_5635093
  have hstable : (prefixWord ++ tailWord_5635093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635093).length < 2 ^ (prefixWord ++ tailWord_5635093).sum := by decide
  have hdescent : baseEnd_5635093 < baseStart_5635093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635104 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 2, 4]
def baseStart_5635104 : Nat := 118140960795 + 5635104 * 2 ^ 59
def prefixEnd_5635104 : Nat := 4983230072969 + 3 ^ 40 * 5635104 * 2
def baseEnd_5635104 : Nat := 964505630024541954461545

theorem tailTrace_5635104 : CollatzResearch.WordTrace tailWord_5635104 prefixEnd_5635104 964505630024541954461545 := by
  unfold tailWord_5635104
  simp only [CollatzResearch.WordTrace]
  refine ⟨102764563888494040993900183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137019418517992054658533577 102764563888494040993900183)
  ·
    refine ⟨154146845832741061490850275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102764563888494040993900183 154146845832741061490850275)
    ·
      refine ⟨231220268749111592236275413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154146845832741061490850275 231220268749111592236275413)
      ·
        refine ⟨5419225048807302943037705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 231220268749111592236275413 5419225048807302943037705)
        ·
          refine ⟨4064418786605477207278279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5419225048807302943037705 4064418786605477207278279)
          ·
            refine ⟨6096628179908215810917419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064418786605477207278279 6096628179908215810917419)
            ·
              refine ⟨9144942269862323716376129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096628179908215810917419 9144942269862323716376129)
              ·
                refine ⟨6858706702396742787282097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144942269862323716376129 6858706702396742787282097)
                ·
                  refine ⟨5144030026797557090461573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6858706702396742787282097 5144030026797557090461573)
                  ·
                    refine ⟨964505630024541954461545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144030026797557090461573 964505630024541954461545)
                    ·
                      rfl

theorem cell23_5635104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_5635104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635104 prefixEnd_5635104 := by exact prefixLift 5635104
  have htrace : WordTrace (prefixWord ++ tailWord_5635104) baseStart_5635104 baseEnd_5635104 := by
    simpa [prefixWord, tailWord_5635104, baseEnd_5635104] using wordTrace_append hprefix tailTrace_5635104
  have hstable : (prefixWord ++ tailWord_5635104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635104).length < 2 ^ (prefixWord ++ tailWord_5635104).sum := by decide
  have hdescent : baseEnd_5635104 < baseStart_5635104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635136 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_5635136 : Nat := 118140960795 + 5635136 * 2 ^ 59
def prefixEnd_5635136 : Nat := 4983230072969 + 3 ^ 40 * 5635136 * 2
def baseEnd_5635136 : Nat := 2893533321454569738184487

theorem tailTrace_5635136 : CollatzResearch.WordTrace tailWord_5635136 prefixEnd_5635136 2893533321454569738184487 := by
  unfold tailWord_5635136
  simp only [CollatzResearch.WordTrace]
  refine ⟨102765147456436075726482631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137020196608581434301976841 102765147456436075726482631)
  ·
    refine ⟨154147721184654113589723947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102765147456436075726482631 154147721184654113589723947)
    ·
      refine ⟨231221581776981170384585921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154147721184654113589723947 231221581776981170384585921)
      ·
        refine ⟨173416186332735877788439441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231221581776981170384585921 173416186332735877788439441)
        ·
          refine ⟨130062139749551908341329581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173416186332735877788439441 130062139749551908341329581)
          ·
            refine ⟨48773302406081965627998593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130062139749551908341329581 48773302406081965627998593)
            ·
              refine ⟨36579976804561474220998945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48773302406081965627998593 36579976804561474220998945)
              ·
                refine ⟨27434982603421105665749209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36579976804561474220998945 27434982603421105665749209)
                ·
                  refine ⟨20576236952565829249311907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27434982603421105665749209 20576236952565829249311907)
                  ·
                    refine ⟨30864355428848743873967861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20576236952565829249311907 30864355428848743873967861)
                    ·
                      refine ⟨2893533321454569738184487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30864355428848743873967861 2893533321454569738184487)
                      ·
                        rfl

theorem cell23_5635136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_5635136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635136 prefixEnd_5635136 := by exact prefixLift 5635136
  have htrace : WordTrace (prefixWord ++ tailWord_5635136) baseStart_5635136 baseEnd_5635136 := by
    simpa [prefixWord, tailWord_5635136, baseEnd_5635136] using wordTrace_append hprefix tailTrace_5635136
  have hstable : (prefixWord ++ tailWord_5635136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635136).length < 2 ^ (prefixWord ++ tailWord_5635136).sum := by decide
  have hdescent : baseEnd_5635136 < baseStart_5635136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635146 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_5635146 : Nat := 118140960795 + 5635146 * 2 ^ 59
def prefixEnd_5635146 : Nat := 4983230072969 + 3 ^ 40 * 5635146 * 2
def baseEnd_5635146 : Nat := 2893538456261114699059441

theorem tailTrace_5635146 : CollatzResearch.WordTrace tailWord_5635146 prefixEnd_5635146 2893538456261114699059441 := by
  unfold tailWord_5635146
  simp only [CollatzResearch.WordTrace]
  refine ⟨51382664910708980790207323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137020439761890615440552861 51382664910708980790207323)
  ·
    refine ⟨77073997366063471185310985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51382664910708980790207323 77073997366063471185310985)
    ·
      refine ⟨57805498024547603388983239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77073997366063471185310985 57805498024547603388983239)
      ·
        refine ⟨86708247036821405083474859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57805498024547603388983239 86708247036821405083474859)
        ·
          refine ⟨130062370555232107625212289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86708247036821405083474859 130062370555232107625212289)
          ·
            refine ⟨97546777916424080718909217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130062370555232107625212289 97546777916424080718909217)
            ·
              refine ⟨73160083437318060539181913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97546777916424080718909217 73160083437318060539181913)
              ·
                refine ⟨54870062577988545404386435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73160083437318060539181913 54870062577988545404386435)
                ·
                  refine ⟨82305093866982818106579653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54870062577988545404386435 82305093866982818106579653)
                  ·
                    refine ⟨15432205100059278394983685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82305093866982818106579653 15432205100059278394983685)
                    ·
                      refine ⟨2893538456261114699059441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15432205100059278394983685 2893538456261114699059441)
                      ·
                        rfl

theorem cell23_5635146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_5635146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635146 prefixEnd_5635146 := by exact prefixLift 5635146
  have htrace : WordTrace (prefixWord ++ tailWord_5635146) baseStart_5635146 baseEnd_5635146 := by
    simpa [prefixWord, tailWord_5635146, baseEnd_5635146] using wordTrace_append hprefix tailTrace_5635146
  have hstable : (prefixWord ++ tailWord_5635146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635146).length < 2 ^ (prefixWord ++ tailWord_5635146).sum := by decide
  have hdescent : baseEnd_5635146 < baseStart_5635146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635150 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_5635150 : Nat := 118140960795 + 5635150 * 2 ^ 59
def prefixEnd_5635150 : Nat := 4983230072969 + 3 ^ 40 * 5635150 * 2
def baseEnd_5635150 : Nat := 2893540510183732683409423

theorem tailTrace_5635150 : CollatzResearch.WordTrace tailWord_5635150 prefixEnd_5635150 2893540510183732683409423 := by
  unfold tailWord_5635150
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691350691852678980496863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137020537023214287895983269 25691350691852678980496863)
  ·
    refine ⟨38537026037779018470745295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25691350691852678980496863 38537026037779018470745295)
    ·
      refine ⟨57805539056668527706117943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38537026037779018470745295 57805539056668527706117943)
      ·
        refine ⟨86708308585002791559176915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57805539056668527706117943 86708308585002791559176915)
        ·
          refine ⟨130062462877504187338765373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86708308585002791559176915 130062462877504187338765373)
          ·
            refine ⟨48773423579064070252037015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130062462877504187338765373 48773423579064070252037015)
            ·
              refine ⟨73160135368596105378055523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48773423579064070252037015 73160135368596105378055523)
              ·
                refine ⟨109740203052894158067083285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73160135368596105378055523 109740203052894158067083285)
                ·
                  refine ⟨5144072018104413659394529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109740203052894158067083285 5144072018104413659394529)
                  ·
                    refine ⟨3858054013578310244545897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5144072018104413659394529 3858054013578310244545897)
                    ·
                      refine ⟨2893540510183732683409423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858054013578310244545897 2893540510183732683409423)
                      ·
                        rfl

theorem cell23_5635150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_5635150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635150 prefixEnd_5635150 := by exact prefixLift 5635150
  have htrace : WordTrace (prefixWord ++ tailWord_5635150) baseStart_5635150 baseEnd_5635150 := by
    simpa [prefixWord, tailWord_5635150, baseEnd_5635150] using wordTrace_append hprefix tailTrace_5635150
  have hstable : (prefixWord ++ tailWord_5635150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635150).length < 2 ^ (prefixWord ++ tailWord_5635150).sum := by decide
  have hdescent : baseEnd_5635150 < baseStart_5635150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635156 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 9]
def baseStart_5635156 : Nat := 118140960795 + 5635156 * 2 ^ 59
def prefixEnd_5635156 : Nat := 4983230072969 + 3 ^ 40 * 5635156 * 2
def baseEnd_5635156 : Nat := 321504843451962184437155

theorem tailTrace_5635156 : CollatzResearch.WordTrace tailWord_5635156 prefixEnd_5635156 321504843451962184437155 := by
  unfold tailWord_5635156
  simp only [CollatzResearch.WordTrace]
  refine ⟨102765512186399847434346661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137020682915199796579128881 102765512186399847434346661)
  ·
    refine ⟨19268533534949971393939999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102765512186399847434346661 19268533534949971393939999)
    ·
      refine ⟨28902800302424957090909999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19268533534949971393939999 28902800302424957090909999)
      ·
        refine ⟨43354200453637435636364999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28902800302424957090909999 43354200453637435636364999)
        ·
          refine ⟨65031300680456153454547499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43354200453637435636364999 65031300680456153454547499)
          ·
            refine ⟨97546951020684230181821249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65031300680456153454547499 97546951020684230181821249)
            ·
              refine ⟨73160213265513172636365937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97546951020684230181821249 73160213265513172636365937)
              ·
                refine ⟨54870159949134879477274453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73160213265513172636365937 54870159949134879477274453)
                ·
                  refine ⟨321504843451962184437155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54870159949134879477274453 321504843451962184437155)
                  ·
                    rfl

theorem cell23_5635156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_5635156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635156 prefixEnd_5635156 := by exact prefixLift 5635156
  have htrace : WordTrace (prefixWord ++ tailWord_5635156) baseStart_5635156 baseEnd_5635156 := by
    simpa [prefixWord, tailWord_5635156, baseEnd_5635156] using wordTrace_append hprefix tailTrace_5635156
  have hstable : (prefixWord ++ tailWord_5635156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635156).length < 2 ^ (prefixWord ++ tailWord_5635156).sum := by decide
  have hdescent : baseEnd_5635156 < baseStart_5635156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635196 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_5635196 : Nat := 118140960795 + 5635196 * 2 ^ 59
def prefixEnd_5635196 : Nat := 4983230072969 + 3 ^ 40 * 5635196 * 2
def baseEnd_5635196 : Nat := 2893564130293839503434211

theorem tailTrace_5635196 : CollatzResearch.WordTrace tailWord_5635196 prefixEnd_5635196 2893564130293839503434211 := by
  unfold tailWord_5635196
  simp only [CollatzResearch.WordTrace]
  refine ⟨102766241646327390850074721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137021655528436521133432961 102766241646327390850074721)
  ·
    refine ⟨77074681234745543137556041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102766241646327390850074721 77074681234745543137556041)
    ·
      refine ⟨57806010926059157353167031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77074681234745543137556041 57806010926059157353167031)
      ·
        refine ⟨86709016389088736029750547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57806010926059157353167031 86709016389088736029750547)
        ·
          refine ⟨130063524583633104044625821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86709016389088736029750547 130063524583633104044625821)
          ·
            refine ⟨48773821718862414016734683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130063524583633104044625821 48773821718862414016734683)
            ·
              refine ⟨73160732578293621025102025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48773821718862414016734683 73160732578293621025102025)
              ·
                refine ⟨54870549433720215768826519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73160732578293621025102025 54870549433720215768826519)
                ·
                  refine ⟨82305824150580323653239779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54870549433720215768826519 82305824150580323653239779)
                  ·
                    refine ⟨123458736225870485479859669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82305824150580323653239779 123458736225870485479859669)
                    ·
                      refine ⟨2893564130293839503434211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123458736225870485479859669 2893564130293839503434211)
                      ·
                        rfl

theorem cell23_5635196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_5635196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635196 prefixEnd_5635196 := by exact prefixLift 5635196
  have htrace : WordTrace (prefixWord ++ tailWord_5635196) baseStart_5635196 baseEnd_5635196 := by
    simpa [prefixWord, tailWord_5635196, baseEnd_5635196] using wordTrace_append hprefix tailTrace_5635196
  have hstable : (prefixWord ++ tailWord_5635196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635196).length < 2 ^ (prefixWord ++ tailWord_5635196).sum := by decide
  have hdescent : baseEnd_5635196 < baseStart_5635196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635203 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 2, 5]
def baseStart_5635203 : Nat := 118140960795 + 5635203 * 2 ^ 59
def prefixEnd_5635203 : Nat := 4983230072969 + 3 ^ 40 * 5635203 * 2
def baseEnd_5635203 : Nat := 964522574886140325348893

theorem tailTrace_5635203 : CollatzResearch.WordTrace tailWord_5635203 prefixEnd_5635203 964522574886140325348893 := by
  unfold tailWord_5635203
  simp only [CollatzResearch.WordTrace]
  refine ⟨205532738603629421895654263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137021825735752947930436175 205532738603629421895654263)
  ·
    refine ⟨308299107905444132843481395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205532738603629421895654263 308299107905444132843481395)
    ·
      refine ⟨462448661858166199265222093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308299107905444132843481395 462448661858166199265222093)
      ·
        refine ⟨173418248196812324724458285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 462448661858166199265222093 173418248196812324724458285)
        ·
          refine ⟨65031843073804621771671857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173418248196812324724458285 65031843073804621771671857)
          ·
            refine ⟨48773882305353466328753893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65031843073804621771671857 48773882305353466328753893)
            ·
              refine ⟨9145102932253774936641355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48773882305353466328753893 9145102932253774936641355)
              ·
                refine ⟨13717654398380662404962033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9145102932253774936641355 13717654398380662404962033)
                ·
                  refine ⟨10288240798785496803721525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13717654398380662404962033 10288240798785496803721525)
                  ·
                    refine ⟨964522574886140325348893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10288240798785496803721525 964522574886140325348893)
                    ·
                      rfl

theorem cell23_5635203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 5].length) (baseStart_5635203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635203 prefixEnd_5635203 := by exact prefixLift 5635203
  have htrace : WordTrace (prefixWord ++ tailWord_5635203) baseStart_5635203 baseEnd_5635203 := by
    simpa [prefixWord, tailWord_5635203, baseEnd_5635203] using wordTrace_append hprefix tailTrace_5635203
  have hstable : (prefixWord ++ tailWord_5635203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635203).length < 2 ^ (prefixWord ++ tailWord_5635203).sum := by decide
  have hdescent : baseEnd_5635203 < baseStart_5635203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635230 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5635230 : Nat := 118140960795 + 5635230 * 2 ^ 59
def prefixEnd_5635230 : Nat := 4983230072969 + 3 ^ 40 * 5635230 * 2
def baseEnd_5635230 : Nat := 2893581588636092370409055

theorem tailTrace_5635230 : CollatzResearch.WordTrace tailWord_5635230 prefixEnd_5635230 2893581588636092370409055 := by
  unfold tailWord_5635230
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691715421816450688360893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137022482249687737004591429 25691715421816450688360893)
  ·
    refine ⟨9634393283181169008135335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25691715421816450688360893 9634393283181169008135335)
    ·
      refine ⟨14451589924771753512203003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9634393283181169008135335 14451589924771753512203003)
      ·
        refine ⟨21677384887157630268304505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14451589924771753512203003 21677384887157630268304505)
        ·
          refine ⟨16258038665368222701228379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21677384887157630268304505 16258038665368222701228379)
          ·
            refine ⟨24387057998052334051842569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16258038665368222701228379 24387057998052334051842569)
            ·
              refine ⟨18290293498539250538881927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24387057998052334051842569 18290293498539250538881927)
              ·
                refine ⟨27435440247808875808322891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18290293498539250538881927 27435440247808875808322891)
                ·
                  refine ⟨41153160371713313712484337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27435440247808875808322891 41153160371713313712484337)
                  ·
                    refine ⟨30864870278784985284363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41153160371713313712484337 30864870278784985284363253)
                    ·
                      refine ⟨2893581588636092370409055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30864870278784985284363253 2893581588636092370409055)
                      ·
                        rfl

theorem cell23_5635230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5635230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635230 prefixEnd_5635230 := by exact prefixLift 5635230
  have htrace : WordTrace (prefixWord ++ tailWord_5635230) baseStart_5635230 baseEnd_5635230 := by
    simpa [prefixWord, tailWord_5635230, baseEnd_5635230] using wordTrace_append hprefix tailTrace_5635230
  have hstable : (prefixWord ++ tailWord_5635230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635230).length < 2 ^ (prefixWord ++ tailWord_5635230).sum := by decide
  have hdescent : baseEnd_5635230 < baseStart_5635230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635250 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_5635250 : Nat := 118140960795 + 5635250 * 2 ^ 59
def prefixEnd_5635250 : Nat := 4983230072969 + 3 ^ 40 * 5635250 * 2
def baseEnd_5635250 : Nat := 964530619416394097386321

theorem tailTrace_5635250 : CollatzResearch.WordTrace tailWord_5635250 prefixEnd_5635250 964530619416394097386321 := by
  unfold tailWord_5635250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51383613208614787230653801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137022968556306099281743469 51383613208614787230653801)
  ·
    refine ⟨38537709906461090422990351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51383613208614787230653801 38537709906461090422990351)
    ·
      refine ⟨57806564859691635634485527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38537709906461090422990351 57806564859691635634485527)
      ·
        refine ⟨86709847289537453451728291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57806564859691635634485527 86709847289537453451728291)
        ·
          refine ⟨130064770934306180177592437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86709847289537453451728291 130064770934306180177592437)
          ·
            refine ⟨12193572275091204391649291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130064770934306180177592437 12193572275091204391649291)
            ·
              refine ⟨18290358412636806587473937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12193572275091204391649291 18290358412636806587473937)
              ·
                refine ⟨13717768809477604940605453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18290358412636806587473937 13717768809477604940605453)
                ·
                  refine ⟨5144163303554101852727045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13717768809477604940605453 5144163303554101852727045)
                  ·
                    refine ⟨964530619416394097386321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144163303554101852727045 964530619416394097386321)
                    ·
                      rfl

theorem cell23_5635250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_5635250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635250 prefixEnd_5635250 := by exact prefixLift 5635250
  have htrace : WordTrace (prefixWord ++ tailWord_5635250) baseStart_5635250 baseEnd_5635250 := by
    simpa [prefixWord, tailWord_5635250, baseEnd_5635250] using wordTrace_append hprefix tailTrace_5635250
  have hstable : (prefixWord ++ tailWord_5635250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635250).length < 2 ^ (prefixWord ++ tailWord_5635250).sum := by decide
  have hdescent : baseEnd_5635250 < baseStart_5635250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635260 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_5635260 : Nat := 118140960795 + 5635260 * 2 ^ 59
def prefixEnd_5635260 : Nat := 4983230072969 + 3 ^ 40 * 5635260 * 2
def baseEnd_5635260 : Nat := 2893596993055727253033917

theorem tailTrace_5635260 : CollatzResearch.WordTrace tailWord_5635260 prefixEnd_5635260 2893596993055727253033917 := by
  unfold tailWord_5635260
  simp only [CollatzResearch.WordTrace]
  refine ⟨102767408782211460315239617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137023211709615280420319489 102767408782211460315239617)
  ·
    refine ⟨77075556586658595236429713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102767408782211460315239617 77075556586658595236429713)
    ·
      refine ⟨57806667439993946427322285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77075556586658595236429713 57806667439993946427322285)
      ·
        refine ⟨21677500289997729910245857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57806667439993946427322285 21677500289997729910245857)
        ·
          refine ⟨16258125217498297432684393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21677500289997729910245857 16258125217498297432684393)
          ·
            refine ⟨12193593913123723074513295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16258125217498297432684393 12193593913123723074513295)
            ·
              refine ⟨18290390869685584611769943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12193593913123723074513295 18290390869685584611769943)
              ·
                refine ⟨27435586304528376917654915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18290390869685584611769943 27435586304528376917654915)
                ·
                  refine ⟨41153379456792565376482373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27435586304528376917654915 41153379456792565376482373)
                  ·
                    refine ⟨7716258648148606008090445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41153379456792565376482373 7716258648148606008090445)
                    ·
                      refine ⟨2893596993055727253033917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7716258648148606008090445 2893596993055727253033917)
                      ·
                        rfl

theorem cell23_5635260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_5635260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635260 prefixEnd_5635260 := by exact prefixLift 5635260
  have htrace : WordTrace (prefixWord ++ tailWord_5635260) baseStart_5635260 baseEnd_5635260 := by
    simpa [prefixWord, tailWord_5635260, baseEnd_5635260] using wordTrace_append hprefix tailTrace_5635260
  have hstable : (prefixWord ++ tailWord_5635260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635260).length < 2 ^ (prefixWord ++ tailWord_5635260).sum := by decide
  have hdescent : baseEnd_5635260 < baseStart_5635260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635284 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5635284 : Nat := 118140960795 + 5635284 * 2 ^ 59
def prefixEnd_5635284 : Nat := 4983230072969 + 3 ^ 40 * 5635284 * 2
def baseEnd_5635284 : Nat := 964536438863811719711269

theorem tailTrace_5635284 : CollatzResearch.WordTrace tailWord_5635284 prefixEnd_5635284 964536438863811719711269 := by
  unfold tailWord_5635284
  simp only [CollatzResearch.WordTrace]
  refine ⟨102767846458167986364676453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137023795277557315152901937 102767846458167986364676453)
  ·
    refine ⟨19268971210906497443376835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102767846458167986364676453 19268971210906497443376835)
    ·
      refine ⟨28903456816359746165065253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19268971210906497443376835 28903456816359746165065253)
      ·
        refine ⟨5419398153067452405949735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28903456816359746165065253 5419398153067452405949735)
        ·
          refine ⟨8129097229601178608924603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419398153067452405949735 8129097229601178608924603)
          ·
            refine ⟨12193645844401767913386905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129097229601178608924603 12193645844401767913386905)
            ·
              refine ⟨9145234383301325935040179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12193645844401767913386905 9145234383301325935040179)
              ·
                refine ⟨13717851574951988902560269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9145234383301325935040179 13717851574951988902560269)
                ·
                  refine ⟨5144194340606995838460101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13717851574951988902560269 5144194340606995838460101)
                  ·
                    refine ⟨964536438863811719711269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144194340606995838460101 964536438863811719711269)
                    ·
                      rfl

theorem cell23_5635284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5635284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635284 prefixEnd_5635284 := by exact prefixLift 5635284
  have htrace : WordTrace (prefixWord ++ tailWord_5635284) baseStart_5635284 baseEnd_5635284 := by
    simpa [prefixWord, tailWord_5635284, baseEnd_5635284] using wordTrace_append hprefix tailTrace_5635284
  have hstable : (prefixWord ++ tailWord_5635284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635284).length < 2 ^ (prefixWord ++ tailWord_5635284).sum := by decide
  have hdescent : baseEnd_5635284 < baseStart_5635284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635300 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_5635300 : Nat := 118140960795 + 5635300 * 2 ^ 59
def prefixEnd_5635300 : Nat := 4983230072969 + 3 ^ 40 * 5635300 * 2
def baseEnd_5635300 : Nat := 2893617532281907096533733

theorem tailTrace_5635300 : CollatzResearch.WordTrace tailWord_5635300 prefixEnd_5635300 2893617532281907096533733 := by
  unfold tailWord_5635300
  simp only [CollatzResearch.WordTrace]
  refine ⟨102768138242139003730967677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137024184322852004974623569 102768138242139003730967677)
  ·
    refine ⟨38538051840802126399112879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102768138242139003730967677 38538051840802126399112879)
    ·
      refine ⟨57807077761203189598669319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38538051840802126399112879 57807077761203189598669319)
      ·
        refine ⟨86710616641804784398003979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57807077761203189598669319 86710616641804784398003979)
        ·
          refine ⟨130065924962707176597005969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86710616641804784398003979 130065924962707176597005969)
          ·
            refine ⟨97549443722030382447754477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130065924962707176597005969 97549443722030382447754477)
            ·
              refine ⟨36581041395761393417907929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97549443722030382447754477 36581041395761393417907929)
              ·
                refine ⟨27435781046821045063430947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36581041395761393417907929 27435781046821045063430947)
                ·
                  refine ⟨41153671570231567595146421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27435781046821045063430947 41153671570231567595146421)
                  ·
                    refine ⟨3858156709709209462044977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41153671570231567595146421 3858156709709209462044977)
                    ·
                      refine ⟨2893617532281907096533733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858156709709209462044977 2893617532281907096533733)
                      ·
                        rfl

theorem cell23_5635300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_5635300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635300 prefixEnd_5635300 := by exact prefixLift 5635300
  have htrace : WordTrace (prefixWord ++ tailWord_5635300) baseStart_5635300 baseEnd_5635300 := by
    simpa [prefixWord, tailWord_5635300, baseEnd_5635300] using wordTrace_append hprefix tailTrace_5635300
  have hstable : (prefixWord ++ tailWord_5635300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635300).length < 2 ^ (prefixWord ++ tailWord_5635300).sum := by decide
  have hdescent : baseEnd_5635300 < baseStart_5635300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635310 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_5635310 : Nat := 118140960795 + 5635310 * 2 ^ 59
def prefixEnd_5635310 : Nat := 4983230072969 + 3 ^ 40 * 5635310 * 2
def baseEnd_5635310 : Nat := 964540889029484019136229

theorem tailTrace_5635310 : CollatzResearch.WordTrace tailWord_5635310 prefixEnd_5635310 964540889029484019136229 := by
  unfold tailWord_5635310
  simp only [CollatzResearch.WordTrace]
  refine ⟨25692080151780222396224923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137024427476161186113199589 25692080151780222396224923)
  ·
    refine ⟨38538120227670333594337385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25692080151780222396224923 38538120227670333594337385)
    ·
      refine ⟨28903590170752750195753039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38538120227670333594337385 28903590170752750195753039)
      ·
        refine ⟨43355385256129125293629559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28903590170752750195753039 43355385256129125293629559)
        ·
          refine ⟨65033077884193687940444339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43355385256129125293629559 65033077884193687940444339)
          ·
            refine ⟨97549616826290531910666509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65033077884193687940444339 97549616826290531910666509)
            ·
              refine ⟨36581106309858949466499941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97549616826290531910666509 36581106309858949466499941)
              ·
                refine ⟨6858957433098553024968739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36581106309858949466499941 6858957433098553024968739)
                ·
                  refine ⟨10288436149647829537453109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858957433098553024968739 10288436149647829537453109)
                  ·
                    refine ⟨964540889029484019136229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10288436149647829537453109 964540889029484019136229)
                    ·
                      rfl

theorem cell23_5635310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_5635310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635310 prefixEnd_5635310 := by exact prefixLift 5635310
  have htrace : WordTrace (prefixWord ++ tailWord_5635310) baseStart_5635310 baseEnd_5635310 := by
    simpa [prefixWord, tailWord_5635310, baseEnd_5635310] using wordTrace_append hprefix tailTrace_5635310
  have hstable : (prefixWord ++ tailWord_5635310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635310).length < 2 ^ (prefixWord ++ tailWord_5635310).sum := by decide
  have hdescent : baseEnd_5635310 < baseStart_5635310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635340 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_5635340 : Nat := 118140960795 + 5635340 * 2 ^ 59
def prefixEnd_5635340 : Nat := 4983230072969 + 3 ^ 40 * 5635340 * 2
def baseEnd_5635340 : Nat := 964546023836028980011183

theorem tailTrace_5635340 : CollatzResearch.WordTrace tailWord_5635340 prefixEnd_5635340 964546023836028980011183 := by
  unfold tailWord_5635340
  simp only [CollatzResearch.WordTrace]
  refine ⟨102768867702066547146695737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137025156936088729528927649 102768867702066547146695737)
  ·
    refine ⟨77076650776549910360021803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102768867702066547146695737 77076650776549910360021803)
    ·
      refine ⟨115614976164824865540032705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77076650776549910360021803 115614976164824865540032705)
      ·
        refine ⟨86711232123618649155024529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115614976164824865540032705 86711232123618649155024529)
        ·
          refine ⟨65033424092713986866268397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86711232123618649155024529 65033424092713986866268397)
          ·
            refine ⟨24387534034767745074850649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65033424092713986866268397 24387534034767745074850649)
            ·
              refine ⟨18290650526075808806137987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24387534034767745074850649 18290650526075808806137987)
              ·
                refine ⟨27435975789113713209206981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18290650526075808806137987 27435975789113713209206981)
                ·
                  refine ⟨5144245460458821226726309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27435975789113713209206981 5144245460458821226726309)
                  ·
                    refine ⟨964546023836028980011183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144245460458821226726309 964546023836028980011183)
                    ·
                      rfl

theorem cell23_5635340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_5635340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635340 prefixEnd_5635340 := by exact prefixLift 5635340
  have htrace : WordTrace (prefixWord ++ tailWord_5635340) baseStart_5635340 baseEnd_5635340 := by
    simpa [prefixWord, tailWord_5635340, baseEnd_5635340] using wordTrace_append hprefix tailTrace_5635340
  have hstable : (prefixWord ++ tailWord_5635340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635340).length < 2 ^ (prefixWord ++ tailWord_5635340).sum := by decide
  have hdescent : baseEnd_5635340 < baseStart_5635340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635370 : List Nat := [3, 1, 4, 2, 1, 1, 2, 9]
def baseStart_5635370 : Nat := 118140960795 + 5635370 * 2 ^ 59
def prefixEnd_5635370 : Nat := 4983230072969 + 3 ^ 40 * 5635370 * 2
def baseEnd_5635370 : Nat := 107172350960285993431793

theorem tailTrace_5635370 : CollatzResearch.WordTrace tailWord_5635370 prefixEnd_5635370 107172350960285993431793 := by
  unfold tailWord_5635370
  simp only [CollatzResearch.WordTrace]
  refine ⟨51384707398506102354245891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137025886396016272944655709 51384707398506102354245891)
  ·
    refine ⟨77077061097759153531368837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51384707398506102354245891 77077061097759153531368837)
    ·
      refine ⟨14451948955829841287131657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77077061097759153531368837 14451948955829841287131657)
      ·
        refine ⟨10838961716872380965348743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14451948955829841287131657 10838961716872380965348743)
        ·
          refine ⟨16258442575308571448023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10838961716872380965348743 16258442575308571448023115)
          ·
            refine ⟨24387663862962857172034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16258442575308571448023115 24387663862962857172034673)
            ·
              refine ⟨18290747897222142879026005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24387663862962857172034673 18290747897222142879026005)
              ·
                refine ⟨107172350960285993431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18290747897222142879026005 107172350960285993431793)
                ·
                  rfl

theorem cell23_5635370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_5635370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635370 prefixEnd_5635370 := by exact prefixLift 5635370
  have htrace : WordTrace (prefixWord ++ tailWord_5635370) baseStart_5635370 baseEnd_5635370 := by
    simpa [prefixWord, tailWord_5635370, baseEnd_5635370] using wordTrace_append hprefix tailTrace_5635370
  have hstable : (prefixWord ++ tailWord_5635370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635370).length < 2 ^ (prefixWord ++ tailWord_5635370).sum := by decide
  have hdescent : baseEnd_5635370 < baseStart_5635370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635421 : List Nat := [1, 4, 5, 1, 1, 1, 3, 7]
def baseStart_5635421 : Nat := 118140960795 + 5635421 * 2 ^ 59
def prefixEnd_5635421 : Nat := 4983230072969 + 3 ^ 40 * 5635421 * 2
def baseEnd_5635421 : Nat := 107173320868188930485951

theorem tailTrace_5635421 : CollatzResearch.WordTrace tailWord_5635421 prefixEnd_5635421 107173320868188930485951 := by
  unfold tailWord_5635421
  simp only [CollatzResearch.WordTrace]
  refine ⟨205540689716839645127090117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137027126477893096751393411 205540689716839645127090117)
  ·
    refine ⟨38538879321907433461329397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205540689716839645127090117 38538879321907433461329397)
    ·
      refine ⟨3613019936428821886999631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38538879321907433461329397 3613019936428821886999631)
      ·
        refine ⟨5419529904643232830499447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613019936428821886999631 5419529904643232830499447)
        ·
          refine ⟨8129294856964849245749171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419529904643232830499447 8129294856964849245749171)
          ·
            refine ⟨12193942285447273868623757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8129294856964849245749171 12193942285447273868623757)
            ·
              refine ⟨4572728357042727700733909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12193942285447273868623757 4572728357042727700733909)
              ·
                refine ⟨107173320868188930485951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4572728357042727700733909 107173320868188930485951)
                ·
                  rfl

theorem cell23_5635421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 7].length) (baseStart_5635421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635421 prefixEnd_5635421 := by exact prefixLift 5635421
  have htrace : WordTrace (prefixWord ++ tailWord_5635421) baseStart_5635421 baseEnd_5635421 := by
    simpa [prefixWord, tailWord_5635421, baseEnd_5635421] using wordTrace_append hprefix tailTrace_5635421
  have hstable : (prefixWord ++ tailWord_5635421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635421).length < 2 ^ (prefixWord ++ tailWord_5635421).sum := by decide
  have hdescent : baseEnd_5635421 < baseStart_5635421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635460 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 7]
def baseStart_5635460 : Nat := 118140960795 + 5635460 * 2 ^ 59
def prefixEnd_5635460 : Nat := 4983230072969 + 3 ^ 40 * 5635460 * 2
def baseEnd_5635460 : Nat := 321522187687402941170333

theorem tailTrace_5635460 : CollatzResearch.WordTrace tailWord_5635460 prefixEnd_5635460 321522187687402941170333 := by
  unfold tailWord_5635460
  simp only [CollatzResearch.WordTrace]
  refine ⟨102771056081849177393879917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137028074775798903191839889 102771056081849177393879917)
  ·
    refine ⟨38539146030693441522704969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102771056081849177393879917 38539146030693441522704969)
    ·
      refine ⟨28904359523020081142028727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38539146030693441522704969 28904359523020081142028727)
      ·
        refine ⟨43356539284530121713043091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28904359523020081142028727 43356539284530121713043091)
        ·
          refine ⟨65034808926795182569564637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43356539284530121713043091 65034808926795182569564637)
          ·
            refine ⟨24388053347548193463586739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65034808926795182569564637 24388053347548193463586739)
            ·
              refine ⟨36582080021322290195380109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24388053347548193463586739 36582080021322290195380109)
              ·
                refine ⟨13718280007995858823267541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36582080021322290195380109 13718280007995858823267541)
                ·
                  refine ⟨321522187687402941170333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13718280007995858823267541 321522187687402941170333)
                  ·
                    rfl

theorem cell23_5635460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_5635460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635460 prefixEnd_5635460 := by exact prefixLift 5635460
  have htrace : WordTrace (prefixWord ++ tailWord_5635460) baseStart_5635460 baseEnd_5635460 := by
    simpa [prefixWord, tailWord_5635460, baseEnd_5635460] using wordTrace_append hprefix tailTrace_5635460
  have hstable : (prefixWord ++ tailWord_5635460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635460).length < 2 ^ (prefixWord ++ tailWord_5635460).sum := by decide
  have hdescent : baseEnd_5635460 < baseStart_5635460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635527 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_5635527 : Nat := 118140960795 + 5635527 * 2 ^ 59
def prefixEnd_5635527 : Nat := 4983230072969 + 3 ^ 40 * 5635527 * 2
def baseEnd_5635527 : Nat := 2893734092390477708395189

theorem tailTrace_5635527 : CollatzResearch.WordTrace tailWord_5635527 prefixEnd_5635527 2893734092390477708395189 := by
  unfold tailWord_5635527
  simp only [CollatzResearch.WordTrace]
  refine ⟨205544555854455625230448835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137029703902970416820299223 205544555854455625230448835)
  ·
    refine ⟨308316833781683437845673253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205544555854455625230448835 308316833781683437845673253)
    ·
      refine ⟨57809406334065644596063735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308316833781683437845673253 57809406334065644596063735)
      ·
        refine ⟨86714109501098466894095603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57809406334065644596063735 86714109501098466894095603)
        ·
          refine ⟨130071164251647700341143405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86714109501098466894095603 130071164251647700341143405)
          ·
            refine ⟨48776686594367887627928777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130071164251647700341143405 48776686594367887627928777)
            ·
              refine ⟨36582514945775915720946583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48776686594367887627928777 36582514945775915720946583)
              ·
                refine ⟨54873772418663873581419875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36582514945775915720946583 54873772418663873581419875)
                ·
                  refine ⟨82310658627995810372129813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54873772418663873581419875 82310658627995810372129813)
                  ·
                    refine ⟨3858312123187303611193585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82310658627995810372129813 3858312123187303611193585)
                    ·
                      refine ⟨2893734092390477708395189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3858312123187303611193585 2893734092390477708395189)
                      ·
                        rfl

theorem cell23_5635527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_5635527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635527 prefixEnd_5635527 := by exact prefixLift 5635527
  have htrace : WordTrace (prefixWord ++ tailWord_5635527) baseStart_5635527 baseEnd_5635527 := by
    simpa [prefixWord, tailWord_5635527, baseEnd_5635527] using wordTrace_append hprefix tailTrace_5635527
  have hstable : (prefixWord ++ tailWord_5635527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635527).length < 2 ^ (prefixWord ++ tailWord_5635527).sum := by decide
  have hdescent : baseEnd_5635527 < baseStart_5635527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635594 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_5635594 : Nat := 118140960795 + 5635594 * 2 ^ 59
def prefixEnd_5635594 : Nat := 4983230072969 + 3 ^ 40 * 5635594 * 2
def baseEnd_5635594 : Nat := 2893768495594328946257381

theorem tailTrace_5635594 : CollatzResearch.WordTrace tailWord_5635594 prefixEnd_5635594 2893768495594328946257381 := by
  unfold tailWord_5635594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51386749886303223918284459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137031333030141930448758557 51386749886303223918284459)
  ·
    refine ⟨77080124829454835877426689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51386749886303223918284459 77080124829454835877426689)
    ·
      refine ⟨57810093622091126908070017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77080124829454835877426689 57810093622091126908070017)
      ·
        refine ⟨43357570216568345181052513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57810093622091126908070017 43357570216568345181052513)
        ·
          refine ⟨32518177662426258885789385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43357570216568345181052513 32518177662426258885789385)
          ·
            refine ⟨24388633246819694164342039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32518177662426258885789385 24388633246819694164342039)
            ·
              refine ⟨36582949870229541246513059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24388633246819694164342039 36582949870229541246513059)
              ·
                refine ⟨54874424805344311869769589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36582949870229541246513059 54874424805344311869769589)
                ·
                  refine ⟨5144477325501029237790899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54874424805344311869769589 5144477325501029237790899)
                  ·
                    refine ⟨7716715988251543856686349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5144477325501029237790899 7716715988251543856686349)
                    ·
                      refine ⟨2893768495594328946257381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7716715988251543856686349 2893768495594328946257381)
                      ·
                        rfl

theorem cell23_5635594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_5635594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635594 prefixEnd_5635594 := by exact prefixLift 5635594
  have htrace : WordTrace (prefixWord ++ tailWord_5635594) baseStart_5635594 baseEnd_5635594 := by
    simpa [prefixWord, tailWord_5635594, baseEnd_5635594] using wordTrace_append hprefix tailTrace_5635594
  have hstable : (prefixWord ++ tailWord_5635594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635594).length < 2 ^ (prefixWord ++ tailWord_5635594).sum := by decide
  have hdescent : baseEnd_5635594 < baseStart_5635594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635598 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5635598 : Nat := 118140960795 + 5635598 * 2 ^ 59
def prefixEnd_5635598 : Nat := 4983230072969 + 3 ^ 40 * 5635598 * 2
def baseEnd_5635598 : Nat := 2893770549516946930607363

theorem tailTrace_5635598 : CollatzResearch.WordTrace tailWord_5635598 prefixEnd_5635598 2893770549516946930607363 := by
  unfold tailWord_5635598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25693393179649800544535431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137031430291465602904188965 25693393179649800544535431)
  ·
    refine ⟨38540089769474700816803147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25693393179649800544535431 38540089769474700816803147)
    ·
      refine ⟨57810134654212051225204721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38540089769474700816803147 57810134654212051225204721)
      ·
        refine ⟨43357600990659038418903541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57810134654212051225204721 43357600990659038418903541)
        ·
          refine ⟨4064775092874284851772207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43357600990659038418903541 4064775092874284851772207)
          ·
            refine ⟨6097162639311427277658311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064775092874284851772207 6097162639311427277658311)
            ·
              refine ⟨9145743958967140916487467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6097162639311427277658311 9145743958967140916487467)
              ·
                refine ⟨13718615938450711374731201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9145743958967140916487467 13718615938450711374731201)
                ·
                  refine ⟨10288961953838033531048401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13718615938450711374731201 10288961953838033531048401)
                  ·
                    refine ⟨7716721465378525148286301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10288961953838033531048401 7716721465378525148286301)
                    ·
                      refine ⟨2893770549516946930607363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7716721465378525148286301 2893770549516946930607363)
                      ·
                        rfl

theorem cell23_5635598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5635598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635598 prefixEnd_5635598 := by exact prefixLift 5635598
  have htrace : WordTrace (prefixWord ++ tailWord_5635598) baseStart_5635598 baseEnd_5635598 := by
    simpa [prefixWord, tailWord_5635598, baseEnd_5635598] using wordTrace_append hprefix tailTrace_5635598
  have hstable : (prefixWord ++ tailWord_5635598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635598).length < 2 ^ (prefixWord ++ tailWord_5635598).sum := by decide
  have hdescent : baseEnd_5635598 < baseStart_5635598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635637 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_5635637 : Nat := 118140960795 + 5635637 * 2 ^ 59
def prefixEnd_5635637 : Nat := 4983230072969 + 3 ^ 40 * 5635637 * 2
def baseEnd_5635637 : Nat := 2893790575262472278019683

theorem tailTrace_5635637 : CollatzResearch.WordTrace tailWord_5635637 prefixEnd_5635637 2893790575262472278019683 := by
  unfold tailWord_5635637
  simp only [CollatzResearch.WordTrace]
  refine ⟨205548567884057114016953165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137032378589371409344635443 205548567884057114016953165)
  ·
    refine ⟨77080712956521417756357437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205548567884057114016953165 77080712956521417756357437)
    ·
      refine ⟨28905267358695531658634039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77080712956521417756357437 28905267358695531658634039)
      ·
        refine ⟨43357901038043297487951059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28905267358695531658634039 43357901038043297487951059)
        ·
          refine ⟨65036851557064946231926589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43357901038043297487951059 65036851557064946231926589)
          ·
            refine ⟨24388819333899354836972471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65036851557064946231926589 24388819333899354836972471)
            ·
              refine ⟨36583229000849032255458707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24388819333899354836972471 36583229000849032255458707)
              ·
                refine ⟨54874843501273548383188061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36583229000849032255458707 54874843501273548383188061)
                ·
                  refine ⟨20578066312977580643695523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54874843501273548383188061 20578066312977580643695523)
                  ·
                    refine ⟨30867099469466370965543285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20578066312977580643695523 30867099469466370965543285)
                    ·
                      refine ⟨2893790575262472278019683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30867099469466370965543285 2893790575262472278019683)
                      ·
                        rfl

theorem cell23_5635637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_5635637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635637 prefixEnd_5635637 := by exact prefixLift 5635637
  have htrace : WordTrace (prefixWord ++ tailWord_5635637) baseStart_5635637 baseEnd_5635637 := by
    simpa [prefixWord, tailWord_5635637, baseEnd_5635637] using wordTrace_append hprefix tailTrace_5635637
  have hstable : (prefixWord ++ tailWord_5635637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635637).length < 2 ^ (prefixWord ++ tailWord_5635637).sum := by decide
  have hdescent : baseEnd_5635637 < baseStart_5635637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635647 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_5635647 : Nat := 118140960795 + 5635647 * 2 ^ 59
def prefixEnd_5635647 : Nat := 4983230072969 + 3 ^ 40 * 5635647 * 2
def baseEnd_5635647 : Nat := 2893795710069017238894637

theorem tailTrace_5635647 : CollatzResearch.WordTrace tailWord_5635647 prefixEnd_5635647 2893795710069017238894637 := by
  unfold tailWord_5635647
  simp only [CollatzResearch.WordTrace]
  refine ⟨205548932614020885724817195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137032621742680590483211463 205548932614020885724817195)
  ·
    refine ⟨308323398921031328587225793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205548932614020885724817195 308323398921031328587225793)
    ·
      refine ⟨231242549190773496440419345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308323398921031328587225793 231242549190773496440419345)
      ·
        refine ⟨173431911893080122330314509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231242549190773496440419345 173431911893080122330314509)
        ·
          refine ⟨65036966959905045873867941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173431911893080122330314509 65036966959905045873867941)
          ·
            refine ⟨12194431304982196101350239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65036966959905045873867941 12194431304982196101350239)
            ·
              refine ⟨18291646957473294152025359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12194431304982196101350239 18291646957473294152025359)
              ·
                refine ⟨27437470436209941228038039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18291646957473294152025359 27437470436209941228038039)
                ·
                  refine ⟨41156205654314911842057059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27437470436209941228038039 41156205654314911842057059)
                  ·
                    refine ⟨61734308481472367763085589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41156205654314911842057059 61734308481472367763085589)
                    ·
                      refine ⟨2893795710069017238894637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61734308481472367763085589 2893795710069017238894637)
                      ·
                        rfl

theorem cell23_5635647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_5635647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635647 prefixEnd_5635647 := by exact prefixLift 5635647
  have htrace : WordTrace (prefixWord ++ tailWord_5635647) baseStart_5635647 baseEnd_5635647 := by
    simpa [prefixWord, tailWord_5635647, baseEnd_5635647] using wordTrace_append hprefix tailTrace_5635647
  have hstable : (prefixWord ++ tailWord_5635647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635647).length < 2 ^ (prefixWord ++ tailWord_5635647).sum := by decide
  have hdescent : baseEnd_5635647 < baseStart_5635647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635727 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_5635727 : Nat := 118140960795 + 5635727 * 2 ^ 59
def prefixEnd_5635727 : Nat := 4983230072969 + 3 ^ 40 * 5635727 * 2
def baseEnd_5635727 : Nat := 2893836788521376925894269

theorem tailTrace_5635727 : CollatzResearch.WordTrace tailWord_5635727 prefixEnd_5635727 2893836788521376925894269 := by
  unfold tailWord_5635727
  simp only [CollatzResearch.WordTrace]
  refine ⟨205551850453731059387729435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137034566969154039591819623 205551850453731059387729435)
  ·
    refine ⟨308327775680596589081594153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205551850453731059387729435 308327775680596589081594153)
    ·
      refine ⟨231245831760447441811195615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308327775680596589081594153 231245831760447441811195615)
      ·
        refine ⟨346868747640671162716793423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231245831760447441811195615 346868747640671162716793423)
        ·
          refine ⟨520303121461006744075190135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346868747640671162716793423 520303121461006744075190135)
          ·
            refine ⟨780454682191510116112785203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520303121461006744075190135 780454682191510116112785203)
            ·
              refine ⟨1170682023287265174169177805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780454682191510116112785203 1170682023287265174169177805)
              ·
                refine ⟨439005758732724440313441677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1170682023287265174169177805 439005758732724440313441677)
                ·
                  refine ⟨164627159524771665117540629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439005758732724440313441677 164627159524771665117540629)
                  ·
                    refine ⟨7716898102723671802384717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164627159524771665117540629 7716898102723671802384717)
                    ·
                      refine ⟨2893836788521376925894269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7716898102723671802384717 2893836788521376925894269)
                      ·
                        rfl

theorem cell23_5635727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_5635727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635727 prefixEnd_5635727 := by exact prefixLift 5635727
  have htrace : WordTrace (prefixWord ++ tailWord_5635727) baseStart_5635727 baseEnd_5635727 := by
    simpa [prefixWord, tailWord_5635727, baseEnd_5635727] using wordTrace_append hprefix tailTrace_5635727
  have hstable : (prefixWord ++ tailWord_5635727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635727).length < 2 ^ (prefixWord ++ tailWord_5635727).sum := by decide
  have hdescent : baseEnd_5635727 < baseStart_5635727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635744 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_5635744 : Nat := 118140960795 + 5635744 * 2 ^ 59
def prefixEnd_5635744 : Nat := 4983230072969 + 3 ^ 40 * 5635744 * 2
def baseEnd_5635744 : Nat := 2893845517692503359381691

theorem tailTrace_5635744 : CollatzResearch.WordTrace tailWord_5635744 prefixEnd_5635744 2893845517692503359381691 := by
  unfold tailWord_5635744
  simp only [CollatzResearch.WordTrace]
  refine ⟨102776235247334735645549143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137034980329779647527398857 102776235247334735645549143)
  ·
    refine ⟨154164352871002103468323715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102776235247334735645549143 154164352871002103468323715)
    ·
      refine ⟨231246529306503155202485573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154164352871002103468323715 231246529306503155202485573)
      ·
        refine ⟨43358724244969341600466045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231246529306503155202485573 43358724244969341600466045)
        ·
          refine ⟨16259521591863503100174767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43358724244969341600466045 16259521591863503100174767)
          ·
            refine ⟨24389282387795254650262151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16259521591863503100174767 24389282387795254650262151)
            ·
              refine ⟨36583923581692881975393227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24389282387795254650262151 36583923581692881975393227)
              ·
                refine ⟨54875885372539322963089841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36583923581692881975393227 54875885372539322963089841)
                ·
                  refine ⟨41156914029404492222317381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54875885372539322963089841 41156914029404492222317381)
                  ·
                    refine ⟨7716921380513342291684509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41156914029404492222317381 7716921380513342291684509)
                    ·
                      refine ⟨2893845517692503359381691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7716921380513342291684509 2893845517692503359381691)
                      ·
                        rfl

theorem cell23_5635744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_5635744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635744 prefixEnd_5635744 := by exact prefixLift 5635744
  have htrace : WordTrace (prefixWord ++ tailWord_5635744) baseStart_5635744 baseEnd_5635744 := by
    simpa [prefixWord, tailWord_5635744, baseEnd_5635744] using wordTrace_append hprefix tailTrace_5635744
  have hstable : (prefixWord ++ tailWord_5635744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635744).length < 2 ^ (prefixWord ++ tailWord_5635744).sum := by decide
  have hdescent : baseEnd_5635744 < baseStart_5635744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635747 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 7]
def baseStart_5635747 : Nat := 118140960795 + 5635747 * 2 ^ 59
def prefixEnd_5635747 : Nat := 4983230072969 + 3 ^ 40 * 5635747 * 2
def baseEnd_5635747 : Nat := 321538562014940760849353

theorem tailTrace_5635747 : CollatzResearch.WordTrace tailWord_5635747 prefixEnd_5635747 321538562014940760849353 := by
  unfold tailWord_5635747
  simp only [CollatzResearch.WordTrace]
  refine ⟨205552579913658602803457495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137035053275772401868971663 205552579913658602803457495)
  ·
    refine ⟨308328869870487904205186243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205552579913658602803457495 308328869870487904205186243)
    ·
      refine ⟨462493304805731856307779365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308328869870487904205186243 462493304805731856307779365)
      ·
        refine ⟨86717494651074723057708631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 462493304805731856307779365 86717494651074723057708631)
        ·
          refine ⟨130076241976612084586562947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86717494651074723057708631 130076241976612084586562947)
          ·
            refine ⟨195114362964918126879844421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130076241976612084586562947 195114362964918126879844421)
            ·
              refine ⟨36583943055922148789970829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195114362964918126879844421 36583943055922148789970829)
              ·
                refine ⟨13718978645970805796239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36583943055922148789970829 13718978645970805796239061)
                ·
                  refine ⟨321538562014940760849353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13718978645970805796239061 321538562014940760849353)
                  ·
                    rfl

theorem cell23_5635747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 7].length) (baseStart_5635747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635747 prefixEnd_5635747 := by exact prefixLift 5635747
  have htrace : WordTrace (prefixWord ++ tailWord_5635747) baseStart_5635747 baseEnd_5635747 := by
    simpa [prefixWord, tailWord_5635747, baseEnd_5635747] using wordTrace_append hprefix tailTrace_5635747
  have hstable : (prefixWord ++ tailWord_5635747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635747).length < 2 ^ (prefixWord ++ tailWord_5635747).sum := by decide
  have hdescent : baseEnd_5635747 < baseStart_5635747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5635787 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_5635787 : Nat := 118140960795 + 5635787 * 2 ^ 59
def prefixEnd_5635787 : Nat := 4983230072969 + 3 ^ 40 * 5635787 * 2
def baseEnd_5635787 : Nat := 2893867597360646691143993

theorem tailTrace_5635787 : CollatzResearch.WordTrace tailWord_5635787 prefixEnd_5635787 2893867597360646691143993 := by
  unfold tailWord_5635787
  simp only [CollatzResearch.WordTrace]
  refine ⟨205554038833513689634913615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137036025889009126423275743 205554038833513689634913615)
  ·
    refine ⟨308331058250270534452370423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205554038833513689634913615 308331058250270534452370423)
    ·
      refine ⟨462496587375405801678555635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308331058250270534452370423 462496587375405801678555635)
      ·
        refine ⟨693744881063108702517833453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462496587375405801678555635 693744881063108702517833453)
        ·
          refine ⟨260154330398665763444187545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693744881063108702517833453 260154330398665763444187545)
          ·
            refine ⟨195115747798999322583140659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260154330398665763444187545 195115747798999322583140659)
            ·
              refine ⟨292673621698498983874710989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195115747798999322583140659 292673621698498983874710989)
              ·
                refine ⟨109752608136937118953016621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292673621698498983874710989 109752608136937118953016621)
                ·
                  refine ⟨41157228051351419607381233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109752608136937118953016621 41157228051351419607381233)
                  ·
                    refine ⟨30867921038513564705535925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41157228051351419607381233 30867921038513564705535925)
                    ·
                      refine ⟨2893867597360646691143993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30867921038513564705535925 2893867597360646691143993)
                      ·
                        rfl

theorem cell23_5635787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_5635787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5635787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5635787 prefixEnd_5635787 := by exact prefixLift 5635787
  have htrace : WordTrace (prefixWord ++ tailWord_5635787) baseStart_5635787 baseEnd_5635787 := by
    simpa [prefixWord, tailWord_5635787, baseEnd_5635787] using wordTrace_append hprefix tailTrace_5635787
  have hstable : (prefixWord ++ tailWord_5635787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5635787).length < 2 ^ (prefixWord ++ tailWord_5635787).sum := by decide
  have hdescent : baseEnd_5635787 < baseStart_5635787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5635787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
