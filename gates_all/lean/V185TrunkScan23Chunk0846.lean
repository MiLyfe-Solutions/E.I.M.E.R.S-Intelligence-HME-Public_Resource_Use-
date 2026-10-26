import V185TrunkScan23Chunk0845

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5007105 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5007105 : Nat := 118140960795 + 5007105 * 2 ^ 59
def prefixEnd_5007105 : Nat := 4983230072969 + 3 ^ 40 * 5007105 * 2
def baseEnd_5007105 : Nat := 2571051552530737412360249

theorem tailTrace_5007105 : CollatzResearch.WordTrace tailWord_5007105 prefixEnd_5007105 2571051552530737412360249 := by
  unfold tailWord_5007105
  simp only [CollatzResearch.WordTrace]
  refine ⟨182624122525121205297502769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121749415016747470198335179 182624122525121205297502769)
  ·
    refine ⟨136968091893840903973127077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182624122525121205297502769 136968091893840903973127077)
    ·
      refine ⟨25681517230095169494961327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136968091893840903973127077 25681517230095169494961327)
      ·
        refine ⟨38522275845142754242441991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25681517230095169494961327 38522275845142754242441991)
        ·
          refine ⟨57783413767714131363662987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38522275845142754242441991 57783413767714131363662987)
          ·
            refine ⟨86675120651571197045494481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57783413767714131363662987 86675120651571197045494481)
            ·
              refine ⟨65006340488678397784120861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86675120651571197045494481 65006340488678397784120861)
              ·
                refine ⟨24377377683254399169045323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65006340488678397784120861 24377377683254399169045323)
                ·
                  refine ⟨36566066524881598753567985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24377377683254399169045323 36566066524881598753567985)
                  ·
                    refine ⟨27424549893661199065175989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36566066524881598753567985 27424549893661199065175989)
                    ·
                      refine ⟨2571051552530737412360249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27424549893661199065175989 2571051552530737412360249)
                      ·
                        rfl

theorem cell23_5007105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5007105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007105 prefixEnd_5007105 := by exact prefixLift 5007105
  have htrace : WordTrace (prefixWord ++ tailWord_5007105) baseStart_5007105 baseEnd_5007105 := by
    simpa [prefixWord, tailWord_5007105, baseEnd_5007105] using wordTrace_append hprefix tailTrace_5007105
  have hstable : (prefixWord ++ tailWord_5007105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007105).length < 2 ^ (prefixWord ++ tailWord_5007105).sum := by decide
  have hdescent : baseEnd_5007105 < baseStart_5007105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007115 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_5007115 : Nat := 118140960795 + 5007115 * 2 ^ 59
def prefixEnd_5007115 : Nat := 4983230072969 + 3 ^ 40 * 5007115 * 2
def baseEnd_5007115 : Nat := 2571056687337282373235203

theorem tailTrace_5007115 : CollatzResearch.WordTrace tailWord_5007115 prefixEnd_5007115 2571056687337282373235203 := by
  unfold tailWord_5007115
  simp only [CollatzResearch.WordTrace]
  refine ⟨182624487255084977005366799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121749658170056651336911199 182624487255084977005366799)
  ·
    refine ⟨273936730882627465508050199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182624487255084977005366799 273936730882627465508050199)
    ·
      refine ⟨410905096323941198262075299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273936730882627465508050199 410905096323941198262075299)
      ·
        refine ⟨616357644485911797393112949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410905096323941198262075299 616357644485911797393112949)
        ·
          refine ⟨57783529170554231005604339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 616357644485911797393112949 57783529170554231005604339)
          ·
            refine ⟨86675293755831346508406509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57783529170554231005604339 86675293755831346508406509)
            ·
              refine ⟨32503235158436754940652441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86675293755831346508406509 32503235158436754940652441)
              ·
                refine ⟨24377426368827566205489331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32503235158436754940652441 24377426368827566205489331)
                ·
                  refine ⟨36566139553241349308233997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24377426368827566205489331 36566139553241349308233997)
                  ·
                    refine ⟨13712302332465505990587749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36566139553241349308233997 13712302332465505990587749)
                    ·
                      refine ⟨2571056687337282373235203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13712302332465505990587749 2571056687337282373235203)
                      ·
                        rfl

theorem cell23_5007115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_5007115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007115 prefixEnd_5007115 := by exact prefixLift 5007115
  have htrace : WordTrace (prefixWord ++ tailWord_5007115) baseStart_5007115 baseEnd_5007115 := by
    simpa [prefixWord, tailWord_5007115, baseEnd_5007115] using wordTrace_append hprefix tailTrace_5007115
  have hstable : (prefixWord ++ tailWord_5007115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007115).length < 2 ^ (prefixWord ++ tailWord_5007115).sum := by decide
  have hdescent : baseEnd_5007115 < baseStart_5007115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007132 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5007132 : Nat := 118140960795 + 5007132 * 2 ^ 59
def prefixEnd_5007132 : Nat := 4983230072969 + 3 ^ 40 * 5007132 * 2
def baseEnd_5007132 : Nat := 2571065416508408806722625

theorem tailTrace_5007132 : CollatzResearch.WordTrace tailWord_5007132 prefixEnd_5007132 2571065416508408806722625 := by
  unfold tailWord_5007132
  simp only [CollatzResearch.WordTrace]
  refine ⟨91312553648011694454367825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121750071530682259272490433 91312553648011694454367825)
  ·
    refine ⟨68484415236008770840775869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91312553648011694454367825 68484415236008770840775869)
    ·
      refine ⟨25681655713503289065290951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68484415236008770840775869 25681655713503289065290951)
      ·
        refine ⟨38522483570254933597936427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25681655713503289065290951 38522483570254933597936427)
        ·
          refine ⟨57783725355382400396904641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38522483570254933597936427 57783725355382400396904641)
          ·
            refine ⟨43337794016536800297678481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57783725355382400396904641 43337794016536800297678481)
            ·
              refine ⟨32503345512402600223258861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43337794016536800297678481 32503345512402600223258861)
              ·
                refine ⟨12188754567150975083722073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32503345512402600223258861 12188754567150975083722073)
                ·
                  refine ⟨9141565925363231312791555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12188754567150975083722073 9141565925363231312791555)
                  ·
                    refine ⟨13712348888044846969187333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9141565925363231312791555 13712348888044846969187333)
                    ·
                      refine ⟨2571065416508408806722625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13712348888044846969187333 2571065416508408806722625)
                      ·
                        rfl

theorem cell23_5007132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5007132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007132 prefixEnd_5007132 := by exact prefixLift 5007132
  have htrace : WordTrace (prefixWord ++ tailWord_5007132) baseStart_5007132 baseEnd_5007132 := by
    simpa [prefixWord, tailWord_5007132, baseEnd_5007132] using wordTrace_append hprefix tailTrace_5007132
  have hstable : (prefixWord ++ tailWord_5007132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007132).length < 2 ^ (prefixWord ++ tailWord_5007132).sum := by decide
  have hdescent : baseEnd_5007132 < baseStart_5007132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007175 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_5007175 : Nat := 118140960795 + 5007175 * 2 ^ 59
def prefixEnd_5007175 : Nat := 4983230072969 + 3 ^ 40 * 5007175 * 2
def baseEnd_5007175 : Nat := 2571087496176552138484927

theorem tailTrace_5007175 : CollatzResearch.WordTrace tailWord_5007175 prefixEnd_5007175 2571087496176552138484927 := by
  unfold tailWord_5007175
  simp only [CollatzResearch.WordTrace]
  refine ⟨182626675634867607252550979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121751117089911738168367319 182626675634867607252550979)
  ·
    refine ⟨273940013452301410878826469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182626675634867607252550979 273940013452301410878826469)
    ·
      refine ⟨51363752522306514539779963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273940013452301410878826469 51363752522306514539779963)
      ·
        refine ⟨77045628783459771809669945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51363752522306514539779963 77045628783459771809669945)
        ·
          refine ⟨57784221587594828857252459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77045628783459771809669945 57784221587594828857252459)
          ·
            refine ⟨86676332381392243285878689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57784221587594828857252459 86676332381392243285878689)
            ·
              refine ⟨65007249286044182464409017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86676332381392243285878689 65007249286044182464409017)
              ·
                refine ⟨48755436964533136848306763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65007249286044182464409017 48755436964533136848306763)
                ·
                  refine ⟨73133155446799705272460145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48755436964533136848306763 73133155446799705272460145)
                  ·
                    refine ⟨54849866585099778954345109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73133155446799705272460145 54849866585099778954345109)
                    ·
                      refine ⟨2571087496176552138484927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54849866585099778954345109 2571087496176552138484927)
                      ·
                        rfl

theorem cell23_5007175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_5007175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007175 prefixEnd_5007175 := by exact prefixLift 5007175
  have htrace : WordTrace (prefixWord ++ tailWord_5007175) baseStart_5007175 baseEnd_5007175 := by
    simpa [prefixWord, tailWord_5007175, baseEnd_5007175] using wordTrace_append hprefix tailTrace_5007175
  have hstable : (prefixWord ++ tailWord_5007175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007175).length < 2 ^ (prefixWord ++ tailWord_5007175).sum := by decide
  have hdescent : baseEnd_5007175 < baseStart_5007175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007232 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_5007232 : Nat := 118140960795 + 5007232 * 2 ^ 59
def prefixEnd_5007232 : Nat := 4983230072969 + 3 ^ 40 * 5007232 * 2
def baseEnd_5007232 : Nat := 857038921524619471824055

theorem tailTrace_5007232 : CollatzResearch.WordTrace tailWord_5007232 prefixEnd_5007232 857038921524619471824055 := by
  unfold tailWord_5007232
  simp only [CollatzResearch.WordTrace]
  refine ⟨91314377297830552993687975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121752503063774070658250633 91314377297830552993687975)
  ·
    refine ⟨136971565946745829490531963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91314377297830552993687975 136971565946745829490531963)
    ·
      refine ⟨205457348920118744235797945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136971565946745829490531963 205457348920118744235797945)
      ·
        refine ⟨154093011690089058176848459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205457348920118744235797945 154093011690089058176848459)
        ·
          refine ⟨231139517535133587265272689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154093011690089058176848459 231139517535133587265272689)
          ·
            refine ⟨173354638151350190448954517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231139517535133587265272689 173354638151350190448954517)
            ·
              refine ⟨8125998663344540177294743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173354638151350190448954517 8125998663344540177294743)
              ·
                refine ⟨12188997995016810265942115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8125998663344540177294743 12188997995016810265942115)
                ·
                  refine ⟨18283496992525215398913173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12188997995016810265942115 18283496992525215398913173)
                  ·
                    refine ⟨857038921524619471824055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18283496992525215398913173 857038921524619471824055)
                    ·
                      rfl

theorem cell23_5007232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_5007232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007232 prefixEnd_5007232 := by exact prefixLift 5007232
  have htrace : WordTrace (prefixWord ++ tailWord_5007232) baseStart_5007232 baseEnd_5007232 := by
    simpa [prefixWord, tailWord_5007232, baseEnd_5007232] using wordTrace_append hprefix tailTrace_5007232
  have hstable : (prefixWord ++ tailWord_5007232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007232).length < 2 ^ (prefixWord ++ tailWord_5007232).sum := by decide
  have hdescent : baseEnd_5007232 < baseStart_5007232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007233 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5007233 : Nat := 118140960795 + 5007233 * 2 ^ 59
def prefixEnd_5007233 : Nat := 4983230072969 + 3 ^ 40 * 5007233 * 2
def baseEnd_5007233 : Nat := 2571117278054512911559661

theorem tailTrace_5007233 : CollatzResearch.WordTrace tailWord_5007233 prefixEnd_5007233 2571117278054512911559661 := by
  unfold tailWord_5007233
  simp only [CollatzResearch.WordTrace]
  refine ⟨182628791068657483158162353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121752527379104988772108235 182628791068657483158162353)
  ·
    refine ⟨136971593301493112368621765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182628791068657483158162353 136971593301493112368621765)
    ·
      refine ⟨25682173744029958569116581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136971593301493112368621765 25682173744029958569116581)
      ·
        refine ⟨4815407577005617231709359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25682173744029958569116581 4815407577005617231709359)
        ·
          refine ⟨7223111365508425847564039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815407577005617231709359 7223111365508425847564039)
          ·
            refine ⟨10834667048262638771346059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223111365508425847564039 10834667048262638771346059)
            ·
              refine ⟨16252000572393958157019089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834667048262638771346059 16252000572393958157019089)
              ·
                refine ⟨12189000429295468617764317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16252000572393958157019089 12189000429295468617764317)
                ·
                  refine ⟨4570875160985800731661619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12189000429295468617764317 4570875160985800731661619)
                  ·
                    refine ⟨6856312741478701097492429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4570875160985800731661619 6856312741478701097492429)
                    ·
                      refine ⟨2571117278054512911559661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6856312741478701097492429 2571117278054512911559661)
                      ·
                        rfl

theorem cell23_5007233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5007233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007233 prefixEnd_5007233 := by exact prefixLift 5007233
  have htrace : WordTrace (prefixWord ++ tailWord_5007233) baseStart_5007233 baseEnd_5007233 := by
    simpa [prefixWord, tailWord_5007233, baseEnd_5007233] using wordTrace_append hprefix tailTrace_5007233
  have hstable : (prefixWord ++ tailWord_5007233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007233).length < 2 ^ (prefixWord ++ tailWord_5007233).sum := by decide
  have hdescent : baseEnd_5007233 < baseStart_5007233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007250 : List Nat := [3, 2, 3, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5007250 : Nat := 118140960795 + 5007250 * 2 ^ 59
def prefixEnd_5007250 : Nat := 4983230072969 + 3 ^ 40 * 5007250 * 2
def baseEnd_5007250 : Nat := 2571126007225639345047083

theorem tailTrace_5007250 : CollatzResearch.WordTrace tailWord_5007250 prefixEnd_5007250 2571126007225639345047083 := by
  unfold tailWord_5007250
  simp only [CollatzResearch.WordTrace]
  refine ⟨45657352777398973765382801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121752940739730596707687469 45657352777398973765382801)
  ·
    refine ⟨34243014583049230324037101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45657352777398973765382801 34243014583049230324037101)
    ·
      refine ⟨12841130468643461371513913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34243014583049230324037101 12841130468643461371513913)
      ·
        refine ⟨9630847851482596028635435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12841130468643461371513913 9630847851482596028635435)
        ·
          refine ⟨14446271777223894042953153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9630847851482596028635435 14446271777223894042953153)
          ·
            refine ⟨10834703832917920532214865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14446271777223894042953153 10834703832917920532214865)
            ·
              refine ⟨8126027874688440399161149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10834703832917920532214865 8126027874688440399161149)
              ·
                refine ⟨3047260453008165149685431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8126027874688440399161149 3047260453008165149685431)
                ·
                  refine ⟨4570890679512247724528147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047260453008165149685431 4570890679512247724528147)
                  ·
                    refine ⟨6856336019268371586792221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4570890679512247724528147 6856336019268371586792221)
                    ·
                      refine ⟨2571126007225639345047083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6856336019268371586792221 2571126007225639345047083)
                      ·
                        rfl

theorem cell23_5007250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5007250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007250 prefixEnd_5007250 := by exact prefixLift 5007250
  have htrace : WordTrace (prefixWord ++ tailWord_5007250) baseStart_5007250 baseEnd_5007250 := by
    simpa [prefixWord, tailWord_5007250, baseEnd_5007250] using wordTrace_append hprefix tailTrace_5007250
  have hstable : (prefixWord ++ tailWord_5007250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007250).length < 2 ^ (prefixWord ++ tailWord_5007250).sum := by decide
  have hdescent : baseEnd_5007250 < baseStart_5007250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007266 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_5007266 : Nat := 118140960795 + 5007266 * 2 ^ 59
def prefixEnd_5007266 : Nat := 4983230072969 + 3 ^ 40 * 5007266 * 2
def baseEnd_5007266 : Nat := 857044740972037094149003

theorem tailTrace_5007266 : CollatzResearch.WordTrace tailWord_5007266 prefixEnd_5007266 857044740972037094149003 := by
  unfold tailWord_5007266
  simp only [CollatzResearch.WordTrace]
  refine ⟨45657498669384482448528413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121753329785025286529409101 45657498669384482448528413)
  ·
    refine ⟨17121562001019180918198155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45657498669384482448528413 17121562001019180918198155)
    ·
      refine ⟨25682343001528771377297233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17121562001019180918198155 25682343001528771377297233)
      ·
        refine ⟨19261757251146578532972925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25682343001528771377297233 19261757251146578532972925)
        ·
          refine ⟨7223158969179966949864847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19261757251146578532972925 7223158969179966949864847)
          ·
            refine ⟨10834738453769950424797271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223158969179966949864847 10834738453769950424797271)
            ·
              refine ⟨16252107680654925637195907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834738453769950424797271 16252107680654925637195907)
              ·
                refine ⟨24378161520982388455793861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16252107680654925637195907 24378161520982388455793861)
                ·
                  refine ⟨4570905285184197835461349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24378161520982388455793861 4570905285184197835461349)
                  ·
                    refine ⟨857044740972037094149003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4570905285184197835461349 857044740972037094149003)
                    ·
                      rfl

theorem cell23_5007266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_5007266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007266 prefixEnd_5007266 := by exact prefixLift 5007266
  have htrace : WordTrace (prefixWord ++ tailWord_5007266) baseStart_5007266 baseEnd_5007266 := by
    simpa [prefixWord, tailWord_5007266, baseEnd_5007266] using wordTrace_append hprefix tailTrace_5007266
  have hstable : (prefixWord ++ tailWord_5007266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007266).length < 2 ^ (prefixWord ++ tailWord_5007266).sum := by decide
  have hdescent : baseEnd_5007266 < baseStart_5007266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007324 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5007324 : Nat := 118140960795 + 5007324 * 2 ^ 59
def prefixEnd_5007324 : Nat := 4983230072969 + 3 ^ 40 * 5007324 * 2
def baseEnd_5007324 : Nat := 2571164004794072055521743

theorem tailTrace_5007324 : CollatzResearch.WordTrace tailWord_5007324 prefixEnd_5007324 2571164004794072055521743 := by
  unfold tailWord_5007324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91316055055663902849862513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121754740074218537133150017 91316055055663902849862513)
  ·
    refine ⟨68487041291747927137396885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91316055055663902849862513 68487041291747927137396885)
    ·
      refine ⟨3210330060550684084565479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68487041291747927137396885 3210330060550684084565479)
      ·
        refine ⟨4815495090826026126848219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210330060550684084565479 4815495090826026126848219)
        ·
          refine ⟨7223242636239039190272329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815495090826026126848219 7223242636239039190272329)
          ·
            refine ⟨5417431977179279392704247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7223242636239039190272329 5417431977179279392704247)
            ·
              refine ⟨8126147965768919089056371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417431977179279392704247 8126147965768919089056371)
              ·
                refine ⟨12189221948653378633584557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126147965768919089056371 12189221948653378633584557)
                ·
                  refine ⟨4570958230745016987594209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12189221948653378633584557 4570958230745016987594209)
                  ·
                    refine ⟨3428218673058762740695657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4570958230745016987594209 3428218673058762740695657)
                    ·
                      refine ⟨2571164004794072055521743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428218673058762740695657 2571164004794072055521743)
                      ·
                        rfl

theorem cell23_5007324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5007324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007324 prefixEnd_5007324 := by exact prefixLift 5007324
  have htrace : WordTrace (prefixWord ++ tailWord_5007324) baseStart_5007324 baseEnd_5007324 := by
    simpa [prefixWord, tailWord_5007324, baseEnd_5007324] using wordTrace_append hprefix tailTrace_5007324
  have hstable : (prefixWord ++ tailWord_5007324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007324).length < 2 ^ (prefixWord ++ tailWord_5007324).sum := by decide
  have hdescent : baseEnd_5007324 < baseStart_5007324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007332 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_5007332 : Nat := 118140960795 + 5007332 * 2 ^ 59
def prefixEnd_5007332 : Nat := 4983230072969 + 3 ^ 40 * 5007332 * 2
def baseEnd_5007332 : Nat := 2571168112639308024221705

theorem tailTrace_5007332 : CollatzResearch.WordTrace tailWord_5007332 prefixEnd_5007332 2571168112639308024221705 := by
  unfold tailWord_5007332
  simp only [CollatzResearch.WordTrace]
  refine ⟨91316200947649411533008125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121754934596865882044010833 91316200947649411533008125)
  ·
    refine ⟨34243575355368529324878047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91316200947649411533008125 34243575355368529324878047)
    ·
      refine ⟨51365363033052793987317071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34243575355368529324878047 51365363033052793987317071)
      ·
        refine ⟨77048044549579190980975607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51365363033052793987317071 77048044549579190980975607)
        ·
          refine ⟨115572066824368786471463411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77048044549579190980975607 115572066824368786471463411)
          ·
            refine ⟨173358100236553179707195117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115572066824368786471463411 173358100236553179707195117)
            ·
              refine ⟨65009287588707442390198169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173358100236553179707195117 65009287588707442390198169)
              ·
                refine ⟨48756965691530581792648627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65009287588707442390198169 48756965691530581792648627)
                ·
                  refine ⟨73135448537295872688972941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48756965691530581792648627 73135448537295872688972941)
                  ·
                    refine ⟨27425793201485952258364853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73135448537295872688972941 27425793201485952258364853)
                    ·
                      refine ⟨2571168112639308024221705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27425793201485952258364853 2571168112639308024221705)
                      ·
                        rfl

theorem cell23_5007332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_5007332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007332 prefixEnd_5007332 := by exact prefixLift 5007332
  have htrace : WordTrace (prefixWord ++ tailWord_5007332) baseStart_5007332 baseEnd_5007332 := by
    simpa [prefixWord, tailWord_5007332, baseEnd_5007332] using wordTrace_append hprefix tailTrace_5007332
  have hstable : (prefixWord ++ tailWord_5007332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007332).length < 2 ^ (prefixWord ++ tailWord_5007332).sum := by decide
  have hdescent : baseEnd_5007332 < baseStart_5007332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007352 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 7]
def baseStart_5007352 : Nat := 118140960795 + 5007352 * 2 ^ 59
def prefixEnd_5007352 : Nat := 4983230072969 + 3 ^ 40 * 5007352 * 2
def baseEnd_5007352 : Nat := 285686486916933105107957

theorem tailTrace_5007352 : CollatzResearch.WordTrace tailWord_5007352 prefixEnd_5007352 285686486916933105107957 := by
  unfold tailWord_5007352
  simp only [CollatzResearch.WordTrace]
  refine ⟨91316565677613183240872155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121755420903484244321162873 91316565677613183240872155)
  ·
    refine ⟨136974848516419774861308233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91316565677613183240872155 136974848516419774861308233)
    ·
      refine ⟨102731136387314831145981175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136974848516419774861308233 102731136387314831145981175)
      ·
        refine ⟨154096704580972246718971763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102731136387314831145981175 154096704580972246718971763)
        ·
          refine ⟨231145056871458370078457645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154096704580972246718971763 231145056871458370078457645)
          ·
            refine ⟨86679396326796888779421617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231145056871458370078457645 86679396326796888779421617)
            ·
              refine ⟨65009547245097666584566213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86679396326796888779421617 65009547245097666584566213)
              ·
                refine ⟨12189290108455812484606165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65009547245097666584566213 12189290108455812484606165)
                ·
                  refine ⟨285686486916933105107957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12189290108455812484606165 285686486916933105107957)
                  ·
                    rfl

theorem cell23_5007352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_5007352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007352 prefixEnd_5007352 := by exact prefixLift 5007352
  have htrace : WordTrace (prefixWord ++ tailWord_5007352) baseStart_5007352 baseEnd_5007352 := by
    simpa [prefixWord, tailWord_5007352, baseEnd_5007352] using wordTrace_append hprefix tailTrace_5007352
  have hstable : (prefixWord ++ tailWord_5007352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007352).length < 2 ^ (prefixWord ++ tailWord_5007352).sum := by decide
  have hdescent : baseEnd_5007352 < baseStart_5007352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007386 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_5007386 : Nat := 118140960795 + 5007386 * 2 ^ 59
def prefixEnd_5007386 : Nat := 4983230072969 + 3 ^ 40 * 5007386 * 2
def baseEnd_5007386 : Nat := 285688426732738979216273

theorem tailTrace_5007386 : CollatzResearch.WordTrace tailWord_5007386 prefixEnd_5007386 285688426732738979216273 := by
  unfold tailWord_5007386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658592859275797572120503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121756247624735460192321341 45658592859275797572120503)
  ·
    refine ⟨68487889288913696358180755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45658592859275797572120503 68487889288913696358180755)
    ·
      refine ⟨102731833933370544537271133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68487889288913696358180755 102731833933370544537271133)
      ·
        refine ⟨38524437725013954201476675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102731833933370544537271133 38524437725013954201476675)
        ·
          refine ⟨57786656587520931302215013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38524437725013954201476675 57786656587520931302215013)
          ·
            refine ⟨10834998110160174619165315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57786656587520931302215013 10834998110160174619165315)
            ·
              refine ⟨16252497165240261928747973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834998110160174619165315 16252497165240261928747973)
              ·
                refine ⟨3047343218482549111640245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16252497165240261928747973 3047343218482549111640245)
                ·
                  refine ⟨285688426732738979216273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047343218482549111640245 285688426732738979216273)
                  ·
                    rfl

theorem cell23_5007386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_5007386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007386 prefixEnd_5007386 := by exact prefixLift 5007386
  have htrace : WordTrace (prefixWord ++ tailWord_5007386) baseStart_5007386 baseEnd_5007386 := by
    simpa [prefixWord, tailWord_5007386, baseEnd_5007386] using wordTrace_append hprefix tailTrace_5007386
  have hstable : (prefixWord ++ tailWord_5007386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007386).length < 2 ^ (prefixWord ++ tailWord_5007386).sum := by decide
  have hdescent : baseEnd_5007386 < baseStart_5007386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007429 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_5007429 : Nat := 118140960795 + 5007429 * 2 ^ 59
def prefixEnd_5007429 : Nat := 4983230072969 + 3 ^ 40 * 5007429 * 2
def baseEnd_5007429 : Nat := 857072640087598048236253

theorem tailTrace_5007429 : CollatzResearch.WordTrace tailWord_5007429 prefixEnd_5007429 857072640087598048236253 := by
  unfold tailWord_5007429
  simp only [CollatzResearch.WordTrace]
  refine ⟨182635939775947408632297341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121757293183964939088198227 182635939775947408632297341)
  ·
    refine ⟨68488477415980278237111503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182635939775947408632297341 68488477415980278237111503)
    ·
      refine ⟨102732716123970417355667255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68488477415980278237111503 102732716123970417355667255)
      ·
        refine ⟨154099074185955626033500883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102732716123970417355667255 154099074185955626033500883)
        ·
          refine ⟨231148611278933439050251325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154099074185955626033500883 231148611278933439050251325)
          ·
            refine ⟨86680729229600039643844247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231148611278933439050251325 86680729229600039643844247)
            ·
              refine ⟨130021093844400059465766371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86680729229600039643844247 130021093844400059465766371)
              ·
                refine ⟨195031640766600089198649557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130021093844400059465766371 195031640766600089198649557)
                ·
                  refine ⟨4571054080467189590593349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 195031640766600089198649557 4571054080467189590593349)
                  ·
                    refine ⟨857072640087598048236253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4571054080467189590593349 857072640087598048236253)
                    ·
                      rfl

theorem cell23_5007429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_5007429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007429 prefixEnd_5007429 := by exact prefixLift 5007429
  have htrace : WordTrace (prefixWord ++ tailWord_5007429) baseStart_5007429 baseEnd_5007429 := by
    simpa [prefixWord, tailWord_5007429, baseEnd_5007429] using wordTrace_append hprefix tailTrace_5007429
  have hstable : (prefixWord ++ tailWord_5007429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007429).length < 2 ^ (prefixWord ++ tailWord_5007429).sum := by decide
  have hdescent : baseEnd_5007429 < baseStart_5007429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007436 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5007436 : Nat := 118140960795 + 5007436 * 2 ^ 59
def prefixEnd_5007436 : Nat := 4983230072969 + 3 ^ 40 * 5007436 * 2
def baseEnd_5007436 : Nat := 2571221514627375617321227

theorem tailTrace_5007436 : CollatzResearch.WordTrace tailWord_5007436 prefixEnd_5007436 2571221514627375617321227 := by
  unfold tailWord_5007436
  simp only [CollatzResearch.WordTrace]
  refine ⟨91318097543461024413901081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121757463391281365885201441 91318097543461024413901081)
  ·
    refine ⟨68488573157595768310425811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91318097543461024413901081 68488573157595768310425811)
    ·
      refine ⟨102732859736393652465638717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68488573157595768310425811 102732859736393652465638717)
      ·
        refine ⟨38524822401147619674614519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102732859736393652465638717 38524822401147619674614519)
        ·
          refine ⟨57787233601721429511921779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38524822401147619674614519 57787233601721429511921779)
          ·
            refine ⟨86680850402582144267882669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57787233601721429511921779 86680850402582144267882669)
            ·
              refine ⟨32505318900968304100456001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86680850402582144267882669 32505318900968304100456001)
              ·
                refine ⟨24378989175726228075342001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32505318900968304100456001 24378989175726228075342001)
                ·
                  refine ⟨18284241881794671056506501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24378989175726228075342001 18284241881794671056506501)
                  ·
                    refine ⟨3428295352836500823094969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18284241881794671056506501 3428295352836500823094969)
                    ·
                      refine ⟨2571221514627375617321227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428295352836500823094969 2571221514627375617321227)
                      ·
                        rfl

theorem cell23_5007436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5007436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007436 prefixEnd_5007436 := by exact prefixLift 5007436
  have htrace : WordTrace (prefixWord ++ tailWord_5007436) baseStart_5007436 baseEnd_5007436 := by
    simpa [prefixWord, tailWord_5007436, baseEnd_5007436] using wordTrace_append hprefix tailTrace_5007436
  have hstable : (prefixWord ++ tailWord_5007436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007436).length < 2 ^ (prefixWord ++ tailWord_5007436).sum := by decide
  have hdescent : baseEnd_5007436 < baseStart_5007436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007459 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 6]
def baseStart_5007459 : Nat := 118140960795 + 5007459 * 2 ^ 59
def prefixEnd_5007459 : Nat := 4983230072969 + 3 ^ 40 * 5007459 * 2
def baseEnd_5007459 : Nat := 285692591631381003037069

theorem tailTrace_5007459 : CollatzResearch.WordTrace tailWord_5007459 prefixEnd_5007459 285692591631381003037069 := by
  unfold tailWord_5007459
  simp only [CollatzResearch.WordTrace]
  refine ⟨182637033965838723755889431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121758022643892482503926287 182637033965838723755889431)
  ·
    refine ⟨273955550948758085633834147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182637033965838723755889431 273955550948758085633834147)
    ·
      refine ⟨410933326423137128450751221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273955550948758085633834147 410933326423137128450751221)
      ·
        refine ⟨38524999352169105792257927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 410933326423137128450751221 38524999352169105792257927)
        ·
          refine ⟨57787499028253658688386891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38524999352169105792257927 57787499028253658688386891)
          ·
            refine ⟨86681248542380488032580337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57787499028253658688386891 86681248542380488032580337)
            ·
              refine ⟨65010936406785366024435253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86681248542380488032580337 65010936406785366024435253)
              ·
                refine ⟨6094775288136128064790805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65010936406785366024435253 6094775288136128064790805)
                ·
                  refine ⟨285692591631381003037069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6094775288136128064790805 285692591631381003037069)
                  ·
                    rfl

theorem cell23_5007459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 6].length) (baseStart_5007459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007459 prefixEnd_5007459 := by exact prefixLift 5007459
  have htrace : WordTrace (prefixWord ++ tailWord_5007459) baseStart_5007459 baseEnd_5007459 := by
    simpa [prefixWord, tailWord_5007459, baseEnd_5007459] using wordTrace_append hprefix tailTrace_5007459
  have hstable : (prefixWord ++ tailWord_5007459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007459).length < 2 ^ (prefixWord ++ tailWord_5007459).sum := by decide
  have hdescent : baseEnd_5007459 < baseStart_5007459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007506 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5007506 : Nat := 118140960795 + 5007506 * 2 ^ 59
def prefixEnd_5007506 : Nat := 4983230072969 + 3 ^ 40 * 5007506 * 2
def baseEnd_5007506 : Nat := 857085819424396781148635

theorem tailTrace_5007506 : CollatzResearch.WordTrace tailWord_5007506 prefixEnd_5007506 857085819424396781148635 := by
  unfold tailWord_5007506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45659687049167112695712593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121759165464445633855233581 45659687049167112695712593)
  ·
    refine ⟨34244765286875334521784445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45659687049167112695712593 34244765286875334521784445)
    ·
      refine ⟨12841786982578250445669167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34244765286875334521784445 12841786982578250445669167)
      ·
        refine ⟨19262680473867375668503751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12841786982578250445669167 19262680473867375668503751)
        ·
          refine ⟨28894020710801063502755627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19262680473867375668503751 28894020710801063502755627)
          ·
            refine ⟨43341031066201595254133441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28894020710801063502755627 43341031066201595254133441)
            ·
              refine ⟨32505773299651196440600081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43341031066201595254133441 32505773299651196440600081)
              ·
                refine ⟨24379329974738397330450061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32505773299651196440600081 24379329974738397330450061)
                ·
                  refine ⟨9142248740526898998918773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24379329974738397330450061 9142248740526898998918773)
                  ·
                    refine ⟨857085819424396781148635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142248740526898998918773 857085819424396781148635)
                    ·
                      rfl

theorem cell23_5007506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5007506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007506 prefixEnd_5007506 := by exact prefixLift 5007506
  have htrace : WordTrace (prefixWord ++ tailWord_5007506) baseStart_5007506 baseEnd_5007506 := by
    simpa [prefixWord, tailWord_5007506, baseEnd_5007506] using wordTrace_append hprefix tailTrace_5007506
  have hstable : (prefixWord ++ tailWord_5007506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007506).length < 2 ^ (prefixWord ++ tailWord_5007506).sum := by decide
  have hdescent : baseEnd_5007506 < baseStart_5007506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007546 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_5007546 : Nat := 118140960795 + 5007546 * 2 ^ 59
def prefixEnd_5007546 : Nat := 4983230072969 + 3 ^ 40 * 5007546 * 2
def baseEnd_5007546 : Nat := 2571277997499370186945721

theorem tailTrace_5007546 : CollatzResearch.WordTrace tailWord_5007546 prefixEnd_5007546 2571277997499370186945721 := by
  unfold tailWord_5007546
  simp only [CollatzResearch.WordTrace]
  refine ⟨45660051779130884403576623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121760138077682358409537661 45660051779130884403576623)
  ·
    refine ⟨68490077668696326605364935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45660051779130884403576623 68490077668696326605364935)
    ·
      refine ⟨102735116503044489908047403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68490077668696326605364935 102735116503044489908047403)
      ·
        refine ⟨154102674754566734862071105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102735116503044489908047403 154102674754566734862071105)
        ·
          refine ⟨115577006065925051146553329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154102674754566734862071105 115577006065925051146553329)
          ·
            refine ⟨86682754549443788359914997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115577006065925051146553329 86682754549443788359914997)
            ·
              refine ⟨8126508239010355158742031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86682754549443788359914997 8126508239010355158742031)
              ·
                refine ⟨12189762358515532738113047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126508239010355158742031 12189762358515532738113047)
                ·
                  refine ⟨18284643537773299107169571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12189762358515532738113047 18284643537773299107169571)
                  ·
                    refine ⟨27426965306659948660754357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18284643537773299107169571 27426965306659948660754357)
                    ·
                      refine ⟨2571277997499370186945721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27426965306659948660754357 2571277997499370186945721)
                      ·
                        rfl

theorem cell23_5007546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_5007546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007546 prefixEnd_5007546 := by exact prefixLift 5007546
  have htrace : WordTrace (prefixWord ++ tailWord_5007546) baseStart_5007546 baseEnd_5007546 := by
    simpa [prefixWord, tailWord_5007546, baseEnd_5007546] using wordTrace_append hprefix tailTrace_5007546
  have hstable : (prefixWord ++ tailWord_5007546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007546).length < 2 ^ (prefixWord ++ tailWord_5007546).sum := by decide
  have hdescent : baseEnd_5007546 < baseStart_5007546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007566 : List Nat := [4, 1, 1, 1, 4, 1, 3, 8]
def baseStart_5007566 : Nat := 118140960795 + 5007566 * 2 ^ 59
def prefixEnd_5007566 : Nat := 4983230072969 + 3 ^ 40 * 5007566 * 2
def baseEnd_5007566 : Nat := 95232898781942966988727

theorem tailTrace_5007566 : CollatzResearch.WordTrace tailWord_5007566 prefixEnd_5007566 95232898781942966988727 := by
  unfold tailWord_5007566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22830117072056385128754319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121760624384300720686689701 22830117072056385128754319)
  ·
    refine ⟨34245175608084577693131479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22830117072056385128754319 34245175608084577693131479)
    ·
      refine ⟨51367763412126866539697219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34245175608084577693131479 51367763412126866539697219)
      ·
        refine ⟨77051645118190299809545829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51367763412126866539697219 77051645118190299809545829)
        ·
          refine ⟨14447183459660681214289843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77051645118190299809545829 14447183459660681214289843)
          ·
            refine ⟨21670775189491021821434765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447183459660681214289843 21670775189491021821434765)
            ·
              refine ⟨8126540696059133183038037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21670775189491021821434765 8126540696059133183038037)
              ·
                refine ⟨95232898781942966988727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8126540696059133183038037 95232898781942966988727)
                ·
                  rfl

theorem cell23_5007566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_5007566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007566 prefixEnd_5007566 := by exact prefixLift 5007566
  have htrace : WordTrace (prefixWord ++ tailWord_5007566) baseStart_5007566 baseEnd_5007566 := by
    simpa [prefixWord, tailWord_5007566, baseEnd_5007566] using wordTrace_append hprefix tailTrace_5007566
  have hstable : (prefixWord ++ tailWord_5007566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007566).length < 2 ^ (prefixWord ++ tailWord_5007566).sum := by decide
  have hdescent : baseEnd_5007566 < baseStart_5007566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007569 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_5007569 : Nat := 118140960795 + 5007569 * 2 ^ 59
def prefixEnd_5007569 : Nat := 4983230072969 + 3 ^ 40 * 5007569 * 2
def baseEnd_5007569 : Nat := 2571289807554423596958115

theorem tailTrace_5007569 : CollatzResearch.WordTrace tailWord_5007569 prefixEnd_5007569 2571289807554423596958115 := by
  unfold tailWord_5007569
  simp only [CollatzResearch.WordTrace]
  refine ⟨182641045995440212542393761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121760697330293475028262507 182641045995440212542393761)
  ·
    refine ⟨136980784496580159406795321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182641045995440212542393761 136980784496580159406795321)
    ·
      refine ⟨102735588372435119555096491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136980784496580159406795321 102735588372435119555096491)
      ·
        refine ⟨154103382558652679332644737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102735588372435119555096491 154103382558652679332644737)
        ·
          refine ⟨115577536918989509499483553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154103382558652679332644737 115577536918989509499483553)
          ·
            refine ⟨86683152689242132124612665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115577536918989509499483553 86683152689242132124612665)
            ·
              refine ⟨65012364516931599093459499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86683152689242132124612665 65012364516931599093459499)
              ·
                refine ⟨97518546775397398640189249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65012364516931599093459499 97518546775397398640189249)
                ·
                  refine ⟨73138910081548048980141937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97518546775397398640189249 73138910081548048980141937)
                  ·
                    refine ⟨54854182561161036735106453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73138910081548048980141937 54854182561161036735106453)
                    ·
                      refine ⟨2571289807554423596958115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54854182561161036735106453 2571289807554423596958115)
                      ·
                        rfl

theorem cell23_5007569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_5007569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007569 prefixEnd_5007569 := by exact prefixLift 5007569
  have htrace : WordTrace (prefixWord ++ tailWord_5007569) baseStart_5007569 baseEnd_5007569 := by
    simpa [prefixWord, tailWord_5007569, baseEnd_5007569] using wordTrace_append hprefix tailTrace_5007569
  have hstable : (prefixWord ++ tailWord_5007569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007569).length < 2 ^ (prefixWord ++ tailWord_5007569).sum := by decide
  have hdescent : baseEnd_5007569 < baseStart_5007569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007610 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_5007610 : Nat := 118140960795 + 5007610 * 2 ^ 59
def prefixEnd_5007610 : Nat := 4983230072969 + 3 ^ 40 * 5007610 * 2
def baseEnd_5007610 : Nat := 2571310860261257936545427

theorem tailTrace_5007610 : CollatzResearch.WordTrace tailWord_5007610 prefixEnd_5007610 2571310860261257936545427 := by
  unfold tailWord_5007610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45660635347072919136159071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121761694258861117696424189 45660635347072919136159071)
  ·
    refine ⟨68490953020609378704238607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45660635347072919136159071 68490953020609378704238607)
    ·
      refine ⟨102736429530914068056357911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68490953020609378704238607 102736429530914068056357911)
      ·
        refine ⟨154104644296371102084536867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102736429530914068056357911 154104644296371102084536867)
        ·
          refine ⟨231156966444556653126805301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154104644296371102084536867 231156966444556653126805301)
          ·
            refine ⟨21670965604177186230637997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231156966444556653126805301 21670965604177186230637997)
            ·
              refine ⟨8126612101566444836489249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21670965604177186230637997 8126612101566444836489249)
              ·
                refine ⟨6094959076174833627366937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8126612101566444836489249 6094959076174833627366937)
                ·
                  refine ⟨4571219307131125220525203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6094959076174833627366937 4571219307131125220525203)
                  ·
                    refine ⟨6856828960696687830787805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571219307131125220525203 6856828960696687830787805)
                    ·
                      refine ⟨2571310860261257936545427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6856828960696687830787805 2571310860261257936545427)
                      ·
                        rfl

theorem cell23_5007610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_5007610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007610 prefixEnd_5007610 := by exact prefixLift 5007610
  have htrace : WordTrace (prefixWord ++ tailWord_5007610) baseStart_5007610 baseEnd_5007610 := by
    simpa [prefixWord, tailWord_5007610, baseEnd_5007610] using wordTrace_append hprefix tailTrace_5007610
  have hstable : (prefixWord ++ tailWord_5007610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007610).length < 2 ^ (prefixWord ++ tailWord_5007610).sum := by decide
  have hdescent : baseEnd_5007610 < baseStart_5007610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007626 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_5007626 : Nat := 118140960795 + 5007626 * 2 ^ 59
def prefixEnd_5007626 : Nat := 4983230072969 + 3 ^ 40 * 5007626 * 2
def baseEnd_5007626 : Nat := 857106358650576624648451

theorem tailTrace_5007626 : CollatzResearch.WordTrace tailWord_5007626 prefixEnd_5007626 857106358650576624648451 := by
  unfold tailWord_5007626
  simp only [CollatzResearch.WordTrace]
  refine ⟨45660781239058427819304683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121762083304155807518145821 45660781239058427819304683)
  ·
    refine ⟨68491171858587641728957025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45660781239058427819304683 68491171858587641728957025)
    ·
      refine ⟨51368378893940731296717769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68491171858587641728957025 51368378893940731296717769)
      ·
        refine ⟨38526284170455548472538327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51368378893940731296717769 38526284170455548472538327)
        ·
          refine ⟨57789426255683322708807491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38526284170455548472538327 57789426255683322708807491)
          ·
            refine ⟨86684139383524984063211237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57789426255683322708807491 86684139383524984063211237)
            ·
              refine ⟨16253276134410934511852107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86684139383524984063211237 16253276134410934511852107)
              ·
                refine ⟨24379914201616401767778161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16253276134410934511852107 24379914201616401767778161)
                ·
                  refine ⟨18284935651212301325833621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24379914201616401767778161 18284935651212301325833621)
                  ·
                    refine ⟨857106358650576624648451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18284935651212301325833621 857106358650576624648451)
                    ·
                      rfl

theorem cell23_5007626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_5007626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007626 prefixEnd_5007626 := by exact prefixLift 5007626
  have htrace : WordTrace (prefixWord ++ tailWord_5007626) baseStart_5007626 baseEnd_5007626 := by
    simpa [prefixWord, tailWord_5007626, baseEnd_5007626] using wordTrace_append hprefix tailTrace_5007626
  have hstable : (prefixWord ++ tailWord_5007626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007626).length < 2 ^ (prefixWord ++ tailWord_5007626).sum := by decide
  have hdescent : baseEnd_5007626 < baseStart_5007626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007653 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 5]
def baseStart_5007653 : Nat := 118140960795 + 5007653 * 2 ^ 59
def prefixEnd_5007653 : Nat := 4983230072969 + 3 ^ 40 * 5007653 * 2
def baseEnd_5007653 : Nat := 2571332939929401268307729

theorem tailTrace_5007653 : CollatzResearch.WordTrace tailWord_5007653 prefixEnd_5007653 2571332939929401268307729 := by
  unfold tailWord_5007653
  simp only [CollatzResearch.WordTrace]
  refine ⟨182644109727135894888451613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121762739818090596592301075 182644109727135894888451613)
  ·
    refine ⟨68491541147675960583169355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182644109727135894888451613 68491541147675960583169355)
    ·
      refine ⟨102737311721513940874754033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68491541147675960583169355 102737311721513940874754033)
      ·
        refine ⟨77052983791135455656065525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102737311721513940874754033 77052983791135455656065525)
        ·
          refine ⟨7223717230418948967756143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77052983791135455656065525 7223717230418948967756143)
          ·
            refine ⟨10835575845628423451634215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223717230418948967756143 10835575845628423451634215)
            ·
              refine ⟨16253363768442635177451323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10835575845628423451634215 16253363768442635177451323)
              ·
                refine ⟨24380045652663952766176985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16253363768442635177451323 24380045652663952766176985)
                ·
                  refine ⟨18285034239497964574632739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24380045652663952766176985 18285034239497964574632739)
                  ·
                    refine ⟨27427551359246946861949109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18285034239497964574632739 27427551359246946861949109)
                    ·
                      refine ⟨2571332939929401268307729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27427551359246946861949109 2571332939929401268307729)
                      ·
                        rfl

theorem cell23_5007653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_5007653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007653 prefixEnd_5007653 := by exact prefixLift 5007653
  have htrace : WordTrace (prefixWord ++ tailWord_5007653) baseStart_5007653 baseEnd_5007653 := by
    simpa [prefixWord, tailWord_5007653, baseEnd_5007653] using wordTrace_append hprefix tailTrace_5007653
  have hstable : (prefixWord ++ tailWord_5007653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007653).length < 2 ^ (prefixWord ++ tailWord_5007653).sum := by decide
  have hdescent : baseEnd_5007653 < baseStart_5007653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007673 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 7]
def baseStart_5007673 : Nat := 118140960795 + 5007673 * 2 ^ 59
def prefixEnd_5007673 : Nat := 4983230072969 + 3 ^ 40 * 5007673 * 2
def baseEnd_5007673 : Nat := 285704801060276798895293

theorem tailTrace_5007673 : CollatzResearch.WordTrace tailWord_5007673 prefixEnd_5007673 285704801060276798895293 := by
  unfold tailWord_5007673
  simp only [CollatzResearch.WordTrace]
  refine ⟨182644839187063438304179673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121763226124708958869453115 182644839187063438304179673)
  ·
    refine ⟨136983629390297578728134755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182644839187063438304179673 136983629390297578728134755)
    ·
      refine ⟨205475444085446368092202133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136983629390297578728134755 205475444085446368092202133)
      ·
        refine ⟨9631661441505298504321975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 205475444085446368092202133 9631661441505298504321975)
        ·
          refine ⟨14447492162257947756482963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9631661441505298504321975 14447492162257947756482963)
          ·
            refine ⟨21671238243386921634724445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447492162257947756482963 21671238243386921634724445)
            ·
              refine ⟨8126714341270095613021667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21671238243386921634724445 8126714341270095613021667)
              ·
                refine ⟨12190071511905143419532501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126714341270095613021667 12190071511905143419532501)
                ·
                  refine ⟨285704801060276798895293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12190071511905143419532501 285704801060276798895293)
                  ·
                    rfl

theorem cell23_5007673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_5007673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007673 prefixEnd_5007673 := by exact prefixLift 5007673
  have htrace : WordTrace (prefixWord ++ tailWord_5007673) baseStart_5007673 baseEnd_5007673 := by
    simpa [prefixWord, tailWord_5007673, baseEnd_5007673] using wordTrace_append hprefix tailTrace_5007673
  have hstable : (prefixWord ++ tailWord_5007673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007673).length < 2 ^ (prefixWord ++ tailWord_5007673).sum := by decide
  have hdescent : baseEnd_5007673 < baseStart_5007673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007703 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 2, 5]
def baseStart_5007703 : Nat := 118140960795 + 5007703 * 2 ^ 59
def prefixEnd_5007703 : Nat := 4983230072969 + 3 ^ 40 * 5007703 * 2
def baseEnd_5007703 : Nat := 857119537987375357560833

theorem tailTrace_5007703 : CollatzResearch.WordTrace tailWord_5007703 prefixEnd_5007703 857119537987375357560833 := by
  unfold tailWord_5007703
  simp only [CollatzResearch.WordTrace]
  refine ⟨182645933376954753427771763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121763955584636502285181175 182645933376954753427771763)
  ·
    refine ⟨273968900065432130141657645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182645933376954753427771763 273968900065432130141657645)
    ·
      refine ⟨102738337524537048803121617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273968900065432130141657645 102738337524537048803121617)
      ·
        refine ⟨77053753143402786602341213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102738337524537048803121617 77053753143402786602341213)
        ·
          refine ⟨28895157428776044975877955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77053753143402786602341213 28895157428776044975877955)
          ·
            refine ⟨43342736143164067463816933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28895157428776044975877955 43342736143164067463816933)
            ·
              refine ⟨8126763026843262649465675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43342736143164067463816933 8126763026843262649465675)
              ·
                refine ⟨12190144540264893974198513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126763026843262649465675 12190144540264893974198513)
                ·
                  refine ⟨9142608405198670480648885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12190144540264893974198513 9142608405198670480648885)
                  ·
                    refine ⟨857119537987375357560833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142608405198670480648885 857119537987375357560833)
                    ·
                      rfl

theorem cell23_5007703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_5007703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007703 prefixEnd_5007703 := by exact prefixLift 5007703
  have htrace : WordTrace (prefixWord ++ tailWord_5007703) baseStart_5007703 baseEnd_5007703 := by
    simpa [prefixWord, tailWord_5007703, baseEnd_5007703] using wordTrace_append hprefix tailTrace_5007703
  have hstable : (prefixWord ++ tailWord_5007703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007703).length < 2 ^ (prefixWord ++ tailWord_5007703).sum := by decide
  have hdescent : baseEnd_5007703 < baseStart_5007703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007723 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 4, 4, 2]
def baseStart_5007723 : Nat := 118140960795 + 5007723 * 2 ^ 59
def prefixEnd_5007723 : Nat := 4983230072969 + 3 ^ 40 * 5007723 * 2
def baseEnd_5007723 : Nat := 2571368883575215994432407

theorem tailTrace_5007723 : CollatzResearch.WordTrace tailWord_5007723 prefixEnd_5007723 2571368883575215994432407 := by
  unfold tailWord_5007723
  simp only [CollatzResearch.WordTrace]
  refine ⟨182646662836882296843499823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121764441891254864562333215 182646662836882296843499823)
  ·
    refine ⟨273969994255323445265249735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182646662836882296843499823 273969994255323445265249735)
    ·
      refine ⟨410954991382985167897874603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273969994255323445265249735 410954991382985167897874603)
      ·
        refine ⟨616432487074477751846811905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410954991382985167897874603 616432487074477751846811905)
        ·
          refine ⟨462324365305858313885108929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616432487074477751846811905 462324365305858313885108929)
          ·
            refine ⟨346743273979393735413831697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462324365305858313885108929 346743273979393735413831697)
            ·
              refine ⟨260057455484545301560373773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346743273979393735413831697 260057455484545301560373773)
              ·
                refine ⟨97521545806704488085140165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260057455484545301560373773 97521545806704488085140165)
                ·
                  refine ⟨18285289838757091515963781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97521545806704488085140165 18285289838757091515963781)
                  ·
                    refine ⟨3428491844766954659243209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18285289838757091515963781 3428491844766954659243209)
                    ·
                      refine ⟨2571368883575215994432407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428491844766954659243209 2571368883575215994432407)
                      ·
                        rfl

theorem cell23_5007723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4, 2].length) (baseStart_5007723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007723 prefixEnd_5007723 := by exact prefixLift 5007723
  have htrace : WordTrace (prefixWord ++ tailWord_5007723) baseStart_5007723 baseEnd_5007723 := by
    simpa [prefixWord, tailWord_5007723, baseEnd_5007723] using wordTrace_append hprefix tailTrace_5007723
  have hstable : (prefixWord ++ tailWord_5007723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007723).length < 2 ^ (prefixWord ++ tailWord_5007723).sum := by decide
  have hdescent : baseEnd_5007723 < baseStart_5007723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007724 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 5]
def baseStart_5007724 : Nat := 118140960795 + 5007724 * 2 ^ 59
def prefixEnd_5007724 : Nat := 4983230072969 + 3 ^ 40 * 5007724 * 2
def baseEnd_5007724 : Nat := 285707710783985610057767

theorem tailTrace_5007724 : CollatzResearch.WordTrace tailWord_5007724 prefixEnd_5007724 285707710783985610057767 := by
  unfold tailWord_5007724
  simp only [CollatzResearch.WordTrace]
  refine ⟨91323349654939337007143113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121764466206585782676190817 91323349654939337007143113)
  ·
    refine ⟨68492512241204502755357335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91323349654939337007143113 68492512241204502755357335)
    ·
      refine ⟨102738768361806754133036003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68492512241204502755357335 102738768361806754133036003)
      ·
        refine ⟨154108152542710131199554005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102738768361806754133036003 154108152542710131199554005)
        ·
          refine ⟨3611909825219768699989547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 154108152542710131199554005 3611909825219768699989547)
          ·
            refine ⟨5417864737829653049984321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611909825219768699989547 5417864737829653049984321)
            ·
              refine ⟨4063398553372239787488241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5417864737829653049984321 4063398553372239787488241)
              ·
                refine ⟨3047548915029179840616181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063398553372239787488241 3047548915029179840616181)
                ·
                  refine ⟨285707710783985610057767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047548915029179840616181 285707710783985610057767)
                  ·
                    rfl

theorem cell23_5007724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_5007724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007724 prefixEnd_5007724 := by exact prefixLift 5007724
  have htrace : WordTrace (prefixWord ++ tailWord_5007724) baseStart_5007724 baseEnd_5007724 := by
    simpa [prefixWord, tailWord_5007724, baseEnd_5007724] using wordTrace_append hprefix tailTrace_5007724
  have hstable : (prefixWord ++ tailWord_5007724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007724).length < 2 ^ (prefixWord ++ tailWord_5007724).sum := by decide
  have hdescent : baseEnd_5007724 < baseStart_5007724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007754 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_5007754 : Nat := 118140960795 + 5007754 * 2 ^ 59
def prefixEnd_5007754 : Nat := 4983230072969 + 3 ^ 40 * 5007754 * 2
def baseEnd_5007754 : Nat := 857128267158501791048255

theorem tailTrace_5007754 : CollatzResearch.WordTrace tailWord_5007754 prefixEnd_5007754 857128267158501791048255 := by
  unfold tailWord_5007754
  simp only [CollatzResearch.WordTrace]
  refine ⟨45661948374942497284469579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121765195666513326091918877 45661948374942497284469579)
  ·
    refine ⟨68492922562413745926704369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45661948374942497284469579 68492922562413745926704369)
    ·
      refine ⟨51369691921810309445028277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68492922562413745926704369 51369691921810309445028277)
      ·
        refine ⟨4815908617669716510471401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51369691921810309445028277 4815908617669716510471401)
        ·
          refine ⟨3611931463252287382853551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4815908617669716510471401 3611931463252287382853551)
          ·
            refine ⟨5417897194878431074280327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611931463252287382853551 5417897194878431074280327)
            ·
              refine ⟨8126845792317646611420491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417897194878431074280327 8126845792317646611420491)
              ·
                refine ⟨12190268688476469917130737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126845792317646611420491 12190268688476469917130737)
                ·
                  refine ⟨9142701516357352437848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12190268688476469917130737 9142701516357352437848053)
                  ·
                    refine ⟨857128267158501791048255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142701516357352437848053 857128267158501791048255)
                    ·
                      rfl

theorem cell23_5007754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_5007754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007754 prefixEnd_5007754 := by exact prefixLift 5007754
  have htrace : WordTrace (prefixWord ++ tailWord_5007754) baseStart_5007754 baseEnd_5007754 := by
    simpa [prefixWord, tailWord_5007754, baseEnd_5007754] using wordTrace_append hprefix tailTrace_5007754
  have hstable : (prefixWord ++ tailWord_5007754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007754).length < 2 ^ (prefixWord ++ tailWord_5007754).sum := by decide
  have hdescent : baseEnd_5007754 < baseStart_5007754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007783 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5007783 : Nat := 118140960795 + 5007783 * 2 ^ 59
def prefixEnd_5007783 : Nat := 4983230072969 + 3 ^ 40 * 5007783 * 2
def baseEnd_5007783 : Nat := 2571399692414485759682131

theorem tailTrace_5007783 : CollatzResearch.WordTrace tailWord_5007783 prefixEnd_5007783 2571399692414485759682131 := by
  unfold tailWord_5007783
  simp only [CollatzResearch.WordTrace]
  refine ⟨182648851216664927090684003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121765900811109951393789335 182648851216664927090684003)
  ·
    refine ⟨273973276824997390636026005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182648851216664927090684003 273973276824997390636026005)
    ·
      refine ⟨12842497351171752686063719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 273973276824997390636026005 12842497351171752686063719)
      ·
        refine ⟨19263746026757629029095579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12842497351171752686063719 19263746026757629029095579)
        ·
          refine ⟨28895619040136443543643369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19263746026757629029095579 28895619040136443543643369)
          ·
            refine ⟨21671714280102332657732527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28895619040136443543643369 21671714280102332657732527)
            ·
              refine ⟨32507571420153498986598791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21671714280102332657732527 32507571420153498986598791)
              ·
                refine ⟨48761357130230248479898187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32507571420153498986598791 48761357130230248479898187)
                ·
                  refine ⟨73142035695345372719847281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48761357130230248479898187 73142035695345372719847281)
                  ·
                    refine ⟨54856526771509029539885461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73142035695345372719847281 54856526771509029539885461)
                    ·
                      refine ⟨2571399692414485759682131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54856526771509029539885461 2571399692414485759682131)
                      ·
                        rfl

theorem cell23_5007783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5007783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007783 prefixEnd_5007783 := by exact prefixLift 5007783
  have htrace : WordTrace (prefixWord ++ tailWord_5007783) baseStart_5007783 baseEnd_5007783 := by
    simpa [prefixWord, tailWord_5007783, baseEnd_5007783] using wordTrace_append hprefix tailTrace_5007783
  have hstable : (prefixWord ++ tailWord_5007783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007783).length < 2 ^ (prefixWord ++ tailWord_5007783).sum := by decide
  have hdescent : baseEnd_5007783 < baseStart_5007783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007784 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5007784 : Nat := 118140960795 + 5007784 * 2 ^ 59
def prefixEnd_5007784 : Nat := 4983230072969 + 3 ^ 40 * 5007784 * 2
def baseEnd_5007784 : Nat := 857133401965046751923209

theorem tailTrace_5007784 : CollatzResearch.WordTrace tailWord_5007784 prefixEnd_5007784 857133401965046751923209 := by
  unfold tailWord_5007784
  simp only [CollatzResearch.WordTrace]
  refine ⟨91324443844830652130735203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121765925126440869507646937 91324443844830652130735203)
  ·
    refine ⟨136986665767245978196102805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91324443844830652130735203 136986665767245978196102805)
    ·
      refine ⟨6421249957839655227942319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136986665767245978196102805 6421249957839655227942319)
      ·
        refine ⟨9631874936759482841913479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6421249957839655227942319 9631874936759482841913479)
        ·
          refine ⟨14447812405139224262870219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9631874936759482841913479 14447812405139224262870219)
          ·
            refine ⟨21671718607708836394305329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447812405139224262870219 21671718607708836394305329)
            ·
              refine ⟨16253788955781627295728997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21671718607708836394305329 16253788955781627295728997)
              ·
                refine ⟨3047585429209055117949187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16253788955781627295728997 3047585429209055117949187)
                ·
                  refine ⟨4571378143813582676923781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047585429209055117949187 4571378143813582676923781)
                  ·
                    refine ⟨857133401965046751923209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4571378143813582676923781 857133401965046751923209)
                    ·
                      rfl

theorem cell23_5007784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5007784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007784 prefixEnd_5007784 := by exact prefixLift 5007784
  have htrace : WordTrace (prefixWord ++ tailWord_5007784) baseStart_5007784 baseEnd_5007784 := by
    simpa [prefixWord, tailWord_5007784, baseEnd_5007784] using wordTrace_append hprefix tailTrace_5007784
  have hstable : (prefixWord ++ tailWord_5007784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007784).length < 2 ^ (prefixWord ++ tailWord_5007784).sum := by decide
  have hdescent : baseEnd_5007784 < baseStart_5007784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007797 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 6]
def baseStart_5007797 : Nat := 118140960795 + 5007797 * 2 ^ 59
def prefixEnd_5007797 : Nat := 4983230072969 + 3 ^ 40 * 5007797 * 2
def baseEnd_5007797 : Nat := 285711875682627633878563

theorem tailTrace_5007797 : CollatzResearch.WordTrace tailWord_5007797 prefixEnd_5007797 285711875682627633878563 := by
  unfold tailWord_5007797
  simp only [CollatzResearch.WordTrace]
  refine ⟨182649361838614207481693645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121766241225742804987795763 182649361838614207481693645)
  ·
    refine ⟨68493510689480327805635117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182649361838614207481693645 68493510689480327805635117)
    ·
      refine ⟨25685066508555122927113169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68493510689480327805635117 25685066508555122927113169)
      ·
        refine ⟨19263799881416342195334877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25685066508555122927113169 19263799881416342195334877)
        ·
          refine ⟨7223924955531128323250579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19263799881416342195334877 7223924955531128323250579)
          ·
            refine ⟨10835887433296692484875869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223924955531128323250579 10835887433296692484875869)
            ·
              refine ⟨4063457787486259681828451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10835887433296692484875869 4063457787486259681828451)
              ·
                refine ⟨6095186681229389522742677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063457787486259681828451 6095186681229389522742677)
                ·
                  refine ⟨285711875682627633878563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6095186681229389522742677 285711875682627633878563)
                  ·
                    rfl

theorem cell23_5007797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_5007797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007797 prefixEnd_5007797 := by exact prefixLift 5007797
  have htrace : WordTrace (prefixWord ++ tailWord_5007797) baseStart_5007797 baseEnd_5007797 := by
    simpa [prefixWord, tailWord_5007797, baseEnd_5007797] using wordTrace_append hprefix tailTrace_5007797
  have hstable : (prefixWord ++ tailWord_5007797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007797).length < 2 ^ (prefixWord ++ tailWord_5007797).sum := by decide
  have hdescent : baseEnd_5007797 < baseStart_5007797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007840 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_5007840 : Nat := 118140960795 + 5007840 * 2 ^ 59
def prefixEnd_5007840 : Nat := 4983230072969 + 3 ^ 40 * 5007840 * 2
def baseEnd_5007840 : Nat := 857142986937264012223123

theorem tailTrace_5007840 : CollatzResearch.WordTrace tailWord_5007840 prefixEnd_5007840 857142986937264012223123 := by
  unfold tailWord_5007840
  simp only [CollatzResearch.WordTrace]
  refine ⟨91325465088729212912754487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121767286784972283883672649 91325465088729212912754487)
  ·
    refine ⟨136988197633093819369131731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91325465088729212912754487 136988197633093819369131731)
    ·
      refine ⟨205482296449640729053697597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136988197633093819369131731 205482296449640729053697597)
      ·
        refine ⟨77055861168615273395136599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205482296449640729053697597 77055861168615273395136599)
        ·
          refine ⟨115583791752922910092704899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77055861168615273395136599 115583791752922910092704899)
          ·
            refine ⟨173375687629384365139057349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115583791752922910092704899 173375687629384365139057349)
            ·
              refine ⟨32507941430509568463573253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173375687629384365139057349 32507941430509568463573253)
              ·
                refine ⟨6095239018220544086919985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32507941430509568463573253 6095239018220544086919985)
                ·
                  refine ⟨4571429263665408065189989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6095239018220544086919985 4571429263665408065189989)
                  ·
                    refine ⟨857142986937264012223123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4571429263665408065189989 857142986937264012223123)
                    ·
                      rfl

theorem cell23_5007840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_5007840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007840 prefixEnd_5007840 := by exact prefixLift 5007840
  have htrace : WordTrace (prefixWord ++ tailWord_5007840) baseStart_5007840 baseEnd_5007840 := by
    simpa [prefixWord, tailWord_5007840, baseEnd_5007840] using wordTrace_append hprefix tailTrace_5007840
  have hstable : (prefixWord ++ tailWord_5007840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007840).length < 2 ^ (prefixWord ++ tailWord_5007840).sum := by decide
  have hdescent : baseEnd_5007840 < baseStart_5007840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007850 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_5007850 : Nat := 118140960795 + 5007850 * 2 ^ 59
def prefixEnd_5007850 : Nat := 4983230072969 + 3 ^ 40 * 5007850 * 2
def baseEnd_5007850 : Nat := 2571434095618336997544323

theorem tailTrace_5007850 : CollatzResearch.WordTrace tailWord_5007850 prefixEnd_5007850 2571434095618336997544323 := by
  unfold tailWord_5007850
  simp only [CollatzResearch.WordTrace]
  refine ⟨45662823726855549383343251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121767529938281465022248669 45662823726855549383343251)
  ·
    refine ⟨68494235590283324075014877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45662823726855549383343251 68494235590283324075014877)
    ·
      refine ⟨25685338346356246528130579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68494235590283324075014877 25685338346356246528130579)
      ·
        refine ⟨38528007519534369792195869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25685338346356246528130579 38528007519534369792195869)
        ·
          refine ⟨14448002819825388672073451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38528007519534369792195869 14448002819825388672073451)
          ·
            refine ⟨21672004229738083008110177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14448002819825388672073451 21672004229738083008110177)
            ·
              refine ⟨16254003172303562256082633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21672004229738083008110177 16254003172303562256082633)
              ·
                refine ⟨12190502379227671692061975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16254003172303562256082633 12190502379227671692061975)
                ·
                  refine ⟨18285753568841507538092963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12190502379227671692061975 18285753568841507538092963)
                  ·
                    refine ⟨27428630353262261307139445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18285753568841507538092963 27428630353262261307139445)
                    ·
                      refine ⟨2571434095618336997544323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27428630353262261307139445 2571434095618336997544323)
                      ·
                        rfl

theorem cell23_5007850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_5007850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007850 prefixEnd_5007850 := by exact prefixLift 5007850
  have htrace : WordTrace (prefixWord ++ tailWord_5007850) baseStart_5007850 baseEnd_5007850 := by
    simpa [prefixWord, tailWord_5007850, baseEnd_5007850] using wordTrace_append hprefix tailTrace_5007850
  have hstable : (prefixWord ++ tailWord_5007850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007850).length < 2 ^ (prefixWord ++ tailWord_5007850).sum := by decide
  have hdescent : baseEnd_5007850 < baseStart_5007850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007861 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5007861 : Nat := 118140960795 + 5007861 * 2 ^ 59
def prefixEnd_5007861 : Nat := 4983230072969 + 3 ^ 40 * 5007861 * 2
def baseEnd_5007861 : Nat := 857146581301845484835591

theorem tailTrace_5007861 : CollatzResearch.WordTrace tailWord_5007861 prefixEnd_5007861 857146581301845484835591 := by
  unfold tailWord_5007861
  simp only [CollatzResearch.WordTrace]
  refine ⟨182651696110382346412023437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121767797406921564274682291 182651696110382346412023437)
  ·
    refine ⟨68494386041393379904508789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182651696110382346412023437 68494386041393379904508789)
    ·
      refine ⟨6421348691380629366047699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68494386041393379904508789 6421348691380629366047699)
      ·
        refine ⟨9632023037070944049071549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6421348691380629366047699 9632023037070944049071549)
        ·
          refine ⟨3612008638901604018401831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9632023037070944049071549 3612008638901604018401831)
          ·
            refine ⟨5418012958352406027602747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612008638901604018401831 5418012958352406027602747)
            ·
              refine ⟨8127019437528609041404121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418012958352406027602747 8127019437528609041404121)
              ·
                refine ⟨6095264578146456781053091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8127019437528609041404121 6095264578146456781053091)
                ·
                  refine ⟨9142896867219685171579637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095264578146456781053091 9142896867219685171579637)
                  ·
                    refine ⟨857146581301845484835591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142896867219685171579637 857146581301845484835591)
                    ·
                      rfl

theorem cell23_5007861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5007861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007861 prefixEnd_5007861 := by exact prefixLift 5007861
  have htrace : WordTrace (prefixWord ++ tailWord_5007861) baseStart_5007861 baseEnd_5007861 := by
    simpa [prefixWord, tailWord_5007861, baseEnd_5007861] using wordTrace_append hprefix tailTrace_5007861
  have hstable : (prefixWord ++ tailWord_5007861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007861).length < 2 ^ (prefixWord ++ tailWord_5007861).sum := by decide
  have hdescent : baseEnd_5007861 < baseStart_5007861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007878 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5007878 : Nat := 118140960795 + 5007878 * 2 ^ 59
def prefixEnd_5007878 : Nat := 4983230072969 + 3 ^ 40 * 5007878 * 2
def baseEnd_5007878 : Nat := 857149491025554295998065

theorem tailTrace_5007878 : CollatzResearch.WordTrace tailWord_5007878 prefixEnd_5007878 857149491025554295998065 := by
  unfold tailWord_5007878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707884879728773697356009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121768210767547172210261525 5707884879728773697356009)
  ·
    refine ⟨4280913659796580273017007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5707884879728773697356009 4280913659796580273017007)
    ·
      refine ⟨6421370489694870409525511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280913659796580273017007 6421370489694870409525511)
      ·
        refine ⟨9632055734542305614288267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6421370489694870409525511 9632055734542305614288267)
        ·
          refine ⟨14448083601813458421432401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632055734542305614288267 14448083601813458421432401)
          ·
            refine ⟨10836062701360093816074301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14448083601813458421432401 10836062701360093816074301)
            ·
              refine ⟨4063523513010035181027863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10836062701360093816074301 4063523513010035181027863)
              ·
                refine ⟨6095285269515052771541795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063523513010035181027863 6095285269515052771541795)
                ·
                  refine ⟨9142927904272579157312693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095285269515052771541795 9142927904272579157312693)
                  ·
                    refine ⟨857149491025554295998065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142927904272579157312693 857149491025554295998065)
                    ·
                      rfl

theorem cell23_5007878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5007878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007878 prefixEnd_5007878 := by exact prefixLift 5007878
  have htrace : WordTrace (prefixWord ++ tailWord_5007878) baseStart_5007878 baseEnd_5007878 := by
    simpa [prefixWord, tailWord_5007878, baseEnd_5007878] using wordTrace_append hprefix tailTrace_5007878
  have hstable : (prefixWord ++ tailWord_5007878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007878).length < 2 ^ (prefixWord ++ tailWord_5007878).sum := by decide
  have hdescent : baseEnd_5007878 < baseStart_5007878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007884 : List Nat := [2, 2, 1, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_5007884 : Nat := 118140960795 + 5007884 * 2 ^ 59
def prefixEnd_5007884 : Nat := 4983230072969 + 3 ^ 40 * 5007884 * 2
def baseEnd_5007884 : Nat := 2571451553960589864519167

theorem tailTrace_5007884 : CollatzResearch.WordTrace tailWord_5007884 prefixEnd_5007884 2571451553960589864519167 := by
  unfold tailWord_5007884
  simp only [CollatzResearch.WordTrace]
  refine ⟨91326267494649510670055353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121768356659532680893407137 91326267494649510670055353)
  ·
    refine ⟨68494700620987133002541515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91326267494649510670055353 68494700620987133002541515)
    ·
      refine ⟨102742050931480699503812273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68494700620987133002541515 102742050931480699503812273)
      ·
        refine ⟨77056538198610524627859205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102742050931480699503812273 77056538198610524627859205)
        ·
          refine ⟨14448100912239473367723601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77056538198610524627859205 14448100912239473367723601)
          ·
            refine ⟨10836075684179605025792701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14448100912239473367723601 10836075684179605025792701)
            ·
              refine ⟨4063528381567351884672263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10836075684179605025792701 4063528381567351884672263)
              ·
                refine ⟨6095292572351027827008395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063528381567351884672263 6095292572351027827008395)
                ·
                  refine ⟨9142938858526541740512593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095292572351027827008395 9142938858526541740512593)
                  ·
                    refine ⟨6857204143894906305384445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9142938858526541740512593 6857204143894906305384445)
                    ·
                      refine ⟨2571451553960589864519167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857204143894906305384445 2571451553960589864519167)
                      ·
                        rfl

theorem cell23_5007884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_5007884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007884 prefixEnd_5007884 := by exact prefixLift 5007884
  have htrace : WordTrace (prefixWord ++ tailWord_5007884) baseStart_5007884 baseEnd_5007884 := by
    simpa [prefixWord, tailWord_5007884, baseEnd_5007884] using wordTrace_append hprefix tailTrace_5007884
  have hstable : (prefixWord ++ tailWord_5007884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007884).length < 2 ^ (prefixWord ++ tailWord_5007884).sum := by decide
  have hdescent : baseEnd_5007884 < baseStart_5007884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007907 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 3, 3, 2]
def baseStart_5007907 : Nat := 118140960795 + 5007907 * 2 ^ 59
def prefixEnd_5007907 : Nat := 4983230072969 + 3 ^ 40 * 5007907 * 2
def baseEnd_5007907 : Nat := 2571463364015643274531561

theorem tailTrace_5007907 : CollatzResearch.WordTrace tailWord_5007907 prefixEnd_5007907 2571463364015643274531561 := by
  unfold tailWord_5007907
  simp only [CollatzResearch.WordTrace]
  refine ⟨182653373868215696268197975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121768915912143797512131983 182653373868215696268197975)
  ·
    refine ⟨273980060802323544402296963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182653373868215696268197975 273980060802323544402296963)
    ·
      refine ⟨410970091203485316603445445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273980060802323544402296963 410970091203485316603445445)
      ·
        refine ⟨77056892100653496863146021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410970091203485316603445445 77056892100653496863146021)
        ·
          refine ⟨14448167268872530661839879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77056892100653496863146021 14448167268872530661839879)
          ·
            refine ⟨21672250903308795992759819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14448167268872530661839879 21672250903308795992759819)
            ·
              refine ⟨32508376354963193989139729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21672250903308795992759819 32508376354963193989139729)
              ·
                refine ⟨24381282266222395491854797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32508376354963193989139729 24381282266222395491854797)
                ·
                  refine ⟨9142980849833398309445549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24381282266222395491854797 9142980849833398309445549)
                  ·
                    refine ⟨3428617818687524366042081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9142980849833398309445549 3428617818687524366042081)
                    ·
                      refine ⟨2571463364015643274531561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428617818687524366042081 2571463364015643274531561)
                      ·
                        rfl

theorem cell23_5007907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_5007907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007907 prefixEnd_5007907 := by exact prefixLift 5007907
  have htrace : WordTrace (prefixWord ++ tailWord_5007907) baseStart_5007907 baseEnd_5007907 := by
    simpa [prefixWord, tailWord_5007907, baseEnd_5007907] using wordTrace_append hprefix tailTrace_5007907
  have hstable : (prefixWord ++ tailWord_5007907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007907).length < 2 ^ (prefixWord ++ tailWord_5007907).sum := by decide
  have hdescent : baseEnd_5007907 < baseStart_5007907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007914 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_5007914 : Nat := 118140960795 + 5007914 * 2 ^ 59
def prefixEnd_5007914 : Nat := 4983230072969 + 3 ^ 40 * 5007914 * 2
def baseEnd_5007914 : Nat := 2571466958380224747144029

theorem tailTrace_5007914 : CollatzResearch.WordTrace tailWord_5007914 prefixEnd_5007914 2571466958380224747144029 := by
  unfold tailWord_5007914
  simp only [CollatzResearch.WordTrace]
  refine ⟨45663407294797584115925699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121769086119460224309135197 45663407294797584115925699)
  ·
    refine ⟨68495110942196376173888549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45663407294797584115925699 68495110942196376173888549)
    ·
      refine ⟨12842833301661820532604103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68495110942196376173888549 12842833301661820532604103)
      ·
        refine ⟨19264249952492730798906155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12842833301661820532604103 19264249952492730798906155)
        ·
          refine ⟨28896374928739096198359233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19264249952492730798906155 28896374928739096198359233)
          ·
            refine ⟨21672281196554322148769425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28896374928739096198359233 21672281196554322148769425)
            ·
              refine ⟨16254210897415741611577069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21672281196554322148769425 16254210897415741611577069)
              ·
                refine ⟨6095329086530903104341401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16254210897415741611577069 6095329086530903104341401)
                ·
                  refine ⟨4571496814898177328256051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6095329086530903104341401 4571496814898177328256051)
                  ·
                    refine ⟨6857245222347265992384077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571496814898177328256051 6857245222347265992384077)
                    ·
                      refine ⟨2571466958380224747144029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857245222347265992384077 2571466958380224747144029)
                      ·
                        rfl

theorem cell23_5007914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_5007914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007914 prefixEnd_5007914 := by exact prefixLift 5007914
  have htrace : WordTrace (prefixWord ++ tailWord_5007914) baseStart_5007914 baseEnd_5007914 := by
    simpa [prefixWord, tailWord_5007914, baseEnd_5007914] using wordTrace_append hprefix tailTrace_5007914
  have hstable : (prefixWord ++ tailWord_5007914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007914).length < 2 ^ (prefixWord ++ tailWord_5007914).sum := by decide
  have hdescent : baseEnd_5007914 < baseStart_5007914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007941 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_5007941 : Nat := 118140960795 + 5007941 * 2 ^ 59
def prefixEnd_5007941 : Nat := 4983230072969 + 3 ^ 40 * 5007941 * 2
def baseEnd_5007941 : Nat := 2571480822357896141506405

theorem tailTrace_5007941 : CollatzResearch.WordTrace tailWord_5007941 prefixEnd_5007941 2571480822357896141506405 := by
  unfold tailWord_5007941
  simp only [CollatzResearch.WordTrace]
  refine ⟨182654613950092520074935677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121769742633395013383290451 182654613950092520074935677)
  ·
    refine ⟨68495480231284695028100879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182654613950092520074935677 68495480231284695028100879)
    ·
      refine ⟨102743220346927042542151319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68495480231284695028100879 102743220346927042542151319)
      ·
        refine ⟨154114830520390563813226979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102743220346927042542151319 154114830520390563813226979)
        ·
          refine ⟨231172245780585845719840469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154114830520390563813226979 231172245780585845719840469)
          ·
            refine ⟨5418099510482480759058761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 231172245780585845719840469 5418099510482480759058761)
            ·
              refine ⟨4063574632861860569294071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418099510482480759058761 4063574632861860569294071)
              ·
                refine ⟨6095361949292790853941107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063574632861860569294071 6095361949292790853941107)
                ·
                  refine ⟨9143042923939186280911661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095361949292790853941107 9143042923939186280911661)
                  ·
                    refine ⟨3428641096477194855341873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9143042923939186280911661 3428641096477194855341873)
                    ·
                      refine ⟨2571480822357896141506405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428641096477194855341873 2571480822357896141506405)
                      ·
                        rfl

theorem cell23_5007941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_5007941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007941 prefixEnd_5007941 := by exact prefixLift 5007941
  have htrace : WordTrace (prefixWord ++ tailWord_5007941) baseStart_5007941 baseEnd_5007941 := by
    simpa [prefixWord, tailWord_5007941, baseEnd_5007941] using wordTrace_append hprefix tailTrace_5007941
  have hstable : (prefixWord ++ tailWord_5007941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007941).length < 2 ^ (prefixWord ++ tailWord_5007941).sum := by decide
  have hdescent : baseEnd_5007941 < baseStart_5007941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007950 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_5007950 : Nat := 118140960795 + 5007950 * 2 ^ 59
def prefixEnd_5007950 : Nat := 4983230072969 + 3 ^ 40 * 5007950 * 2
def baseEnd_5007950 : Nat := 2571485443683786606293863

theorem tailTrace_5007950 : CollatzResearch.WordTrace tailWord_5007950 prefixEnd_5007950 2571485443683786606293863 := by
  unfold tailWord_5007950
  simp only [CollatzResearch.WordTrace]
  refine ⟨22831867775882489326501663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121769961471373276408008869 22831867775882489326501663)
  ·
    refine ⟨34247801663823733989752495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22831867775882489326501663 34247801663823733989752495)
    ·
      refine ⟨51371702495735600984628743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34247801663823733989752495 51371702495735600984628743)
      ·
        refine ⟨77057553743603401476943115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51371702495735600984628743 77057553743603401476943115)
        ·
          refine ⟨115586330615405102215414673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77057553743603401476943115 115586330615405102215414673)
          ·
            refine ⟨86689747961553826661561005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115586330615405102215414673 86689747961553826661561005)
            ·
              refine ⟨32508655485582684998085377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86689747961553826661561005 32508655485582684998085377)
              ·
                refine ⟨24381491614187013748564033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32508655485582684998085377 24381491614187013748564033)
                ·
                  refine ⟨18286118710640260311423025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24381491614187013748564033 18286118710640260311423025)
                  ·
                    refine ⟨13714589032980195233567269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18286118710640260311423025 13714589032980195233567269)
                    ·
                      refine ⟨2571485443683786606293863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13714589032980195233567269 2571485443683786606293863)
                      ·
                        rfl

theorem cell23_5007950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_5007950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007950 prefixEnd_5007950 := by exact prefixLift 5007950
  have htrace : WordTrace (prefixWord ++ tailWord_5007950) baseStart_5007950 baseEnd_5007950 := by
    simpa [prefixWord, tailWord_5007950, baseEnd_5007950] using wordTrace_append hprefix tailTrace_5007950
  have hstable : (prefixWord ++ tailWord_5007950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007950).length < 2 ^ (prefixWord ++ tailWord_5007950).sum := by decide
  have hdescent : baseEnd_5007950 < baseStart_5007950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007954 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_5007954 : Nat := 118140960795 + 5007954 * 2 ^ 59
def prefixEnd_5007954 : Nat := 4983230072969 + 3 ^ 40 * 5007954 * 2
def baseEnd_5007954 : Nat := 2571487497606404590643845

theorem tailTrace_5007954 : CollatzResearch.WordTrace tailWord_5007954 prefixEnd_5007954 2571487497606404590643845 := by
  unfold tailWord_5007954
  simp only [CollatzResearch.WordTrace]
  refine ⟨45663772024761355823789729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121770058732696948863439277 45663772024761355823789729)
  ·
    refine ⟨34247829018571016867842297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45663772024761355823789729 34247829018571016867842297)
    ·
      refine ⟨25685871763928262650881723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34247829018571016867842297 25685871763928262650881723)
      ·
        refine ⟨38528807645892393976322585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25685871763928262650881723 38528807645892393976322585)
        ·
          refine ⟨28896605734419295482241939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38528807645892393976322585 28896605734419295482241939)
          ·
            refine ⟨43344908601628943223362909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28896605734419295482241939 43344908601628943223362909)
            ·
              refine ⟨16254340725610853708761091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43344908601628943223362909 16254340725610853708761091)
              ·
                refine ⟨24381511088416280563141637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16254340725610853708761091 24381511088416280563141637)
                ·
                  refine ⟨4571533329078052605589057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24381511088416280563141637 4571533329078052605589057)
                  ·
                    refine ⟨3428649996808539454191793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571533329078052605589057 3428649996808539454191793)
                    ·
                      refine ⟨2571487497606404590643845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428649996808539454191793 2571487497606404590643845)
                      ·
                        rfl

theorem cell23_5007954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_5007954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007954 prefixEnd_5007954 := by exact prefixLift 5007954
  have htrace : WordTrace (prefixWord ++ tailWord_5007954) baseStart_5007954 baseEnd_5007954 := by
    simpa [prefixWord, tailWord_5007954, baseEnd_5007954] using wordTrace_append hprefix tailTrace_5007954
  have hstable : (prefixWord ++ tailWord_5007954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007954).length < 2 ^ (prefixWord ++ tailWord_5007954).sum := by decide
  have hdescent : baseEnd_5007954 < baseStart_5007954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5007971 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 2, 2, 2]
def baseStart_5007971 : Nat := 118140960795 + 5007971 * 2 ^ 59
def prefixEnd_5007971 : Nat := 4983230072969 + 3 ^ 40 * 5007971 * 2
def baseEnd_5007971 : Nat := 2571496226777531024131267

theorem tailTrace_5007971 : CollatzResearch.WordTrace tailWord_5007971 prefixEnd_5007971 2571496226777531024131267 := by
  unfold tailWord_5007971
  simp only [CollatzResearch.WordTrace]
  refine ⟨182655708139983835198527767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121770472093322556799018511 182655708139983835198527767)
  ·
    refine ⟨273983562209975752797791651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182655708139983835198527767 273983562209975752797791651)
    ·
      refine ⟨410975343314963629196687477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273983562209975752797791651 410975343314963629196687477)
      ·
        refine ⟨38528938435777840237189451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 410975343314963629196687477 38528938435777840237189451)
        ·
          refine ⟨57793407653666760355784177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38528938435777840237189451 57793407653666760355784177)
          ·
            refine ⟨43345055740250070266838133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57793407653666760355784177 43345055740250070266838133)
            ·
              refine ⟨4063598975648444087516075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43345055740250070266838133 4063598975648444087516075)
              ·
                refine ⟨6095398463472666131274113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063598975648444087516075 6095398463472666131274113)
                ·
                  refine ⟨4571548847604499598455585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6095398463472666131274113 4571548847604499598455585)
                  ·
                    refine ⟨3428661635703374698841689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571548847604499598455585 3428661635703374698841689)
                    ·
                      refine ⟨2571496226777531024131267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428661635703374698841689 2571496226777531024131267)
                      ·
                        rfl

theorem cell23_5007971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_5007971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5007971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5007971 prefixEnd_5007971 := by exact prefixLift 5007971
  have htrace : WordTrace (prefixWord ++ tailWord_5007971) baseStart_5007971 baseEnd_5007971 := by
    simpa [prefixWord, tailWord_5007971, baseEnd_5007971] using wordTrace_append hprefix tailTrace_5007971
  have hstable : (prefixWord ++ tailWord_5007971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5007971).length < 2 ^ (prefixWord ++ tailWord_5007971).sum := by decide
  have hdescent : baseEnd_5007971 < baseStart_5007971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5007971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008047 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_5008047 : Nat := 118140960795 + 5008047 * 2 ^ 59
def prefixEnd_5008047 : Nat := 4983230072969 + 3 ^ 40 * 5008047 * 2
def baseEnd_5008047 : Nat := 2571535251307272726780917

theorem tailTrace_5008047 : CollatzResearch.WordTrace tailWord_5008047 prefixEnd_5008047 2571535251307272726780917 := by
  unfold tailWord_5008047
  simp only [CollatzResearch.WordTrace]
  refine ⟨182658480087708500178294395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121772320058472333452196263 182658480087708500178294395)
  ·
    refine ⟨273987720131562750267441593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182658480087708500178294395 273987720131562750267441593)
    ·
      refine ⟨205490790098672062700581195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273987720131562750267441593 205490790098672062700581195)
      ·
        refine ⟨308236185148008094050871793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205490790098672062700581195 308236185148008094050871793)
        ·
          refine ⟨231177138861006070538153845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308236185148008094050871793 231177138861006070538153845)
          ·
            refine ⟨21672856768219319112951923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231177138861006070538153845 21672856768219319112951923)
            ·
              refine ⟨32509285152328978669427885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21672856768219319112951923 32509285152328978669427885)
              ·
                refine ⟨12190981932123367001035457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32509285152328978669427885 12190981932123367001035457)
                ·
                  refine ⟨9143236449092525250776593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12190981932123367001035457 9143236449092525250776593)
                  ·
                    refine ⟨6857427336819393938082445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9143236449092525250776593 6857427336819393938082445)
                    ·
                      refine ⟨2571535251307272726780917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857427336819393938082445 2571535251307272726780917)
                      ·
                        rfl

theorem cell23_5008047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_5008047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008047 prefixEnd_5008047 := by exact prefixLift 5008047
  have htrace : WordTrace (prefixWord ++ tailWord_5008047) baseStart_5008047 baseEnd_5008047 := by
    simpa [prefixWord, tailWord_5008047, baseEnd_5008047] using wordTrace_append hprefix tailTrace_5008047
  have hstable : (prefixWord ++ tailWord_5008047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008047).length < 2 ^ (prefixWord ++ tailWord_5008047).sum := by decide
  have hdescent : baseEnd_5008047 < baseStart_5008047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008090 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_5008090 : Nat := 118140960795 + 5008090 * 2 ^ 59
def prefixEnd_5008090 : Nat := 4983230072969 + 3 ^ 40 * 5008090 * 2
def baseEnd_5008090 : Nat := 2571557330975416058543219

theorem tailTrace_5008090 : CollatzResearch.WordTrace tailWord_5008090 prefixEnd_5008090 2571557330975416058543219 := by
  unfold tailWord_5008090
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665012106638179630527431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121773365617701812348073149 45665012106638179630527431)
  ·
    refine ⟨68497518159957269445791147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45665012106638179630527431 68497518159957269445791147)
    ·
      refine ⟨102746277239935904168686721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68497518159957269445791147 102746277239935904168686721)
      ·
        refine ⟨77059707929951928126515041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102746277239935904168686721 77059707929951928126515041)
        ·
          refine ⟨57794780947463946094886281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77059707929951928126515041 57794780947463946094886281)
          ·
            refine ⟨43346085710597959571164711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57794780947463946094886281 43346085710597959571164711)
            ·
              refine ⟨65019128565896939356747067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43346085710597959571164711 65019128565896939356747067)
              ·
                refine ⟨97528692848845409035120601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65019128565896939356747067 97528692848845409035120601)
                ·
                  refine ⟨73146519636634056776340451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97528692848845409035120601 73146519636634056776340451)
                  ·
                    refine ⟨109719779454951085164510677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73146519636634056776340451 109719779454951085164510677)
                    ·
                      refine ⟨2571557330975416058543219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109719779454951085164510677 2571557330975416058543219)
                      ·
                        rfl

theorem cell23_5008090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_5008090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008090 prefixEnd_5008090 := by exact prefixLift 5008090
  have htrace : WordTrace (prefixWord ++ tailWord_5008090) baseStart_5008090 baseEnd_5008090 := by
    simpa [prefixWord, tailWord_5008090, baseEnd_5008090] using wordTrace_append hprefix tailTrace_5008090
  have hstable : (prefixWord ++ tailWord_5008090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008090).length < 2 ^ (prefixWord ++ tailWord_5008090).sum := by decide
  have hdescent : baseEnd_5008090 < baseStart_5008090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008097 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_5008097 : Nat := 118140960795 + 5008097 * 2 ^ 59
def prefixEnd_5008097 : Nat := 4983230072969 + 3 ^ 40 * 5008097 * 2
def baseEnd_5008097 : Nat := 857186975113332510385229

theorem tailTrace_5008097 : CollatzResearch.WordTrace tailWord_5008097 prefixEnd_5008097 857186975113332510385229 := by
  unfold tailWord_5008097
  simp only [CollatzResearch.WordTrace]
  refine ⟨182660303737527358717614545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121773535825018239145076363 182660303737527358717614545)
  ·
    refine ⟨136995227803145519038210909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182660303737527358717614545 136995227803145519038210909)
    ·
      refine ⟨51373210426179569639329091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136995227803145519038210909 51373210426179569639329091)
      ·
        refine ⟨77059815639269354458993637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51373210426179569639329091 77059815639269354458993637)
        ·
          refine ⟨14448715432363003961061307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77059815639269354458993637 14448715432363003961061307)
          ·
            refine ⟨21673073148544505941591961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14448715432363003961061307 21673073148544505941591961)
            ·
              refine ⟨16254804861408379456193971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21673073148544505941591961 16254804861408379456193971)
              ·
                refine ⟨24382207292112569184290957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16254804861408379456193971 24382207292112569184290957)
                ·
                  refine ⟨9143327734542213444109109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24382207292112569184290957 9143327734542213444109109)
                  ·
                    refine ⟨857186975113332510385229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9143327734542213444109109 857186975113332510385229)
                    ·
                      rfl

theorem cell23_5008097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_5008097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008097 prefixEnd_5008097 := by exact prefixLift 5008097
  have htrace : WordTrace (prefixWord ++ tailWord_5008097) baseStart_5008097 baseEnd_5008097 := by
    simpa [prefixWord, tailWord_5008097, baseEnd_5008097] using wordTrace_append hprefix tailTrace_5008097
  have hstable : (prefixWord ++ tailWord_5008097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008097).length < 2 ^ (prefixWord ++ tailWord_5008097).sum := by decide
  have hdescent : baseEnd_5008097 < baseStart_5008097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008111 : List Nat := [1, 1, 2, 1, 5, 2, 1, 5, 1, 1, 3]
def baseStart_5008111 : Nat := 118140960795 + 5008111 * 2 ^ 59
def prefixEnd_5008111 : Nat := 4983230072969 + 3 ^ 40 * 5008111 * 2
def baseEnd_5008111 : Nat := 2571568114069160476380623

theorem tailTrace_5008111 : CollatzResearch.WordTrace tailWord_5008111 prefixEnd_5008111 2571568114069160476380623 := by
  unfold tailWord_5008111
  simp only [CollatzResearch.WordTrace]
  refine ⟨182660814359476639108624187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121773876239651092739082791 182660814359476639108624187)
  ·
    refine ⟨273991221539214958662936281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182660814359476639108624187 273991221539214958662936281)
    ·
      refine ⟨205493416154411218997202211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273991221539214958662936281 205493416154411218997202211)
      ·
        refine ⟨308240124231616828495803317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205493416154411218997202211 308240124231616828495803317)
        ·
          refine ⟨28897511646714077671481561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308240124231616828495803317 28897511646714077671481561)
          ·
            refine ⟨21673133735035558253611171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28897511646714077671481561 21673133735035558253611171)
            ·
              refine ⟨32509700602553337380416757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21673133735035558253611171 32509700602553337380416757)
              ·
                refine ⟨3047784431489375379414071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32509700602553337380416757 3047784431489375379414071)
                ·
                  refine ⟨4571676647234063069121107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047784431489375379414071 4571676647234063069121107)
                  ·
                    refine ⟨6857514970851094603681661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571676647234063069121107 6857514970851094603681661)
                    ·
                      refine ⟨2571568114069160476380623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857514970851094603681661 2571568114069160476380623)
                      ·
                        rfl

theorem cell23_5008111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 5, 1, 1, 3].length) (baseStart_5008111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008111 prefixEnd_5008111 := by exact prefixLift 5008111
  have htrace : WordTrace (prefixWord ++ tailWord_5008111) baseStart_5008111 baseEnd_5008111 := by
    simpa [prefixWord, tailWord_5008111, baseEnd_5008111] using wordTrace_append hprefix tailTrace_5008111
  have hstable : (prefixWord ++ tailWord_5008111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008111).length < 2 ^ (prefixWord ++ tailWord_5008111).sum := by decide
  have hdescent : baseEnd_5008111 < baseStart_5008111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008114 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_5008114 : Nat := 118140960795 + 5008114 * 2 ^ 59
def prefixEnd_5008114 : Nat := 4983230072969 + 3 ^ 40 * 5008114 * 2
def baseEnd_5008114 : Nat := 857189884837041321547703

theorem tailTrace_5008114 : CollatzResearch.WordTrace tailWord_5008114 prefixEnd_5008114 857189884837041321547703 := by
  unfold tailWord_5008114
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665230944616442655245849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121773949185643847080655597 45665230944616442655245849)
  ·
    refine ⟨34248923208462331991434387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45665230944616442655245849 34248923208462331991434387)
    ·
      refine ⟨51373384812693497987151581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34248923208462331991434387 51373384812693497987151581)
      ·
        refine ⟨19265019304760061745181843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51373384812693497987151581 19265019304760061745181843)
        ·
          refine ⟨28897528957140092617772765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19265019304760061745181843 28897528957140092617772765)
          ·
            refine ⟨10836573358927534731664787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28897528957140092617772765 10836573358927534731664787)
            ·
              refine ⟨16254860038391302097497181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836573358927534731664787 16254860038391302097497181)
              ·
                refine ⟨6095572514396738286561443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16254860038391302097497181 6095572514396738286561443)
                ·
                  refine ⟨9143358771595107429842165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095572514396738286561443 9143358771595107429842165)
                  ·
                    refine ⟨857189884837041321547703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9143358771595107429842165 857189884837041321547703)
                    ·
                      rfl

theorem cell23_5008114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_5008114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008114 prefixEnd_5008114 := by exact prefixLift 5008114
  have htrace : WordTrace (prefixWord ++ tailWord_5008114) baseStart_5008114 baseEnd_5008114 := by
    simpa [prefixWord, tailWord_5008114, baseEnd_5008114] using wordTrace_append hprefix tailTrace_5008114
  have hstable : (prefixWord ++ tailWord_5008114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008114).length < 2 ^ (prefixWord ++ tailWord_5008114).sum := by decide
  have hdescent : baseEnd_5008114 < baseStart_5008114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008137 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 3]
def baseStart_5008137 : Nat := 118140960795 + 5008137 * 2 ^ 59
def prefixEnd_5008137 : Nat := 4983230072969 + 3 ^ 40 * 5008137 * 2
def baseEnd_5008137 : Nat := 2571581464566177374655503

theorem tailTrace_5008137 : CollatzResearch.WordTrace tailWord_5008137 prefixEnd_5008137 2571581464566177374655503 := by
  unfold tailWord_5008137
  simp only [CollatzResearch.WordTrace]
  refine ⟨182661762657382445549070665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121774508438254963699380443 182661762657382445549070665)
  ·
    refine ⟨136996321993036834161802999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182661762657382445549070665 136996321993036834161802999)
    ·
      refine ⟨205494482989555251242704499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136996321993036834161802999 205494482989555251242704499)
      ·
        refine ⟨308241724484332876864056749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205494482989555251242704499 308241724484332876864056749)
        ·
          refine ⟨115590646681624828824021281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308241724484332876864056749 115590646681624828824021281)
          ·
            refine ⟨86692985011218621618015961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115590646681624828824021281 86692985011218621618015961)
            ·
              refine ⟨65019738758413966213511971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86692985011218621618015961 65019738758413966213511971)
              ·
                refine ⟨97529608137620949320267957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65019738758413966213511971 97529608137620949320267957)
                ·
                  refine ⟨9143400762901963998775121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97529608137620949320267957 9143400762901963998775121)
                  ·
                    refine ⟨6857550572176472999081341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9143400762901963998775121 6857550572176472999081341)
                    ·
                      refine ⟨2571581464566177374655503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857550572176472999081341 2571581464566177374655503)
                      ·
                        rfl

theorem cell23_5008137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_5008137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008137 prefixEnd_5008137 := by exact prefixLift 5008137
  have htrace : WordTrace (prefixWord ++ tailWord_5008137) baseStart_5008137 baseEnd_5008137 := by
    simpa [prefixWord, tailWord_5008137, baseEnd_5008137] using wordTrace_append hprefix tailTrace_5008137
  have hstable : (prefixWord ++ tailWord_5008137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008137).length < 2 ^ (prefixWord ++ tailWord_5008137).sum := by decide
  have hdescent : baseEnd_5008137 < baseStart_5008137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008140 : List Nat := [2, 2, 1, 2, 2, 1, 1, 12]
def baseStart_5008140 : Nat := 118140960795 + 5008140 * 2 ^ 59
def prefixEnd_5008140 : Nat := 4983230072969 + 3 ^ 40 * 5008140 * 2
def baseEnd_5008140 : Nat := 95243815000301513441407

theorem tailTrace_5008140 : CollatzResearch.WordTrace tailWord_5008140 prefixEnd_5008140 95243815000301513441407 := by
  unfold tailWord_5008140
  simp only [CollatzResearch.WordTrace]
  refine ⟨91330936038185788530714937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121774581384247718040953249 91330936038185788530714937)
  ·
    refine ⟨68498202028639341398036203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91330936038185788530714937 68498202028639341398036203)
    ·
      refine ⟨102747303042959012097054305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68498202028639341398036203 102747303042959012097054305)
      ·
        refine ⟨77060477282219259072790729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102747303042959012097054305 77060477282219259072790729)
        ·
          refine ⟨57795357961664444304593047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77060477282219259072790729 57795357961664444304593047)
          ·
            refine ⟨86693036942496666456889571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57795357961664444304593047 86693036942496666456889571)
            ·
              refine ⟨130039555413744999685334357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86693036942496666456889571 130039555413744999685334357)
              ·
                refine ⟨95243815000301513441407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 130039555413744999685334357 95243815000301513441407)
                ·
                  rfl

theorem cell23_5008140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 12].length) (baseStart_5008140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008140 prefixEnd_5008140 := by exact prefixLift 5008140
  have htrace : WordTrace (prefixWord ++ tailWord_5008140) baseStart_5008140 baseEnd_5008140 := by
    simpa [prefixWord, tailWord_5008140, baseEnd_5008140] using wordTrace_append hprefix tailTrace_5008140
  have hstable : (prefixWord ++ tailWord_5008140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008140).length < 2 ^ (prefixWord ++ tailWord_5008140).sum := by decide
  have hdescent : baseEnd_5008140 < baseStart_5008140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008151 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5008151 : Nat := 118140960795 + 5008151 * 2 ^ 59
def prefixEnd_5008151 : Nat := 4983230072969 + 3 ^ 40 * 5008151 * 2
def baseEnd_5008151 : Nat := 2571588653295340319880439

theorem tailTrace_5008151 : CollatzResearch.WordTrace tailWord_5008151 prefixEnd_5008151 2571588653295340319880439 := by
  unfold tailWord_5008151
  simp only [CollatzResearch.WordTrace]
  refine ⟨182662273279331725940080307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121774848852887817293386871 182662273279331725940080307)
  ·
    refine ⟨273993409918997588910120461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182662273279331725940080307 273993409918997588910120461)
    ·
      refine ⟨102747528719624095841295173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273993409918997588910120461 102747528719624095841295173)
      ·
        refine ⟨19265161634929517970242845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102747528719624095841295173 19265161634929517970242845)
        ·
          refine ⟨7224435613098569238841067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19265161634929517970242845 7224435613098569238841067)
          ·
            refine ⟨10836653419647853858261601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7224435613098569238841067 10836653419647853858261601)
            ·
              refine ⟨8127490064735890393696201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10836653419647853858261601 8127490064735890393696201)
              ·
                refine ⟨6095617548551917795272151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8127490064735890393696201 6095617548551917795272151)
                ·
                  refine ⟨9143426322827876692908227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095617548551917795272151 9143426322827876692908227)
                  ·
                    refine ⟨13715139484241815039362341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9143426322827876692908227 13715139484241815039362341)
                    ·
                      refine ⟨2571588653295340319880439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13715139484241815039362341 2571588653295340319880439)
                      ·
                        rfl

theorem cell23_5008151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5008151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008151 prefixEnd_5008151 := by exact prefixLift 5008151
  have htrace : WordTrace (prefixWord ++ tailWord_5008151) baseStart_5008151 baseEnd_5008151 := by
    simpa [prefixWord, tailWord_5008151, baseEnd_5008151] using wordTrace_append hprefix tailTrace_5008151
  have hstable : (prefixWord ++ tailWord_5008151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008151).length < 2 ^ (prefixWord ++ tailWord_5008151).sum := by decide
  have hdescent : baseEnd_5008151 < baseStart_5008151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008174 : List Nat := [4, 1, 3, 2, 1, 3, 9]
def baseStart_5008174 : Nat := 118140960795 + 5008174 * 2 ^ 59
def prefixEnd_5008174 : Nat := 4983230072969 + 3 ^ 40 * 5008174 * 2
def baseEnd_5008174 : Nat := 31748153868523379381393

theorem tailTrace_5008174 : CollatzResearch.WordTrace tailWord_5008174 prefixEnd_5008174 31748153868523379381393 := by
  unfold tailWord_5008174
  simp only [CollatzResearch.WordTrace]
  refine ⟨22832889019781050108520947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121775408105498933912111717 22832889019781050108520947)
  ·
    refine ⟨34249333529671575162781421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22832889019781050108520947 34249333529671575162781421)
    ·
      refine ⟨12843500073626840686043033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34249333529671575162781421 12843500073626840686043033)
      ·
        refine ⟨9632625055220130514532275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12843500073626840686043033 9632625055220130514532275)
        ·
          refine ⟨14448937582830195771798413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632625055220130514532275 14448937582830195771798413)
          ·
            refine ⟨5418351593561323414424405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14448937582830195771798413 5418351593561323414424405)
            ·
              refine ⟨31748153868523379381393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5418351593561323414424405 31748153868523379381393)
              ·
                rfl

theorem cell23_5008174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 9].length) (baseStart_5008174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008174 prefixEnd_5008174 := by exact prefixLift 5008174
  have htrace : WordTrace (prefixWord ++ tailWord_5008174) baseStart_5008174 baseEnd_5008174 := by
    simpa [prefixWord, tailWord_5008174, baseEnd_5008174] using wordTrace_append hprefix tailTrace_5008174
  have hstable : (prefixWord ++ tailWord_5008174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008174).length < 2 ^ (prefixWord ++ tailWord_5008174).sum := by decide
  have hdescent : baseEnd_5008174 < baseStart_5008174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008184 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_5008184 : Nat := 118140960795 + 5008184 * 2 ^ 59
def prefixEnd_5008184 : Nat := 4983230072969 + 3 ^ 40 * 5008184 * 2
def baseEnd_5008184 : Nat := 2571605598156938690767787

theorem tailTrace_5008184 : CollatzResearch.WordTrace tailWord_5008184 prefixEnd_5008184 2571605598156938690767787 := by
  unfold tailWord_5008184
  simp only [CollatzResearch.WordTrace]
  refine ⟨91331738444106086288015803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121775651258808115050687737 91331738444106086288015803)
  ·
    refine ⟨136997607666159129432023705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91331738444106086288015803 136997607666159129432023705)
    ·
      refine ⟨102748205749619347074017779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136997607666159129432023705 102748205749619347074017779)
      ·
        refine ⟨154122308624429020611026669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102748205749619347074017779 154122308624429020611026669)
        ·
          refine ⟨57795865734160882729135001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154122308624429020611026669 57795865734160882729135001)
          ·
            refine ⟨43346899300620662046851251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57795865734160882729135001 43346899300620662046851251)
            ·
              refine ⟨65020348950930993070276877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43346899300620662046851251 65020348950930993070276877)
              ·
                refine ⟨24382630856599122401353829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65020348950930993070276877 24382630856599122401353829)
                ·
                  refine ⟨4571743285612335450253843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24382630856599122401353829 4571743285612335450253843)
                  ·
                    refine ⟨6857614928418503175380765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571743285612335450253843 6857614928418503175380765)
                    ·
                      refine ⟨2571605598156938690767787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857614928418503175380765 2571605598156938690767787)
                      ·
                        rfl

theorem cell23_5008184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_5008184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008184 prefixEnd_5008184 := by exact prefixLift 5008184
  have htrace : WordTrace (prefixWord ++ tailWord_5008184) baseStart_5008184 baseEnd_5008184 := by
    simpa [prefixWord, tailWord_5008184, baseEnd_5008184] using wordTrace_append hprefix tailTrace_5008184
  have hstable : (prefixWord ++ tailWord_5008184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008184).length < 2 ^ (prefixWord ++ tailWord_5008184).sum := by decide
  have hdescent : baseEnd_5008184 < baseStart_5008184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008201 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 3]
def baseStart_5008201 : Nat := 118140960795 + 5008201 * 2 ^ 59
def prefixEnd_5008201 : Nat := 4983230072969 + 3 ^ 40 * 5008201 * 2
def baseEnd_5008201 : Nat := 2571614327328065124255209

theorem tailTrace_5008201 : CollatzResearch.WordTrace tailWord_5008201 prefixEnd_5008201 2571614327328065124255209 := by
  unfold tailWord_5008201
  simp only [CollatzResearch.WordTrace]
  refine ⟨182664096929150584479400457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121776064619433722986266971 182664096929150584479400457)
  ·
    refine ⟨136998072696862938359550343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182664096929150584479400457 136998072696862938359550343)
    ·
      refine ⟨205497109045294407539325515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136998072696862938359550343 205497109045294407539325515)
      ·
        refine ⟨308245663567941611308988273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205497109045294407539325515 308245663567941611308988273)
        ·
          refine ⟨231184247675956208481741205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308245663567941611308988273 231184247675956208481741205)
          ·
            refine ⟨10836761609810447272581619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231184247675956208481741205 10836761609810447272581619)
            ·
              refine ⟨16255142414715670908872429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836761609810447272581619 16255142414715670908872429)
              ·
                refine ⟨6095678405518376590827161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16255142414715670908872429 6095678405518376590827161)
                ·
                  refine ⟨4571758804138782443120371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6095678405518376590827161 4571758804138782443120371)
                  ·
                    refine ⟨6857638206208173664680557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571758804138782443120371 6857638206208173664680557)
                    ·
                      refine ⟨2571614327328065124255209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857638206208173664680557 2571614327328065124255209)
                      ·
                        rfl

theorem cell23_5008201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 1, 3].length) (baseStart_5008201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008201 prefixEnd_5008201 := by exact prefixLift 5008201
  have htrace : WordTrace (prefixWord ++ tailWord_5008201) baseStart_5008201 baseEnd_5008201 := by
    simpa [prefixWord, tailWord_5008201, baseEnd_5008201] using wordTrace_append hprefix tailTrace_5008201
  have hstable : (prefixWord ++ tailWord_5008201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008201).length < 2 ^ (prefixWord ++ tailWord_5008201).sum := by decide
  have hdescent : baseEnd_5008201 < baseStart_5008201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008205 : List Nat := [1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5008205 : Nat := 118140960795 + 5008205 * 2 ^ 59
def prefixEnd_5008205 : Nat := 4983230072969 + 3 ^ 40 * 5008205 * 2
def baseEnd_5008205 : Nat := 2571616381250683108605191

theorem tailTrace_5008205 : CollatzResearch.WordTrace tailWord_5008205 prefixEnd_5008205 2571616381250683108605191 := by
  unfold tailWord_5008205
  simp only [CollatzResearch.WordTrace]
  refine ⟨182664242821136093162546069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121776161880757395441697379 182664242821136093162546069)
  ·
    refine ⟨8562386382240754366994347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182664242821136093162546069 8562386382240754366994347)
    ·
      refine ⟨12843579573361131550491521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562386382240754366994347 12843579573361131550491521)
      ·
        refine ⟨9632684680020848662868641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12843579573361131550491521 9632684680020848662868641)
        ·
          refine ⟨7224513510015636497151481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9632684680020848662868641 7224513510015636497151481)
          ·
            refine ⟨5418385132511727372863611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7224513510015636497151481 5418385132511727372863611)
            ·
              refine ⟨8127577698767591059295417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418385132511727372863611 8127577698767591059295417)
              ·
                refine ⟨6095683274075693294471563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8127577698767591059295417 6095683274075693294471563)
                ·
                  refine ⟨9143524911113539941707345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095683274075693294471563 9143524911113539941707345)
                  ·
                    refine ⟨6857643683335154956280509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9143524911113539941707345 6857643683335154956280509)
                    ·
                      refine ⟨2571616381250683108605191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857643683335154956280509 2571616381250683108605191)
                      ·
                        rfl

theorem cell23_5008205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5008205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008205 prefixEnd_5008205 := by exact prefixLift 5008205
  have htrace : WordTrace (prefixWord ++ tailWord_5008205) baseStart_5008205 baseEnd_5008205 := by
    simpa [prefixWord, tailWord_5008205, baseEnd_5008205] using wordTrace_append hprefix tailTrace_5008205
  have hstable : (prefixWord ++ tailWord_5008205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008205).length < 2 ^ (prefixWord ++ tailWord_5008205).sum := by decide
  have hdescent : baseEnd_5008205 < baseStart_5008205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008237 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5008237 : Nat := 118140960795 + 5008237 * 2 ^ 59
def prefixEnd_5008237 : Nat := 4983230072969 + 3 ^ 40 * 5008237 * 2
def baseEnd_5008237 : Nat := 2571632812631626983405043

theorem tailTrace_5008237 : CollatzResearch.WordTrace tailWord_5008237 prefixEnd_5008237 2571632812631626983405043 := by
  unfold tailWord_5008237
  simp only [CollatzResearch.WordTrace]
  refine ⟨182665409957020162627710965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121776939971346775085140643 182665409957020162627710965)
  ·
    refine ⟨17124882183470640246347903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182665409957020162627710965 17124882183470640246347903)
    ·
      refine ⟨25687323275205960369521855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17124882183470640246347903 25687323275205960369521855)
      ·
        refine ⟨38530984912808940554282783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25687323275205960369521855 38530984912808940554282783)
        ·
          refine ⟨57796477369213410831424175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38530984912808940554282783 57796477369213410831424175)
          ·
            refine ⟨86694716053820116247136263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57796477369213410831424175 86694716053820116247136263)
            ·
              refine ⟨130042074080730174370704395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86694716053820116247136263 130042074080730174370704395)
              ·
                refine ⟨195063111121095261556056593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130042074080730174370704395 195063111121095261556056593)
                ·
                  refine ⟨146297333340821446167042445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195063111121095261556056593 146297333340821446167042445)
                  ·
                    refine ⟨54861500002808042312640917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146297333340821446167042445 54861500002808042312640917)
                    ·
                      refine ⟨2571632812631626983405043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54861500002808042312640917 2571632812631626983405043)
                      ·
                        rfl

theorem cell23_5008237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5008237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008237 prefixEnd_5008237 := by exact prefixLift 5008237
  have htrace : WordTrace (prefixWord ++ tailWord_5008237) baseStart_5008237 baseEnd_5008237 := by
    simpa [prefixWord, tailWord_5008237, baseEnd_5008237] using wordTrace_append hprefix tailTrace_5008237
  have hstable : (prefixWord ++ tailWord_5008237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008237).length < 2 ^ (prefixWord ++ tailWord_5008237).sum := by decide
  have hdescent : baseEnd_5008237 < baseStart_5008237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008264 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 7]
def baseStart_5008264 : Nat := 118140960795 + 5008264 * 2 ^ 59
def prefixEnd_5008264 : Nat := 4983230072969 + 3 ^ 40 * 5008264 * 2
def baseEnd_5008264 : Nat := 285738519623255375307491

theorem tailTrace_5008264 : CollatzResearch.WordTrace tailWord_5008264 prefixEnd_5008264 285738519623255375307491 := by
  unfold tailWord_5008264
  simp only [CollatzResearch.WordTrace]
  refine ⟨91333197363961173119471923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121777596485281564159295897 91333197363961173119471923)
  ·
    refine ⟨136999796045941759679207885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91333197363961173119471923 136999796045941759679207885)
    ·
      refine ⟨51374923517228159879702957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136999796045941759679207885 51374923517228159879702957)
      ·
        refine ⟨19265596318960559954888609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51374923517228159879702957 19265596318960559954888609)
        ·
          refine ⟨14449197239220419966166457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19265596318960559954888609 14449197239220419966166457)
          ·
            refine ⟨10836897929415314974624843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14449197239220419966166457 10836897929415314974624843)
            ·
              refine ⟨16255346894122972461937265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836897929415314974624843 16255346894122972461937265)
              ·
                refine ⟨12191510170592229346452949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16255346894122972461937265 12191510170592229346452949)
                ·
                  refine ⟨285738519623255375307491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12191510170592229346452949 285738519623255375307491)
                  ·
                    rfl

theorem cell23_5008264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_5008264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008264 prefixEnd_5008264 := by exact prefixLift 5008264
  have htrace : WordTrace (prefixWord ++ tailWord_5008264) baseStart_5008264 baseEnd_5008264 := by
    simpa [prefixWord, tailWord_5008264, baseEnd_5008264] using wordTrace_append hprefix tailTrace_5008264
  have hstable : (prefixWord ++ tailWord_5008264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008264).length < 2 ^ (prefixWord ++ tailWord_5008264).sum := by decide
  have hdescent : baseEnd_5008264 < baseStart_5008264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008308 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5008308 : Nat := 118140960795 + 5008308 * 2 ^ 59
def prefixEnd_5008308 : Nat := 4983230072969 + 3 ^ 40 * 5008308 * 2
def baseEnd_5008308 : Nat := 2571669269758096205617217

theorem tailTrace_5008308 : CollatzResearch.WordTrace tailWord_5008308 prefixEnd_5008308 2571669269758096205617217 := by
  unfold tailWord_5008308
  simp only [CollatzResearch.WordTrace]
  refine ⟨91333999769881470876772789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121778666359841961169030385 91333999769881470876772789)
  ·
    refine ⟨8562562478426387894697449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91333999769881470876772789 8562562478426387894697449)
    ·
      refine ⟨6421921858819790921023087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8562562478426387894697449 6421921858819790921023087)
      ·
        refine ⟨9632882788229686381534631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6421921858819790921023087 9632882788229686381534631)
        ·
          refine ⟨14449324182344529572301947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632882788229686381534631 14449324182344529572301947)
          ·
            refine ⟨21673986273516794358452921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14449324182344529572301947 21673986273516794358452921)
            ·
              refine ⟨16255489705137595768839691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21673986273516794358452921 16255489705137595768839691)
              ·
                refine ⟨24383234557706393653259537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16255489705137595768839691 24383234557706393653259537)
                ·
                  refine ⟨18287425918279795239944653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24383234557706393653259537 18287425918279795239944653)
                  ·
                    refine ⟨6857784719354923214979245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18287425918279795239944653 6857784719354923214979245)
                    ·
                      refine ⟨2571669269758096205617217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857784719354923214979245 2571669269758096205617217)
                      ·
                        rfl

theorem cell23_5008308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5008308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008308 prefixEnd_5008308 := by exact prefixLift 5008308
  have htrace : WordTrace (prefixWord ++ tailWord_5008308) baseStart_5008308 baseEnd_5008308 := by
    simpa [prefixWord, tailWord_5008308, baseEnd_5008308] using wordTrace_append hprefix tailTrace_5008308
  have hstable : (prefixWord ++ tailWord_5008308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008308).length < 2 ^ (prefixWord ++ tailWord_5008308).sum := by decide
  have hdescent : baseEnd_5008308 < baseStart_5008308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008337 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 10]
def baseStart_5008337 : Nat := 118140960795 + 5008337 * 2 ^ 59
def prefixEnd_5008337 : Nat := 4983230072969 + 3 ^ 40 * 5008337 * 2
def baseEnd_5008337 : Nat := 285742684521897399128287

theorem tailTrace_5008337 : CollatzResearch.WordTrace tailWord_5008337 prefixEnd_5008337 285742684521897399128287 := by
  unfold tailWord_5008337
  simp only [CollatzResearch.WordTrace]
  refine ⟨182669057256657879706351265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121779371504438586470900843 182669057256657879706351265)
  ·
    refine ⟨137001792942493409779763449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182669057256657879706351265 137001792942493409779763449)
    ·
      refine ⟨102751344706870057334822587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137001792942493409779763449 102751344706870057334822587)
      ·
        refine ⟨154127017060305086002233881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102751344706870057334822587 154127017060305086002233881)
        ·
          refine ⟨115595262795228814501675411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154127017060305086002233881 115595262795228814501675411)
          ·
            refine ⟨173392894192843221752513117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115595262795228814501675411 173392894192843221752513117)
            ·
              refine ⟨65022335322316208157192419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173392894192843221752513117 65022335322316208157192419)
              ·
                refine ⟨97533502983474312235788629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65022335322316208157192419 97533502983474312235788629)
                ·
                  refine ⟨285742684521897399128287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97533502983474312235788629 285742684521897399128287)
                  ·
                    rfl

theorem cell23_5008337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_5008337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008337 prefixEnd_5008337 := by exact prefixLift 5008337
  have htrace : WordTrace (prefixWord ++ tailWord_5008337) baseStart_5008337 baseEnd_5008337 := by
    simpa [prefixWord, tailWord_5008337, baseEnd_5008337] using wordTrace_append hprefix tailTrace_5008337
  have hstable : (prefixWord ++ tailWord_5008337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008337).length < 2 ^ (prefixWord ++ tailWord_5008337).sum := by decide
  have hdescent : baseEnd_5008337 < baseStart_5008337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008381 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_5008381 : Nat := 118140960795 + 5008381 * 2 ^ 59
def prefixEnd_5008381 : Nat := 4983230072969 + 3 ^ 40 * 5008381 * 2
def baseEnd_5008381 : Nat := 2571706753845874420004381

theorem tailTrace_5008381 : CollatzResearch.WordTrace tailWord_5008381 prefixEnd_5008381 2571706753845874420004381 := by
  unfold tailWord_5008381
  simp only [CollatzResearch.WordTrace]
  refine ⟨182670662068498475220952997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121780441378998983480635331 182670662068498475220952997)
  ·
    refine ⟨34250749137843464103928687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182670662068498475220952997 34250749137843464103928687)
    ·
      refine ⟨51376123706765196155893031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34250749137843464103928687 51376123706765196155893031)
      ·
        refine ⟨77064185560147794233839547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51376123706765196155893031 77064185560147794233839547)
        ·
          refine ⟨115596278340221691350759321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77064185560147794233839547 115596278340221691350759321)
          ·
            refine ⟨86697208755166268513069491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115596278340221691350759321 86697208755166268513069491)
            ·
              refine ⟨130045813132749402769604237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86697208755166268513069491 130045813132749402769604237)
              ·
                refine ⟨48767179924781026038601589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130045813132749402769604237 48767179924781026038601589)
                ·
                  refine ⟨4571923117948221191118899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48767179924781026038601589 4571923117948221191118899)
                  ·
                    refine ⟨6857884676922331786678349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571923117948221191118899 6857884676922331786678349)
                    ·
                      refine ⟨2571706753845874420004381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857884676922331786678349 2571706753845874420004381)
                      ·
                        rfl

theorem cell23_5008381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_5008381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008381 prefixEnd_5008381 := by exact prefixLift 5008381
  have htrace : WordTrace (prefixWord ++ tailWord_5008381) baseStart_5008381 baseEnd_5008381 := by
    simpa [prefixWord, tailWord_5008381, baseEnd_5008381] using wordTrace_append hprefix tailTrace_5008381
  have hstable : (prefixWord ++ tailWord_5008381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008381).length < 2 ^ (prefixWord ++ tailWord_5008381).sum := by decide
  have hdescent : baseEnd_5008381 < baseStart_5008381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008408 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5008408 : Nat := 118140960795 + 5008408 * 2 ^ 59
def prefixEnd_5008408 : Nat := 4983230072969 + 3 ^ 40 * 5008408 * 2
def baseEnd_5008408 : Nat := 2571720617823545814366757

theorem tailTrace_5008408 : CollatzResearch.WordTrace tailWord_5008408 prefixEnd_5008408 2571720617823545814366757 := by
  unfold tailWord_5008408
  simp only [CollatzResearch.WordTrace]
  refine ⟨91335823419700329416092939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121781097892933772554790585 91335823419700329416092939)
  ·
    refine ⟨137003735129550494124139409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91335823419700329416092939 137003735129550494124139409)
    ·
      refine ⟨102752801347162870593104557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137003735129550494124139409 102752801347162870593104557)
      ·
        refine ⟨38532300505186076472414209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102752801347162870593104557 38532300505186076472414209)
        ·
          refine ⟨28899225378889557354310657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38532300505186076472414209 28899225378889557354310657)
          ·
            refine ⟨21674419034167168015732993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28899225378889557354310657 21674419034167168015732993)
            ·
              refine ⟨16255814275625376011799745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21674419034167168015732993 16255814275625376011799745)
              ·
                refine ⟨12191860706719032008849809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16255814275625376011799745 12191860706719032008849809)
                ·
                  refine ⟨9143895530039274006637357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12191860706719032008849809 9143895530039274006637357)
                  ·
                    refine ⟨3428960823764727752489009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9143895530039274006637357 3428960823764727752489009)
                    ·
                      refine ⟨2571720617823545814366757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3428960823764727752489009 2571720617823545814366757)
                      ·
                        rfl

theorem cell23_5008408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5008408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008408 prefixEnd_5008408 := by exact prefixLift 5008408
  have htrace : WordTrace (prefixWord ++ tailWord_5008408) baseStart_5008408 baseEnd_5008408 := by
    simpa [prefixWord, tailWord_5008408, baseEnd_5008408] using wordTrace_append hprefix tailTrace_5008408
  have hstable : (prefixWord ++ tailWord_5008408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008408).length < 2 ^ (prefixWord ++ tailWord_5008408).sum := by decide
  have hdescent : baseEnd_5008408 < baseStart_5008408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008415 : List Nat := [1, 1, 2, 4, 1, 4, 1, 4, 1, 1, 3]
def baseStart_5008415 : Nat := 118140960795 + 5008415 * 2 ^ 59
def prefixEnd_5008415 : Nat := 4983230072969 + 3 ^ 40 * 5008415 * 2
def baseEnd_5008415 : Nat := 2571724212188127286979225

theorem tailTrace_5008415 : CollatzResearch.WordTrace tailWord_5008415 prefixEnd_5008415 2571724212188127286979225 := by
  unfold tailWord_5008415
  simp only [CollatzResearch.WordTrace]
  refine ⟨182671902150375299027690699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121781268100250199351793799 182671902150375299027690699)
  ·
    refine ⟨274007853225562948541536049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182671902150375299027690699 274007853225562948541536049)
    ·
      refine ⟨205505889919172211406152037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274007853225562948541536049 205505889919172211406152037)
      ·
        refine ⟨38532354359844789638653507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205505889919172211406152037 38532354359844789638653507)
        ·
          refine ⟨57798531539767184457980261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38532354359844789638653507 57798531539767184457980261)
          ·
            refine ⟨10837224663706347085871299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57798531539767184457980261 10837224663706347085871299)
            ·
              refine ⟨16255836995559520628806949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837224663706347085871299 16255836995559520628806949)
              ·
                refine ⟨3047969436667410117901303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16255836995559520628806949 3047969436667410117901303)
                ·
                  refine ⟨4571954155001115176851955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047969436667410117901303 4571954155001115176851955)
                  ·
                    refine ⟨6857931232501672765277933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571954155001115176851955 6857931232501672765277933)
                    ·
                      refine ⟨2571724212188127286979225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6857931232501672765277933 2571724212188127286979225)
                      ·
                        rfl

theorem cell23_5008415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_5008415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008415 prefixEnd_5008415 := by exact prefixLift 5008415
  have htrace : WordTrace (prefixWord ++ tailWord_5008415) baseStart_5008415 baseEnd_5008415 := by
    simpa [prefixWord, tailWord_5008415, baseEnd_5008415] using wordTrace_append hprefix tailTrace_5008415
  have hstable : (prefixWord ++ tailWord_5008415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008415).length < 2 ^ (prefixWord ++ tailWord_5008415).sum := by decide
  have hdescent : baseEnd_5008415 < baseStart_5008415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008438 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5008438 : Nat := 118140960795 + 5008438 * 2 ^ 59
def prefixEnd_5008438 : Nat := 4983230072969 + 3 ^ 40 * 5008438 * 2
def baseEnd_5008438 : Nat := 2571736022243180696991619

theorem tailTrace_5008438 : CollatzResearch.WordTrace tailWord_5008438 prefixEnd_5008438 2571736022243180696991619 := by
  unfold tailWord_5008438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417046314330748372236123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121781827352861315970518645 11417046314330748372236123)
  ·
    refine ⟨17125569471496122558354185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11417046314330748372236123 17125569471496122558354185)
    ·
      refine ⟨12844177103622091918765639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17125569471496122558354185 12844177103622091918765639)
      ·
        refine ⟨19266265655433137878148459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12844177103622091918765639 19266265655433137878148459)
        ·
          refine ⟨28899398483149706817222689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19266265655433137878148459 28899398483149706817222689)
          ·
            refine ⟨21674548862362280112917017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28899398483149706817222689 21674548862362280112917017)
            ·
              refine ⟨16255911646771710084687763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21674548862362280112917017 16255911646771710084687763)
              ·
                refine ⟨24383867470157565127031645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16255911646771710084687763 24383867470157565127031645)
                ·
                  refine ⟨9143950301309086922636867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24383867470157565127031645 9143950301309086922636867)
                  ·
                    refine ⟨13715925451963630383955301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9143950301309086922636867 13715925451963630383955301)
                    ·
                      refine ⟨2571736022243180696991619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13715925451963630383955301 2571736022243180696991619)
                      ·
                        rfl

theorem cell23_5008438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5008438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008438 prefixEnd_5008438 := by exact prefixLift 5008438
  have htrace : WordTrace (prefixWord ++ tailWord_5008438) baseStart_5008438 baseEnd_5008438 := by
    simpa [prefixWord, tailWord_5008438, baseEnd_5008438] using wordTrace_append hprefix tailTrace_5008438
  have hstable : (prefixWord ++ tailWord_5008438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008438).length < 2 ^ (prefixWord ++ tailWord_5008438).sum := by decide
  have hdescent : baseEnd_5008438 < baseStart_5008438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008455 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_5008455 : Nat := 118140960795 + 5008455 * 2 ^ 59
def prefixEnd_5008455 : Nat := 4983230072969 + 3 ^ 40 * 5008455 * 2
def baseEnd_5008455 : Nat := 2571744751414307130479041

theorem tailTrace_5008455 : CollatzResearch.WordTrace tailWord_5008455 prefixEnd_5008455 2571744751414307130479041 := by
  unfold tailWord_5008455
  simp only [CollatzResearch.WordTrace]
  refine ⟨182673361070230385859146819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121782240713486923906097879 182673361070230385859146819)
  ·
    refine ⟨274010041605345578788720229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182673361070230385859146819 274010041605345578788720229)
    ·
      refine ⟨51376882801002296022885043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274010041605345578788720229 51376882801002296022885043)
      ·
        refine ⟨77065324201503444034327565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51376882801002296022885043 77065324201503444034327565)
        ·
          refine ⟨28899496575563791512872837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77065324201503444034327565 28899496575563791512872837)
          ·
            refine ⟨5418655607918210908663657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28899496575563791512872837 5418655607918210908663657)
            ·
              refine ⟨4063991705938658181497743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418655607918210908663657 4063991705938658181497743)
              ·
                refine ⟨6095987558907987272246615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063991705938658181497743 6095987558907987272246615)
                ·
                  refine ⟨9143981338361980908369923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6095987558907987272246615 9143981338361980908369923)
                  ·
                    refine ⟨13715972007542971362554885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9143981338361980908369923 13715972007542971362554885)
                    ·
                      refine ⟨2571744751414307130479041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13715972007542971362554885 2571744751414307130479041)
                      ·
                        rfl

theorem cell23_5008455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_5008455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008455 prefixEnd_5008455 := by exact prefixLift 5008455
  have htrace : WordTrace (prefixWord ++ tailWord_5008455) baseStart_5008455 baseEnd_5008455 := by
    simpa [prefixWord, tailWord_5008455, baseEnd_5008455] using wordTrace_append hprefix tailTrace_5008455
  have hstable : (prefixWord ++ tailWord_5008455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008455).length < 2 ^ (prefixWord ++ tailWord_5008455).sum := by decide
  have hdescent : baseEnd_5008455 < baseStart_5008455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008461 : List Nat := [1, 6, 1, 1, 1, 3, 10]
def baseStart_5008461 : Nat := 118140960795 + 5008461 * 2 ^ 59
def prefixEnd_5008461 : Nat := 4983230072969 + 3 ^ 40 * 5008461 * 2
def baseEnd_5008461 : Nat := 31749973238249803790173

theorem tailTrace_5008461 : CollatzResearch.WordTrace tailWord_5008461 prefixEnd_5008461 31749973238249803790173 := by
  unfold tailWord_5008461
  simp only [CollatzResearch.WordTrace]
  refine ⟨182673579908208648883865237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121782386605472432589243491 182673579908208648883865237)
  ·
    refine ⟨8562824058197280416431183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182673579908208648883865237 8562824058197280416431183)
    ·
      refine ⟨12844236087295920624646775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562824058197280416431183 12844236087295920624646775)
      ·
        refine ⟨19266354130943880936970163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12844236087295920624646775 19266354130943880936970163)
        ·
          refine ⟨28899531196415821405455245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19266354130943880936970163 28899531196415821405455245)
          ·
            refine ⟨10837324198655933027045717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28899531196415821405455245 10837324198655933027045717)
            ·
              refine ⟨31749973238249803790173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10837324198655933027045717 31749973238249803790173)
              ·
                rfl

theorem cell23_5008461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 10].length) (baseStart_5008461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008461 prefixEnd_5008461 := by exact prefixLift 5008461
  have htrace : WordTrace (prefixWord ++ tailWord_5008461) baseStart_5008461 baseEnd_5008461 := by
    simpa [prefixWord, tailWord_5008461, baseEnd_5008461] using wordTrace_append hprefix tailTrace_5008461
  have hstable : (prefixWord ++ tailWord_5008461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008461).length < 2 ^ (prefixWord ++ tailWord_5008461).sum := by decide
  have hdescent : baseEnd_5008461 < baseStart_5008461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008474 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_5008474 : Nat := 118140960795 + 5008474 * 2 ^ 59
def prefixEnd_5008474 : Nat := 4983230072969 + 3 ^ 40 * 5008474 * 2
def baseEnd_5008474 : Nat := 857251502515580852047151

theorem tailTrace_5008474 : CollatzResearch.WordTrace tailWord_5008474 prefixEnd_5008474 857251502515580852047151 := by
  unfold tailWord_5008474
  simp only [CollatzResearch.WordTrace]
  refine ⟨45668513514290388026022119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121782702704774368069392317 45668513514290388026022119)
  ·
    refine ⟨68502770271435582039033179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45668513514290388026022119 68502770271435582039033179)
    ·
      refine ⟨102754155407153373058549769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68502770271435582039033179 102754155407153373058549769)
      ·
        refine ⟨77065616555365029793912327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102754155407153373058549769 77065616555365029793912327)
        ·
          refine ⟨115598424833047544690868491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77065616555365029793912327 115598424833047544690868491)
          ·
            refine ⟨173397637249571317036302737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115598424833047544690868491 173397637249571317036302737)
            ·
              refine ⟨130048227937178487777227053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173397637249571317036302737 130048227937178487777227053)
              ·
                refine ⟨48768085476441932916460145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130048227937178487777227053 48768085476441932916460145)
                ·
                  refine ⟨36576064107331449687345109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48768085476441932916460145 36576064107331449687345109)
                  ·
                    refine ⟨857251502515580852047151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36576064107331449687345109 857251502515580852047151)
                    ·
                      rfl

theorem cell23_5008474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_5008474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008474 prefixEnd_5008474 := by exact prefixLift 5008474
  have htrace : WordTrace (prefixWord ++ tailWord_5008474) baseStart_5008474 baseEnd_5008474 := by
    simpa [prefixWord, tailWord_5008474, baseEnd_5008474] using wordTrace_append hprefix tailTrace_5008474
  have hstable : (prefixWord ++ tailWord_5008474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008474).length < 2 ^ (prefixWord ++ tailWord_5008474).sum := by decide
  have hdescent : baseEnd_5008474 < baseStart_5008474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008482 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5008482 : Nat := 118140960795 + 5008482 * 2 ^ 59
def prefixEnd_5008482 : Nat := 4983230072969 + 3 ^ 40 * 5008482 * 2
def baseEnd_5008482 : Nat := 857252871797326174947139

theorem tailTrace_5008482 : CollatzResearch.WordTrace tailWord_5008482 prefixEnd_5008482 857252871797326174947139 := by
  unfold tailWord_5008482
  simp only [CollatzResearch.WordTrace]
  refine ⟨45668586460283142367594925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121782897227421712980253133 45668586460283142367594925)
  ·
    refine ⟨17125719922606178387848097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45668586460283142367594925 17125719922606178387848097)
    ·
      refine ⟨12844289941954633790886073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17125719922606178387848097 12844289941954633790886073)
      ·
        refine ⟨9633217456465975343164555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12844289941954633790886073 9633217456465975343164555)
        ·
          refine ⟨14449826184698963014746833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633217456465975343164555 14449826184698963014746833)
          ·
            refine ⟨10837369638524222261060125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14449826184698963014746833 10837369638524222261060125)
            ·
              refine ⟨4064013614446583347897547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10837369638524222261060125 4064013614446583347897547)
              ·
                refine ⟨6096020421669875021846321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064013614446583347897547 6096020421669875021846321)
                ·
                  refine ⟨4572015316252406266384741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6096020421669875021846321 4572015316252406266384741)
                  ·
                    refine ⟨857252871797326174947139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572015316252406266384741 857252871797326174947139)
                    ·
                      rfl

theorem cell23_5008482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5008482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008482 prefixEnd_5008482 := by exact prefixLift 5008482
  have htrace : WordTrace (prefixWord ++ tailWord_5008482) baseStart_5008482 baseEnd_5008482 := by
    simpa [prefixWord, tailWord_5008482, baseEnd_5008482] using wordTrace_append hprefix tailTrace_5008482
  have hstable : (prefixWord ++ tailWord_5008482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008482).length < 2 ^ (prefixWord ++ tailWord_5008482).sum := by decide
  have hdescent : baseEnd_5008482 < baseStart_5008482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008504 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_5008504 : Nat := 118140960795 + 5008504 * 2 ^ 59
def prefixEnd_5008504 : Nat := 4983230072969 + 3 ^ 40 * 5008504 * 2
def baseEnd_5008504 : Nat := 857256637322125812922105

theorem tailTrace_5008504 : CollatzResearch.WordTrace tailWord_5008504 prefixEnd_5008504 857256637322125812922105 := by
  unfold tailWord_5008504
  simp only [CollatzResearch.WordTrace]
  refine ⟨91337574123526433613840283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121783432164701911485120377 91337574123526433613840283)
  ·
    refine ⟨137006361185289650420760425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91337574123526433613840283 137006361185289650420760425)
    ·
      refine ⟨102754770888967237815570319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137006361185289650420760425 102754770888967237815570319)
      ·
        refine ⟨154132156333450856723355479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102754770888967237815570319 154132156333450856723355479)
        ·
          refine ⟨231198234500176285085033219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154132156333450856723355479 231198234500176285085033219)
          ·
            refine ⟨346797351750264427627549829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231198234500176285085033219 346797351750264427627549829)
            ·
              refine ⟨65024503453174580180165593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346797351750264427627549829 65024503453174580180165593)
              ·
                refine ⟨48768377589880935135124195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65024503453174580180165593 48768377589880935135124195)
                ·
                  refine ⟨73152566384821402702686293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48768377589880935135124195 73152566384821402702686293)
                  ·
                    refine ⟨857256637322125812922105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73152566384821402702686293 857256637322125812922105)
                    ·
                      rfl

theorem cell23_5008504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_5008504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008504 prefixEnd_5008504 := by exact prefixLift 5008504
  have htrace : WordTrace (prefixWord ++ tailWord_5008504) baseStart_5008504 baseEnd_5008504 := by
    simpa [prefixWord, tailWord_5008504, baseEnd_5008504] using wordTrace_append hprefix tailTrace_5008504
  have hstable : (prefixWord ++ tailWord_5008504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008504).length < 2 ^ (prefixWord ++ tailWord_5008504).sum := by decide
  have hdescent : baseEnd_5008504 < baseStart_5008504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008541 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5008541 : Nat := 118140960795 + 5008541 * 2 ^ 59
def prefixEnd_5008541 : Nat := 4983230072969 + 3 ^ 40 * 5008541 * 2
def baseEnd_5008541 : Nat := 2571788910750593794003645

theorem tailTrace_5008541 : CollatzResearch.WordTrace tailWord_5008541 prefixEnd_5008541 2571788910750593794003645 := by
  unfold tailWord_5008541
  simp only [CollatzResearch.WordTrace]
  refine ⟨182676497747918822546777477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121784331831945881697851651 182676497747918822546777477)
  ·
    refine ⟨34251843327734779227520777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182676497747918822546777477 34251843327734779227520777)
    ·
      refine ⟨25688882495801084420640583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34251843327734779227520777 25688882495801084420640583)
      ·
        refine ⟨38533323743701626630960875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25688882495801084420640583 38533323743701626630960875)
        ·
          refine ⟨57799985615552439946441313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38533323743701626630960875 57799985615552439946441313)
          ·
            refine ⟨43349989211664329959830985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57799985615552439946441313 43349989211664329959830985)
            ·
              refine ⟨32512491908748247469873239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43349989211664329959830985 32512491908748247469873239)
              ·
                refine ⟨48768737863122371204809859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32512491908748247469873239 48768737863122371204809859)
                ·
                  refine ⟨73153106794683556807214789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48768737863122371204809859 73153106794683556807214789)
                  ·
                    refine ⟨13716207524003166901352773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73153106794683556807214789 13716207524003166901352773)
                    ·
                      refine ⟨2571788910750593794003645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13716207524003166901352773 2571788910750593794003645)
                      ·
                        rfl

theorem cell23_5008541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5008541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008541 prefixEnd_5008541 := by exact prefixLift 5008541
  have htrace : WordTrace (prefixWord ++ tailWord_5008541) baseStart_5008541 baseEnd_5008541 := by
    simpa [prefixWord, tailWord_5008541, baseEnd_5008541] using wordTrace_append hprefix tailTrace_5008541
  have hstable : (prefixWord ++ tailWord_5008541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008541).length < 2 ^ (prefixWord ++ tailWord_5008541).sum := by decide
  have hdescent : baseEnd_5008541 < baseStart_5008541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008601 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_5008601 : Nat := 118140960795 + 5008601 * 2 ^ 59
def prefixEnd_5008601 : Nat := 4983230072969 + 3 ^ 40 * 5008601 * 2
def baseEnd_5008601 : Nat := 2571819719589863559253369

theorem tailTrace_5008601 : CollatzResearch.WordTrace tailWord_5008601 prefixEnd_5008601 2571819719589863559253369 := by
  unfold tailWord_5008601
  simp only [CollatzResearch.WordTrace]
  refine ⟨182678686127701452793961657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121785790751800968529307771 182678686127701452793961657)
  ·
    refine ⟨137009014595776089595471243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182678686127701452793961657 137009014595776089595471243)
    ·
      refine ⟨205513521893664134393206865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137009014595776089595471243 205513521893664134393206865)
      ·
        refine ⟨154135141420248100794905149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205513521893664134393206865 154135141420248100794905149)
        ·
          refine ⟨57800678032593037798089431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154135141420248100794905149 57800678032593037798089431)
          ·
            refine ⟨86701017048889556697134147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57800678032593037798089431 86701017048889556697134147)
            ·
              refine ⟨130051525573334335045701221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86701017048889556697134147 130051525573334335045701221)
              ·
                refine ⟨24384661045000187821068979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130051525573334335045701221 24384661045000187821068979)
                ·
                  refine ⟨36576991567500281731603469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24384661045000187821068979 36576991567500281731603469)
                  ·
                    refine ⟨13716371837812605649351301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36576991567500281731603469 13716371837812605649351301)
                    ·
                      refine ⟨2571819719589863559253369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13716371837812605649351301 2571819719589863559253369)
                      ·
                        rfl

theorem cell23_5008601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_5008601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008601 prefixEnd_5008601 := by exact prefixLift 5008601
  have htrace : WordTrace (prefixWord ++ tailWord_5008601) baseStart_5008601 baseEnd_5008601 := by
    simpa [prefixWord, tailWord_5008601, baseEnd_5008601] using wordTrace_append hprefix tailTrace_5008601
  have hstable : (prefixWord ++ tailWord_5008601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008601).length < 2 ^ (prefixWord ++ tailWord_5008601).sum := by decide
  have hdescent : baseEnd_5008601 < baseStart_5008601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008618 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_5008618 : Nat := 118140960795 + 5008618 * 2 ^ 59
def prefixEnd_5008618 : Nat := 4983230072969 + 3 ^ 40 * 5008618 * 2
def baseEnd_5008618 : Nat := 2571828448760989992740791

theorem tailTrace_5008618 : CollatzResearch.WordTrace tailWord_5008618 prefixEnd_5008618 2571828448760989992740791 := by
  unfold tailWord_5008618
  simp only [CollatzResearch.WordTrace]
  refine ⟨45669826542159966174332627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121786204112426576464887005 45669826542159966174332627)
  ·
    refine ⟨68504739813239949261498941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45669826542159966174332627 68504739813239949261498941)
    ·
      refine ⟨25689277429964980973062103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68504739813239949261498941 25689277429964980973062103)
      ·
        refine ⟨38533916144947471459593155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25689277429964980973062103 38533916144947471459593155)
        ·
          refine ⟨57800874217421207189389733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38533916144947471459593155 57800874217421207189389733)
          ·
            refine ⟨10837663915766476348010575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57800874217421207189389733 10837663915766476348010575)
            ·
              refine ⟨16256495873649714522015863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837663915766476348010575 16256495873649714522015863)
              ·
                refine ⟨24384743810474571783023795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16256495873649714522015863 24384743810474571783023795)
                ·
                  refine ⟨36577115715711857674535693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24384743810474571783023795 36577115715711857674535693)
                  ·
                    refine ⟨13716418393391946627950885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36577115715711857674535693 13716418393391946627950885)
                    ·
                      refine ⟨2571828448760989992740791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13716418393391946627950885 2571828448760989992740791)
                      ·
                        rfl

theorem cell23_5008618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_5008618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008618 prefixEnd_5008618 := by exact prefixLift 5008618
  have htrace : WordTrace (prefixWord ++ tailWord_5008618) baseStart_5008618 baseEnd_5008618 := by
    simpa [prefixWord, tailWord_5008618, baseEnd_5008618] using wordTrace_append hprefix tailTrace_5008618
  have hstable : (prefixWord ++ tailWord_5008618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008618).length < 2 ^ (prefixWord ++ tailWord_5008618).sum := by decide
  have hdescent : baseEnd_5008618 < baseStart_5008618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008645 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_5008645 : Nat := 118140960795 + 5008645 * 2 ^ 59
def prefixEnd_5008645 : Nat := 4983230072969 + 3 ^ 40 * 5008645 * 2
def baseEnd_5008645 : Nat := 857280770912887129034389

theorem tailTrace_5008645 : CollatzResearch.WordTrace tailWord_5008645 prefixEnd_5008645 857280770912887129034389 := by
  unfold tailWord_5008645
  simp only [CollatzResearch.WordTrace]
  refine ⟨182680290939542048308563389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121786860626361365539042259 182680290939542048308563389)
  ·
    refine ⟨68505109102328268115711271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182680290939542048308563389 68505109102328268115711271)
    ·
      refine ⟨102757663653492402173566907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68505109102328268115711271 102757663653492402173566907)
      ·
        refine ⟨154136495480238603260350361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102757663653492402173566907 154136495480238603260350361)
        ·
          refine ⟨115602371610178952445262771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154136495480238603260350361 115602371610178952445262771)
          ·
            refine ⟨173403557415268428667894157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115602371610178952445262771 173403557415268428667894157)
            ·
              refine ⟨65026334030725660750460309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173403557415268428667894157 65026334030725660750460309)
              ·
                refine ⟨3048109407690265347677827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65026334030725660750460309 3048109407690265347677827)
                ·
                  refine ⟨4572164111535398021516741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048109407690265347677827 4572164111535398021516741)
                  ·
                    refine ⟨857280770912887129034389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572164111535398021516741 857280770912887129034389)
                    ·
                      rfl

theorem cell23_5008645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_5008645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008645 prefixEnd_5008645 := by exact prefixLift 5008645
  have htrace : WordTrace (prefixWord ++ tailWord_5008645) baseStart_5008645 baseEnd_5008645 := by
    simpa [prefixWord, tailWord_5008645, baseEnd_5008645] using wordTrace_append hprefix tailTrace_5008645
  have hstable : (prefixWord ++ tailWord_5008645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008645).length < 2 ^ (prefixWord ++ tailWord_5008645).sum := by decide
  have hdescent : baseEnd_5008645 < baseStart_5008645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008661 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_5008661 : Nat := 118140960795 + 5008661 * 2 ^ 59
def prefixEnd_5008661 : Nat := 4983230072969 + 3 ^ 40 * 5008661 * 2
def baseEnd_5008661 : Nat := 2571850528429133324503093

theorem tailTrace_5008661 : CollatzResearch.WordTrace tailWord_5008661 prefixEnd_5008661 2571850528429133324503093 := by
  unfold tailWord_5008661
  simp only [CollatzResearch.WordTrace]
  refine ⟨182680874507484083041145837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121787249671656055360763891 182680874507484083041145837)
  ·
    refine ⟨68505327940306531140429689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182680874507484083041145837 68505327940306531140429689)
    ·
      refine ⟨51378995955229898355322267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68505327940306531140429689 51378995955229898355322267)
      ·
        refine ⟨77068493932844847532983401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51378995955229898355322267 77068493932844847532983401)
        ·
          refine ⟨57801370449633635649737551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77068493932844847532983401 57801370449633635649737551)
          ·
            refine ⟨86702055674450453474606327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57801370449633635649737551 86702055674450453474606327)
            ·
              refine ⟨130053083511675680211909491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86702055674450453474606327 130053083511675680211909491)
              ·
                refine ⟨195079625267513520317864237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130053083511675680211909491 195079625267513520317864237)
                ·
                  refine ⟨73154859475317570119199089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195079625267513520317864237 73154859475317570119199089)
                  ·
                    refine ⟨54866144606488177589399317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73154859475317570119199089 54866144606488177589399317)
                    ·
                      refine ⟨2571850528429133324503093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54866144606488177589399317 2571850528429133324503093)
                      ·
                        rfl

theorem cell23_5008661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_5008661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008661 prefixEnd_5008661 := by exact prefixLift 5008661
  have htrace : WordTrace (prefixWord ++ tailWord_5008661) baseStart_5008661 baseEnd_5008661 := by
    simpa [prefixWord, tailWord_5008661, baseEnd_5008661] using wordTrace_append hprefix tailTrace_5008661
  have hstable : (prefixWord ++ tailWord_5008661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008661).length < 2 ^ (prefixWord ++ tailWord_5008661).sum := by decide
  have hdescent : baseEnd_5008661 < baseStart_5008661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008688 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_5008688 : Nat := 118140960795 + 5008688 * 2 ^ 59
def prefixEnd_5008688 : Nat := 4983230072969 + 3 ^ 40 * 5008688 * 2
def baseEnd_5008688 : Nat := 857288130802268239621823

theorem tailTrace_5008688 : CollatzResearch.WordTrace tailWord_5008688 prefixEnd_5008688 857288130802268239621823 := by
  unfold tailWord_5008688
  simp only [CollatzResearch.WordTrace]
  refine ⟨91340929639193133326189359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121787906185590844434919145 91340929639193133326189359)
  ·
    refine ⟨137011394458789699989284039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91340929639193133326189359 137011394458789699989284039)
    ·
      refine ⟨205517091688184549983926059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137011394458789699989284039 205517091688184549983926059)
      ·
        refine ⟨308275637532276824975889089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205517091688184549983926059 308275637532276824975889089)
        ·
          refine ⟨231206728149207618731916817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308275637532276824975889089 231206728149207618731916817)
          ·
            refine ⟨173405046111905714048937613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231206728149207618731916817 173405046111905714048937613)
            ·
              refine ⟨65026892291964642768351605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173405046111905714048937613 65026892291964642768351605)
              ·
                refine ⟨6096271152371685259532963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65026892291964642768351605 6096271152371685259532963)
                ·
                  refine ⟨9144406728557527889299445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6096271152371685259532963 9144406728557527889299445)
                  ·
                    refine ⟨857288130802268239621823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9144406728557527889299445 857288130802268239621823)
                    ·
                      rfl

theorem cell23_5008688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_5008688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008688 prefixEnd_5008688 := by exact prefixLift 5008688
  have htrace : WordTrace (prefixWord ++ tailWord_5008688) baseStart_5008688 baseEnd_5008688 := by
    simpa [prefixWord, tailWord_5008688, baseEnd_5008688] using wordTrace_append hprefix tailTrace_5008688
  have hstable : (prefixWord ++ tailWord_5008688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008688).length < 2 ^ (prefixWord ++ tailWord_5008688).sum := by decide
  have hdescent : baseEnd_5008688 < baseStart_5008688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008718 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_5008718 : Nat := 118140960795 + 5008718 * 2 ^ 59
def prefixEnd_5008718 : Nat := 4983230072969 + 3 ^ 40 * 5008718 * 2
def baseEnd_5008718 : Nat := 857293265608813200496777

theorem tailTrace_5008718 : CollatzResearch.WordTrace tailWord_5008718 prefixEnd_5008718 857293265608813200496777 := by
  unfold tailWord_5008718
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835369183534697721996351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121788635645518387850647205 22835369183534697721996351)
  ·
    refine ⟨34253053775302046582994527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22835369183534697721996351 34253053775302046582994527)
    ·
      refine ⟨51379580662953069874491791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34253053775302046582994527 51379580662953069874491791)
      ·
        refine ⟨77069370994429604811737687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51379580662953069874491791 77069370994429604811737687)
        ·
          refine ⟨115604056491644407217606531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77069370994429604811737687 115604056491644407217606531)
          ·
            refine ⟨173406084737466610826409797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115604056491644407217606531 173406084737466610826409797)
            ·
              refine ⟨32513640888274989529951837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173406084737466610826409797 32513640888274989529951837)
              ·
                refine ⟨12192615333103121073731939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32513640888274989529951837 12192615333103121073731939)
                ·
                  refine ⟨18288922999654681610597909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12192615333103121073731939 18288922999654681610597909)
                  ·
                    refine ⟨857293265608813200496777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18288922999654681610597909 857293265608813200496777)
                    ·
                      rfl

theorem cell23_5008718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_5008718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008718 prefixEnd_5008718 := by exact prefixLift 5008718
  have htrace : WordTrace (prefixWord ++ tailWord_5008718) baseStart_5008718 baseEnd_5008718 := by
    simpa [prefixWord, tailWord_5008718, baseEnd_5008718] using wordTrace_append hprefix tailTrace_5008718
  have hstable : (prefixWord ++ tailWord_5008718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008718).length < 2 ^ (prefixWord ++ tailWord_5008718).sum := by decide
  have hdescent : baseEnd_5008718 < baseStart_5008718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008725 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5008725 : Nat := 118140960795 + 5008725 * 2 ^ 59
def prefixEnd_5008725 : Nat := 4983230072969 + 3 ^ 40 * 5008725 * 2
def baseEnd_5008725 : Nat := 2571883391191021074102799

theorem tailTrace_5008725 : CollatzResearch.WordTrace tailWord_5008725 prefixEnd_5008725 2571883391191021074102799 := by
  unfold tailWord_5008725
  simp only [CollatzResearch.WordTrace]
  refine ⟨182683208779252221971475629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121788805852834814647650419 182683208779252221971475629)
  ·
    refine ⟨68506203292219583239303361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182683208779252221971475629 68506203292219583239303361)
    ·
      refine ⟨51379652469164687429477521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68506203292219583239303361 51379652469164687429477521)
      ·
        refine ⟨38534739351873515572108141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51379652469164687429477521 38534739351873515572108141)
        ·
          refine ⟨14450527256952568339540553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38534739351873515572108141 14450527256952568339540553)
          ·
            refine ⟨10837895442714426254655415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14450527256952568339540553 10837895442714426254655415)
            ·
              refine ⟨16256843164071639381983123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837895442714426254655415 16256843164071639381983123)
              ·
                refine ⟨24385264746107459072974685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16256843164071639381983123 24385264746107459072974685)
                ·
                  refine ⟨9144474279790297152365507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24385264746107459072974685 9144474279790297152365507)
                  ·
                    refine ⟨13716711419685445728548261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9144474279790297152365507 13716711419685445728548261)
                    ·
                      refine ⟨2571883391191021074102799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13716711419685445728548261 2571883391191021074102799)
                      ·
                        rfl

theorem cell23_5008725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5008725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008725 prefixEnd_5008725 := by exact prefixLift 5008725
  have htrace : WordTrace (prefixWord ++ tailWord_5008725) baseStart_5008725 baseEnd_5008725 := by
    simpa [prefixWord, tailWord_5008725, baseEnd_5008725] using wordTrace_append hprefix tailTrace_5008725
  have hstable : (prefixWord ++ tailWord_5008725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008725).length < 2 ^ (prefixWord ++ tailWord_5008725).sum := by decide
  have hdescent : baseEnd_5008725 < baseStart_5008725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008759 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 1, 2, 2]
def baseStart_5008759 : Nat := 118140960795 + 5008759 * 2 ^ 59
def prefixEnd_5008759 : Nat := 4983230072969 + 3 ^ 40 * 5008759 * 2
def baseEnd_5008759 : Nat := 2571900849533273941077643

theorem tailTrace_5008759 : CollatzResearch.WordTrace tailWord_5008759 prefixEnd_5008759 2571900849533273941077643 := by
  unfold tailWord_5008759
  simp only [CollatzResearch.WordTrace]
  refine ⟨182684448861129045778213331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121789632574086030518808887 182684448861129045778213331)
  ·
    refine ⟨274026673291693568667319997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182684448861129045778213331 274026673291693568667319997)
    ·
      refine ⟨102760002484385088250244999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274026673291693568667319997 102760002484385088250244999)
      ·
        refine ⟨154140003726577632375367499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102760002484385088250244999 154140003726577632375367499)
        ·
          refine ⟨231210005589866448563051249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154140003726577632375367499 231210005589866448563051249)
          ·
            refine ⟨173407504192399836422288437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231210005589866448563051249 173407504192399836422288437)
            ·
              refine ⟨16256953518037484664589541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173407504192399836422288437 16256953518037484664589541)
              ·
                refine ⟨3048178784632028374610539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16256953518037484664589541 3048178784632028374610539)
                ·
                  refine ⟨4572268176948042561915809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048178784632028374610539 4572268176948042561915809)
                  ·
                    refine ⟨3429201132711031921436857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4572268176948042561915809 3429201132711031921436857)
                    ·
                      refine ⟨2571900849533273941077643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429201132711031921436857 2571900849533273941077643)
                      ·
                        rfl

theorem cell23_5008759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_5008759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008759 prefixEnd_5008759 := by exact prefixLift 5008759
  have htrace : WordTrace (prefixWord ++ tailWord_5008759) baseStart_5008759 baseEnd_5008759 := by
    simpa [prefixWord, tailWord_5008759, baseEnd_5008759] using wordTrace_append hprefix tailTrace_5008759
  have hstable : (prefixWord ++ tailWord_5008759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008759).length < 2 ^ (prefixWord ++ tailWord_5008759).sum := by decide
  have hdescent : baseEnd_5008759 < baseStart_5008759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008775 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_5008775 : Nat := 118140960795 + 5008775 * 2 ^ 59
def prefixEnd_5008775 : Nat := 4983230072969 + 3 ^ 40 * 5008775 * 2
def baseEnd_5008775 : Nat := 2571909065223745878477569

theorem tailTrace_5008775 : CollatzResearch.WordTrace tailWord_5008775 prefixEnd_5008775 2571909065223745878477569 := by
  unfold tailWord_5008775
  simp only [CollatzResearch.WordTrace]
  refine ⟨182685032429071080510795779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121790021619380720340530519 182685032429071080510795779)
  ·
    refine ⟨274027548643606620766193669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182685032429071080510795779 274027548643606620766193669)
    ·
      refine ⟨51380165370676241393661313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274027548643606620766193669 51380165370676241393661313)
      ·
        refine ⟨38535124028007181045245985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51380165370676241393661313 38535124028007181045245985)
        ·
          refine ⟨28901343021005385783934489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38535124028007181045245985 28901343021005385783934489)
          ·
            refine ⟨21676007265754039337950867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28901343021005385783934489 21676007265754039337950867)
            ·
              refine ⟨32514010898631059006926301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21676007265754039337950867 32514010898631059006926301)
              ·
                refine ⟨12192754086986647127597363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32514010898631059006926301 12192754086986647127597363)
                ·
                  refine ⟨18289131130479970691396045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12192754086986647127597363 18289131130479970691396045)
                  ·
                    refine ⟨6858424173929989009273517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18289131130479970691396045 6858424173929989009273517)
                    ·
                      refine ⟨2571909065223745878477569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6858424173929989009273517 2571909065223745878477569)
                      ·
                        rfl

theorem cell23_5008775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_5008775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008775 prefixEnd_5008775 := by exact prefixLift 5008775
  have htrace : WordTrace (prefixWord ++ tailWord_5008775) baseStart_5008775 baseEnd_5008775 := by
    simpa [prefixWord, tailWord_5008775, baseEnd_5008775] using wordTrace_append hprefix tailTrace_5008775
  have hstable : (prefixWord ++ tailWord_5008775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008775).length < 2 ^ (prefixWord ++ tailWord_5008775).sum := by decide
  have hdescent : baseEnd_5008775 < baseStart_5008775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008782 : List Nat := [4, 1, 1, 4, 2, 1, 3, 7]
def baseStart_5008782 : Nat := 118140960795 + 5008782 * 2 ^ 59
def prefixEnd_5008782 : Nat := 4983230072969 + 3 ^ 40 * 5008782 * 2
def baseEnd_5008782 : Nat := 95256024429197309299631

theorem tailTrace_5008782 : CollatzResearch.WordTrace tailWord_5008782 prefixEnd_5008782 95256024429197309299631 := by
  unfold tailWord_5008782
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835660967505715088287575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121790191826697147137533733 22835660967505715088287575)
  ·
    refine ⟨34253491451258572632431363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22835660967505715088287575 34253491451258572632431363)
    ·
      refine ⟨51380237176887858948647045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34253491451258572632431363 51380237176887858948647045)
      ·
        refine ⟨9633794470666473552871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51380237176887858948647045 9633794470666473552871321)
        ·
          refine ⟨7225345852999855164653491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9633794470666473552871321 7225345852999855164653491)
          ·
            refine ⟨10838018779499782746980237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225345852999855164653491 10838018779499782746980237)
            ·
              refine ⟨4064257042312418530117589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10838018779499782746980237 4064257042312418530117589)
              ·
                refine ⟨95256024429197309299631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4064257042312418530117589 95256024429197309299631)
                ·
                  rfl

theorem cell23_5008782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_5008782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008782 prefixEnd_5008782 := by exact prefixLift 5008782
  have htrace : WordTrace (prefixWord ++ tailWord_5008782) baseStart_5008782 baseEnd_5008782 := by
    simpa [prefixWord, tailWord_5008782, baseEnd_5008782] using wordTrace_append hprefix tailTrace_5008782
  have hstable : (prefixWord ++ tailWord_5008782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008782).length < 2 ^ (prefixWord ++ tailWord_5008782).sum := by decide
  have hdescent : baseEnd_5008782 < baseStart_5008782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008815 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 3, 4, 2]
def baseStart_5008815 : Nat := 118140960795 + 5008815 * 2 ^ 59
def prefixEnd_5008815 : Nat := 4983230072969 + 3 ^ 40 * 5008815 * 2
def baseEnd_5008815 : Nat := 2571929604449925721977385

theorem tailTrace_5008815 : CollatzResearch.WordTrace tailWord_5008815 prefixEnd_5008815 2571929604449925721977385 := by
  unfold tailWord_5008815
  simp only [CollatzResearch.WordTrace]
  refine ⟨182686491348926167342251899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121790994232617444894834599 182686491348926167342251899)
  ·
    refine ⟨274029737023389251013377849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182686491348926167342251899 274029737023389251013377849)
    ·
      refine ⟨205522302767541938260033387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274029737023389251013377849 205522302767541938260033387)
      ·
        refine ⟨308283454151312907390050081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205522302767541938260033387 308283454151312907390050081)
        ·
          refine ⟨231212590613484680542537561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308283454151312907390050081 231212590613484680542537561)
          ·
            refine ⟨173409442960113510406903171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231212590613484680542537561 173409442960113510406903171)
            ·
              refine ⟨260114164440170265610354757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173409442960113510406903171 260114164440170265610354757)
              ·
                refine ⟨48771405832531924801941517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260114164440170265610354757 48771405832531924801941517)
                ·
                  refine ⟨18289277187199471800728069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48771405832531924801941517 18289277187199471800728069)
                  ·
                    refine ⟨3429239472599900962636513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18289277187199471800728069 3429239472599900962636513)
                    ·
                      refine ⟨2571929604449925721977385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429239472599900962636513 2571929604449925721977385)
                      ·
                        rfl

theorem cell23_5008815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 4, 2].length) (baseStart_5008815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008815 prefixEnd_5008815 := by exact prefixLift 5008815
  have htrace : WordTrace (prefixWord ++ tailWord_5008815) baseStart_5008815 baseEnd_5008815 := by
    simpa [prefixWord, tailWord_5008815, baseEnd_5008815] using wordTrace_append hprefix tailTrace_5008815
  have hstable : (prefixWord ++ tailWord_5008815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008815).length < 2 ^ (prefixWord ++ tailWord_5008815).sum := by decide
  have hdescent : baseEnd_5008815 < baseStart_5008815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008818 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5008818 : Nat := 118140960795 + 5008818 * 2 ^ 59
def prefixEnd_5008818 : Nat := 4983230072969 + 3 ^ 40 * 5008818 * 2
def baseEnd_5008818 : Nat := 2571931144891889210239871

theorem tailTrace_5008818 : CollatzResearch.WordTrace tailWord_5008818 prefixEnd_5008818 2571931144891889210239871 := by
  unfold tailWord_5008818
  simp only [CollatzResearch.WordTrace]
  refine ⟨45671650191978824713652777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121791067178610199236407405 45671650191978824713652777)
  ·
    refine ⟨34253737643984118535239583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45671650191978824713652777 34253737643984118535239583)
    ·
      refine ⟨51380606465976177802859375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34253737643984118535239583 51380606465976177802859375)
      ·
        refine ⟨77070909698964266704289063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51380606465976177802859375 77070909698964266704289063)
        ·
          refine ⟨115606364548446400056433595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77070909698964266704289063 115606364548446400056433595)
          ·
            refine ⟨173409546822669600084650393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115606364548446400056433595 173409546822669600084650393)
            ·
              refine ⟨130057160117002200063487795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173409546822669600084650393 130057160117002200063487795)
              ·
                refine ⟨195085740175503300095231693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130057160117002200063487795 195085740175503300095231693)
                ·
                  refine ⟨73157152565813737535711885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195085740175503300095231693 73157152565813737535711885)
                  ·
                    refine ⟨27433932212180151575891957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73157152565813737535711885 27433932212180151575891957)
                    ·
                      refine ⟨2571931144891889210239871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27433932212180151575891957 2571931144891889210239871)
                      ·
                        rfl

theorem cell23_5008818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5008818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008818 prefixEnd_5008818 := by exact prefixLift 5008818
  have htrace : WordTrace (prefixWord ++ tailWord_5008818) baseStart_5008818 baseEnd_5008818 := by
    simpa [prefixWord, tailWord_5008818, baseEnd_5008818] using wordTrace_append hprefix tailTrace_5008818
  have hstable : (prefixWord ++ tailWord_5008818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008818).length < 2 ^ (prefixWord ++ tailWord_5008818).sum := by decide
  have hdescent : baseEnd_5008818 < baseStart_5008818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008832 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2]
def baseStart_5008832 : Nat := 118140960795 + 5008832 * 2 ^ 59
def prefixEnd_5008832 : Nat := 4983230072969 + 3 ^ 40 * 5008832 * 2
def baseEnd_5008832 : Nat := 2571938333621052155464807

theorem tailTrace_5008832 : CollatzResearch.WordTrace tailWord_5008832 prefixEnd_5008832 2571938333621052155464807 := by
  unfold tailWord_5008832
  simp only [CollatzResearch.WordTrace]
  refine ⟨91343555694932289622810375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121791407593243052830413833 91343555694932289622810375)
  ·
    refine ⟨137015333542398434434215563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91343555694932289622810375 137015333542398434434215563)
    ·
      refine ⟨205523000313597651651323345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137015333542398434434215563 205523000313597651651323345)
      ·
        refine ⟨154142250235198238738492509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205523000313597651651323345 154142250235198238738492509)
        ·
          refine ⟨57803343838199339526934691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154142250235198238738492509 57803343838199339526934691)
          ·
            refine ⟨86705015757299009290402037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57803343838199339526934691 86705015757299009290402037)
            ·
              refine ⟨8128595227246782120975191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86705015757299009290402037 8128595227246782120975191)
              ·
                refine ⟨12192892840870173181462787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128595227246782120975191 12192892840870173181462787)
                ·
                  refine ⟨18289339261305259772194181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12192892840870173181462787 18289339261305259772194181)
                  ·
                    refine ⟨3429251111494736207286409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18289339261305259772194181 3429251111494736207286409)
                    ·
                      refine ⟨2571938333621052155464807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429251111494736207286409 2571938333621052155464807)
                      ·
                        rfl

theorem cell23_5008832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_5008832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008832 prefixEnd_5008832 := by exact prefixLift 5008832
  have htrace : WordTrace (prefixWord ++ tailWord_5008832) baseStart_5008832 baseEnd_5008832 := by
    simpa [prefixWord, tailWord_5008832, baseEnd_5008832] using wordTrace_append hprefix tailTrace_5008832
  have hstable : (prefixWord ++ tailWord_5008832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008832).length < 2 ^ (prefixWord ++ tailWord_5008832).sum := by decide
  have hdescent : baseEnd_5008832 < baseStart_5008832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008836 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5008836 : Nat := 118140960795 + 5008836 * 2 ^ 59
def prefixEnd_5008836 : Nat := 4983230072969 + 3 ^ 40 * 5008836 * 2
def baseEnd_5008836 : Nat := 2571940387543670139814789

theorem tailTrace_5008836 : CollatzResearch.WordTrace tailWord_5008836 prefixEnd_5008836 2571940387543670139814789 := by
  unfold tailWord_5008836
  simp only [CollatzResearch.WordTrace]
  refine ⟨91343628640925043964383181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121791504854566725285844241 91343628640925043964383181)
  ·
    refine ⟨34253860740346891486643693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91343628640925043964383181 34253860740346891486643693)
    ·
      refine ⟨12845197777630084307491385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34253860740346891486643693 12845197777630084307491385)
      ·
        refine ⟨9633898333222563230618539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12845197777630084307491385 9633898333222563230618539)
        ·
          refine ⟨14450847499833844845927809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633898333222563230618539 14450847499833844845927809)
          ·
            refine ⟨10838135624875383634445857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14450847499833844845927809 10838135624875383634445857)
            ·
              refine ⟨8128601718656537725834393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10838135624875383634445857 8128601718656537725834393)
              ·
                refine ⟨6096451288992403294375795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8128601718656537725834393 6096451288992403294375795)
                ·
                  refine ⟨9144676933488604941563693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6096451288992403294375795 9144676933488604941563693)
                  ·
                    refine ⟨3429253850058226853086385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9144676933488604941563693 3429253850058226853086385)
                    ·
                      refine ⟨2571940387543670139814789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429253850058226853086385 2571940387543670139814789)
                      ·
                        rfl

theorem cell23_5008836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5008836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008836 prefixEnd_5008836 := by exact prefixLift 5008836
  have htrace : WordTrace (prefixWord ++ tailWord_5008836) baseStart_5008836 baseEnd_5008836 := by
    simpa [prefixWord, tailWord_5008836, baseEnd_5008836] using wordTrace_append hprefix tailTrace_5008836
  have hstable : (prefixWord ++ tailWord_5008836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008836).length < 2 ^ (prefixWord ++ tailWord_5008836).sum := by decide
  have hdescent : baseEnd_5008836 < baseStart_5008836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008852 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5008852 : Nat := 118140960795 + 5008852 * 2 ^ 59
def prefixEnd_5008852 : Nat := 4983230072969 + 3 ^ 40 * 5008852 * 2
def baseEnd_5008852 : Nat := 2571948603234142077214715

theorem tailTrace_5008852 : CollatzResearch.WordTrace tailWord_5008852 prefixEnd_5008852 2571948603234142077214715 := by
  unfold tailWord_5008852
  simp only [CollatzResearch.WordTrace]
  refine ⟨91343920424896061330674405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121791893899861415107565873 91343920424896061330674405)
  ·
    refine ⟨17126985079668011499501451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91343920424896061330674405 17126985079668011499501451)
    ·
      refine ⟨25690477619502017249252177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17126985079668011499501451 25690477619502017249252177)
      ·
        refine ⟨19267858214626512936939133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25690477619502017249252177 19267858214626512936939133)
        ·
          refine ⟨7225446830484942351352175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19267858214626512936939133 7225446830484942351352175)
          ·
            refine ⟨10838170245727413527028263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225446830484942351352175 10838170245727413527028263)
            ·
              refine ⟨16257255368591120290542395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10838170245727413527028263 16257255368591120290542395)
              ·
                refine ⟨24385883052886680435813593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16257255368591120290542395 24385883052886680435813593)
                ·
                  refine ⟨18289412289665010326860195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24385883052886680435813593 18289412289665010326860195)
                  ·
                    refine ⟨27434118434497515490290293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18289412289665010326860195 27434118434497515490290293)
                    ·
                      refine ⟨2571948603234142077214715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27434118434497515490290293 2571948603234142077214715)
                      ·
                        rfl

theorem cell23_5008852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5008852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008852 prefixEnd_5008852 := by exact prefixLift 5008852
  have htrace : WordTrace (prefixWord ++ tailWord_5008852) baseStart_5008852 baseEnd_5008852 := by
    simpa [prefixWord, tailWord_5008852, baseEnd_5008852] using wordTrace_append hprefix tailTrace_5008852
  have hstable : (prefixWord ++ tailWord_5008852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008852).length < 2 ^ (prefixWord ++ tailWord_5008852).sum := by decide
  have hdescent : baseEnd_5008852 < baseStart_5008852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008922 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_5008922 : Nat := 118140960795 + 5008922 * 2 ^ 59
def prefixEnd_5008922 : Nat := 4983230072969 + 3 ^ 40 * 5008922 * 2
def baseEnd_5008922 : Nat := 2571984546879956803339393

theorem tailTrace_5008922 : CollatzResearch.WordTrace tailWord_5008922 prefixEnd_5008922 2571984546879956803339393 := by
  unfold tailWord_5008922
  simp only [CollatzResearch.WordTrace]
  refine ⟨45672598489884631154099255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121793595973025683077598013 45672598489884631154099255)
  ·
    refine ⟨68508897734826946731148883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45672598489884631154099255 68508897734826946731148883)
    ·
      refine ⟨102763346602240420096723325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68508897734826946731148883 102763346602240420096723325)
      ·
        refine ⟨38536254975840157536271247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102763346602240420096723325 38536254975840157536271247)
        ·
          refine ⟨57804382463760236304406871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38536254975840157536271247 57804382463760236304406871)
          ·
            refine ⟨86706573695640354456610307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57804382463760236304406871 86706573695640354456610307)
            ·
              refine ⟨130059860543460531684915461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86706573695640354456610307 130059860543460531684915461)
              ·
                refine ⟨24386223851898849690921649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130059860543460531684915461 24386223851898849690921649)
                ·
                  refine ⟨18289667888924137268191237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24386223851898849690921649 18289667888924137268191237)
                  ·
                    refine ⟨3429312729173275737785857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18289667888924137268191237 3429312729173275737785857)
                    ·
                      refine ⟨2571984546879956803339393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429312729173275737785857 2571984546879956803339393)
                      ·
                        rfl

theorem cell23_5008922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_5008922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008922 prefixEnd_5008922 := by exact prefixLift 5008922
  have htrace : WordTrace (prefixWord ++ tailWord_5008922) baseStart_5008922 baseEnd_5008922 := by
    simpa [prefixWord, tailWord_5008922, baseEnd_5008922] using wordTrace_append hprefix tailTrace_5008922
  have hstable : (prefixWord ++ tailWord_5008922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008922).length < 2 ^ (prefixWord ++ tailWord_5008922).sum := by decide
  have hdescent : baseEnd_5008922 < baseStart_5008922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008925 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5008925 : Nat := 118140960795 + 5008925 * 2 ^ 59
def prefixEnd_5008925 : Nat := 4983230072969 + 3 ^ 40 * 5008925 * 2
def baseEnd_5008925 : Nat := 2571986087321920291601879

theorem tailTrace_5008925 : CollatzResearch.WordTrace tailWord_5008925 prefixEnd_5008925 2571986087321920291601879 := by
  unfold tailWord_5008925
  simp only [CollatzResearch.WordTrace]
  refine ⟨182690503378527656128756229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121793668919018437419170819 182690503378527656128756229)
  ·
    refine ⟨34254469383473935524141793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182690503378527656128756229 34254469383473935524141793)
    ·
      refine ⟨25690852037605451643106345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34254469383473935524141793 25690852037605451643106345)
      ·
        refine ⟨19268139028204088732329759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25690852037605451643106345 19268139028204088732329759)
        ·
          refine ⟨28902208542306133098494639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19268139028204088732329759 28902208542306133098494639)
          ·
            refine ⟨43353312813459199647741959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28902208542306133098494639 43353312813459199647741959)
            ·
              refine ⟨65029969220188799471612939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43353312813459199647741959 65029969220188799471612939)
              ·
                refine ⟨97544953830283199207419409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65029969220188799471612939 97544953830283199207419409)
                ·
                  refine ⟨73158715372712399405564557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97544953830283199207419409 73158715372712399405564557)
                  ·
                    refine ⟨27434518264767149777086709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73158715372712399405564557 27434518264767149777086709)
                    ·
                      refine ⟨2571986087321920291601879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27434518264767149777086709 2571986087321920291601879)
                      ·
                        rfl

theorem cell23_5008925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5008925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008925 prefixEnd_5008925 := by exact prefixLift 5008925
  have htrace : WordTrace (prefixWord ++ tailWord_5008925) baseStart_5008925 baseEnd_5008925 := by
    simpa [prefixWord, tailWord_5008925, baseEnd_5008925] using wordTrace_append hprefix tailTrace_5008925
  have hstable : (prefixWord ++ tailWord_5008925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008925).length < 2 ^ (prefixWord ++ tailWord_5008925).sum := by decide
  have hdescent : baseEnd_5008925 < baseStart_5008925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008956 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_5008956 : Nat := 118140960795 + 5008956 * 2 ^ 59
def prefixEnd_5008956 : Nat := 4983230072969 + 3 ^ 40 * 5008956 * 2
def baseEnd_5008956 : Nat := 2572002005222209670314237

theorem tailTrace_5008956 : CollatzResearch.WordTrace tailWord_5008956 prefixEnd_5008956 2572002005222209670314237 := by
  unfold tailWord_5008956
  simp only [CollatzResearch.WordTrace]
  refine ⟨91345817020707674211567361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121794422694276898948756481 91345817020707674211567361)
  ·
    refine ⟨68509362765530755658675521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91345817020707674211567361 68509362765530755658675521)
    ·
      refine ⟨51382022074148066744006641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68509362765530755658675521 51382022074148066744006641)
      ·
        refine ⟨38536516555611050058004981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51382022074148066744006641 38536516555611050058004981)
        ·
          refine ⟨3612798427088535942937967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38536516555611050058004981 3612798427088535942937967)
          ·
            refine ⟨5419197640632803914406951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612798427088535942937967 5419197640632803914406951)
            ·
              refine ⟨8128796460949205871610427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419197640632803914406951 8128796460949205871610427)
              ·
                refine ⟨12193194691423808807415641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128796460949205871610427 12193194691423808807415641)
                ·
                  refine ⟨9144896018567856605561731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12193194691423808807415641 9144896018567856605561731)
                  ·
                    refine ⟨13717344027851784908342597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9144896018567856605561731 13717344027851784908342597)
                    ·
                      refine ⟨2572002005222209670314237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13717344027851784908342597 2572002005222209670314237)
                      ·
                        rfl

theorem cell23_5008956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_5008956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008956 prefixEnd_5008956 := by exact prefixLift 5008956
  have htrace : WordTrace (prefixWord ++ tailWord_5008956) baseStart_5008956 baseEnd_5008956 := by
    simpa [prefixWord, tailWord_5008956, baseEnd_5008956] using wordTrace_append hprefix tailTrace_5008956
  have hstable : (prefixWord ++ tailWord_5008956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008956).length < 2 ^ (prefixWord ++ tailWord_5008956).sum := by decide
  have hdescent : baseEnd_5008956 < baseStart_5008956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5008959 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_5008959 : Nat := 118140960795 + 5008959 * 2 ^ 59
def prefixEnd_5008959 : Nat := 4983230072969 + 3 ^ 40 * 5008959 * 2
def baseEnd_5008959 : Nat := 2572003545664173158576723

theorem tailTrace_5008959 : CollatzResearch.WordTrace tailWord_5008959 prefixEnd_5008959 2572003545664173158576723 := by
  unfold tailWord_5008959
  simp only [CollatzResearch.WordTrace]
  refine ⟨182691743460404479935493931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121794495640269653290329287 182691743460404479935493931)
  ·
    refine ⟨274037615190606719903240897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182691743460404479935493931 274037615190606719903240897)
    ·
      refine ⟨205528211392955039927430673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274037615190606719903240897 205528211392955039927430673)
      ·
        refine ⟨154146158544716279945573005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205528211392955039927430673 154146158544716279945573005)
        ·
          refine ⟨57804809454268604979589877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154146158544716279945573005 57804809454268604979589877)
          ·
            refine ⟨5419200886337681716836551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57804809454268604979589877 5419200886337681716836551)
            ·
              refine ⟨8128801329506522575254827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419200886337681716836551 8128801329506522575254827)
              ·
                refine ⟨12193201994259783862882241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128801329506522575254827 12193201994259783862882241)
                ·
                  refine ⟨9144901495694837897161681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12193201994259783862882241 9144901495694837897161681)
                  ·
                    refine ⟨6858676121771128422871261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9144901495694837897161681 6858676121771128422871261)
                    ·
                      refine ⟨2572003545664173158576723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6858676121771128422871261 2572003545664173158576723)
                      ·
                        rfl

theorem cell23_5008959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_5008959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5008959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5008959 prefixEnd_5008959 := by exact prefixLift 5008959
  have htrace : WordTrace (prefixWord ++ tailWord_5008959) baseStart_5008959 baseEnd_5008959 := by
    simpa [prefixWord, tailWord_5008959, baseEnd_5008959] using wordTrace_append hprefix tailTrace_5008959
  have hstable : (prefixWord ++ tailWord_5008959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5008959).length < 2 ^ (prefixWord ++ tailWord_5008959).sum := by decide
  have hdescent : baseEnd_5008959 < baseStart_5008959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5008959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009015 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_5009015 : Nat := 118140960795 + 5009015 * 2 ^ 59
def prefixEnd_5009015 : Nat := 4983230072969 + 3 ^ 40 * 5009015 * 2
def baseEnd_5009015 : Nat := 2572032300580824939476465

theorem tailTrace_5009015 : CollatzResearch.WordTrace tailWord_5009015 prefixEnd_5009015 2572032300580824939476465 := by
  unfold tailWord_5009015
  simp only [CollatzResearch.WordTrace]
  refine ⟨182693785948201601499532499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121795857298801067666354999 182693785948201601499532499)
  ·
    refine ⟨274040678922302402249298749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182693785948201601499532499 274040678922302402249298749)
    ·
      refine ⟨102765254595863400843487031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274040678922302402249298749 102765254595863400843487031)
      ·
        refine ⟨154147881893795101265230547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102765254595863400843487031 154147881893795101265230547)
        ·
          refine ⟨231221822840692651897845821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154147881893795101265230547 231221822840692651897845821)
          ·
            refine ⟨86708183565259744461692183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231221822840692651897845821 86708183565259744461692183)
            ·
              refine ⟨130062275347889616692538275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86708183565259744461692183 130062275347889616692538275)
              ·
                refine ⟨195093413021834425038807413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130062275347889616692538275 195093413021834425038807413)
                ·
                  refine ⟨18290007470796977347388195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195093413021834425038807413 18290007470796977347388195)
                  ·
                    refine ⟨27435011206195466021082293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18290007470796977347388195 27435011206195466021082293)
                    ·
                      refine ⟨2572032300580824939476465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27435011206195466021082293 2572032300580824939476465)
                      ·
                        rfl

theorem cell23_5009015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_5009015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009015 prefixEnd_5009015 := by exact prefixLift 5009015
  have htrace : WordTrace (prefixWord ++ tailWord_5009015) baseStart_5009015 baseEnd_5009015 := by
    simpa [prefixWord, tailWord_5009015, baseEnd_5009015] using wordTrace_append hprefix tailTrace_5009015
  have hstable : (prefixWord ++ tailWord_5009015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009015).length < 2 ^ (prefixWord ++ tailWord_5009015).sum := by decide
  have hdescent : baseEnd_5009015 < baseStart_5009015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009056 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 2, 4]
def baseStart_5009056 : Nat := 118140960795 + 5009056 * 2 ^ 59
def prefixEnd_5009056 : Nat := 4983230072969 + 3 ^ 40 * 5009056 * 2
def baseEnd_5009056 : Nat := 857351117762553093021259

theorem tailTrace_5009056 : CollatzResearch.WordTrace tailWord_5009056 prefixEnd_5009056 857351117762553093021259 := by
  unfold tailWord_5009056
  simp only [CollatzResearch.WordTrace]
  refine ⟨91347640670526532750887511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121796854227368710334516681 91347640670526532750887511)
  ·
    refine ⟨137021461005789799126331267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91347640670526532750887511 137021461005789799126331267)
    ·
      refine ⟨205532191508684698689496901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137021461005789799126331267 205532191508684698689496901)
      ·
        refine ⟨38537285907878381004280669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205532191508684698689496901 38537285907878381004280669)
        ·
          refine ⟨14451482215454392876605251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38537285907878381004280669 14451482215454392876605251)
          ·
            refine ⟨21677223323181589314907877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14451482215454392876605251 21677223323181589314907877)
            ·
              refine ⟨4064479373096547996545227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21677223323181589314907877 4064479373096547996545227)
              ·
                refine ⟨6096719059644821994817841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064479373096547996545227 6096719059644821994817841)
                ·
                  refine ⟨4572539294733616496113381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6096719059644821994817841 4572539294733616496113381)
                  ·
                    refine ⟨857351117762553093021259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572539294733616496113381 857351117762553093021259)
                    ·
                      rfl

theorem cell23_5009056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_5009056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009056 prefixEnd_5009056 := by exact prefixLift 5009056
  have htrace : WordTrace (prefixWord ++ tailWord_5009056) baseStart_5009056 baseEnd_5009056 := by
    simpa [prefixWord, tailWord_5009056, baseEnd_5009056] using wordTrace_append hprefix tailTrace_5009056
  have hstable : (prefixWord ++ tailWord_5009056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009056).length < 2 ^ (prefixWord ++ tailWord_5009056).sum := by decide
  have hdescent : baseEnd_5009056 < baseStart_5009056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009079 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_5009079 : Nat := 118140960795 + 5009079 * 2 ^ 59
def prefixEnd_5009079 : Nat := 4983230072969 + 3 ^ 40 * 5009079 * 2
def baseEnd_5009079 : Nat := 2572065163342712689076171

theorem tailTrace_5009079 : CollatzResearch.WordTrace tailWord_5009079 prefixEnd_5009079 2572065163342712689076171 := by
  unfold tailWord_5009079
  simp only [CollatzResearch.WordTrace]
  refine ⟨182696120219969740429862291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121797413479979826953241527 182696120219969740429862291)
  ·
    refine ⟨274044180329954610644793437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182696120219969740429862291 274044180329954610644793437)
    ·
      refine ⟨102766567623732978991797539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274044180329954610644793437 102766567623732978991797539)
      ·
        refine ⟨154149851435599468487696309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102766567623732978991797539 154149851435599468487696309)
        ·
          refine ⟨14451548572087450170721529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154149851435599468487696309 14451548572087450170721529)
          ·
            refine ⟨10838661429065587628041147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14451548572087450170721529 10838661429065587628041147)
            ·
              refine ⟨16257992143598381442061721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10838661429065587628041147 16257992143598381442061721)
              ·
                refine ⟨12193494107698786081546291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16257992143598381442061721 12193494107698786081546291)
                ·
                  refine ⟨18290241161548179122319437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12193494107698786081546291 18290241161548179122319437)
                  ·
                    refine ⟨6858840435580567170869789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18290241161548179122319437 6858840435580567170869789)
                    ·
                      refine ⟨2572065163342712689076171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6858840435580567170869789 2572065163342712689076171)
                      ·
                        rfl

theorem cell23_5009079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_5009079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009079 prefixEnd_5009079 := by exact prefixLift 5009079
  have htrace : WordTrace (prefixWord ++ tailWord_5009079) baseStart_5009079 baseEnd_5009079 := by
    simpa [prefixWord, tailWord_5009079, baseEnd_5009079] using wordTrace_append hprefix tailTrace_5009079
  have hstable : (prefixWord ++ tailWord_5009079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009079).length < 2 ^ (prefixWord ++ tailWord_5009079).sum := by decide
  have hdescent : baseEnd_5009079 < baseStart_5009079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009096 : List Nat := [2, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_5009096 : Nat := 118140960795 + 5009096 * 2 ^ 59
def prefixEnd_5009096 : Nat := 4983230072969 + 3 ^ 40 * 5009096 * 2
def baseEnd_5009096 : Nat := 2572073892513839122563593

theorem tailTrace_5009096 : CollatzResearch.WordTrace tailWord_5009096 prefixEnd_5009096 2572073892513839122563593 := by
  unfold tailWord_5009096
  simp only [CollatzResearch.WordTrace]
  refine ⟨91348370130454076166615571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121797826840605434888820761 91348370130454076166615571)
  ·
    refine ⟨137022555195681114249923357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91348370130454076166615571 137022555195681114249923357)
    ·
      refine ⟨51383458198380417843721259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137022555195681114249923357 51383458198380417843721259)
      ·
        refine ⟨77075187297570626765581889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51383458198380417843721259 77075187297570626765581889)
        ·
          refine ⟨57806390473177970074186417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77075187297570626765581889 57806390473177970074186417)
          ·
            refine ⟨43354792854883477555639813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57806390473177970074186417 43354792854883477555639813)
            ·
              refine ⟨8129023660290652041682465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43354792854883477555639813 8129023660290652041682465)
              ·
                refine ⟨6096767745217989031261849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8129023660290652041682465 6096767745217989031261849)
                ·
                  refine ⟨4572575808913491773446387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6096767745217989031261849 4572575808913491773446387)
                  ·
                    refine ⟨6858863713370237660169581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4572575808913491773446387 6858863713370237660169581)
                    ·
                      refine ⟨2572073892513839122563593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6858863713370237660169581 2572073892513839122563593)
                      ·
                        rfl

theorem cell23_5009096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_5009096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009096 prefixEnd_5009096 := by exact prefixLift 5009096
  have htrace : WordTrace (prefixWord ++ tailWord_5009096) baseStart_5009096 baseEnd_5009096 := by
    simpa [prefixWord, tailWord_5009096, baseEnd_5009096] using wordTrace_append hprefix tailTrace_5009096
  have hstable : (prefixWord ++ tailWord_5009096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009096).length < 2 ^ (prefixWord ++ tailWord_5009096).sum := by decide
  have hdescent : baseEnd_5009096 < baseStart_5009096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009102 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_5009102 : Nat := 118140960795 + 5009102 * 2 ^ 59
def prefixEnd_5009102 : Nat := 4983230072969 + 3 ^ 40 * 5009102 * 2
def baseEnd_5009102 : Nat := 2572076973397766099088565

theorem tailTrace_5009102 : CollatzResearch.WordTrace tailWord_5009102 prefixEnd_5009102 2572076973397766099088565 := by
  unfold tailWord_5009102
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837119887360801919743695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121797972732590943571966373 22837119887360801919743695)
  ·
    refine ⟨34255679831041202879615543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22837119887360801919743695 34255679831041202879615543)
    ·
      refine ⟨51383519746561804319423315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34255679831041202879615543 51383519746561804319423315)
      ·
        refine ⟨77075279619842706479134973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51383519746561804319423315 77075279619842706479134973)
        ·
          refine ⟨28903229857441014929675615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77075279619842706479134973 28903229857441014929675615)
          ·
            refine ⟨43354844786161522394513423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28903229857441014929675615 43354844786161522394513423)
            ·
              refine ⟨65032267179242283591770135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43354844786161522394513423 65032267179242283591770135)
              ·
                refine ⟨97548400768863425387655203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65032267179242283591770135 97548400768863425387655203)
                ·
                  refine ⟨146322601153295138081482805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97548400768863425387655203 146322601153295138081482805)
                  ·
                    refine ⟨13717743858121419195139013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146322601153295138081482805 13717743858121419195139013)
                    ·
                      refine ⟨2572076973397766099088565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13717743858121419195139013 2572076973397766099088565)
                      ·
                        rfl

theorem cell23_5009102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_5009102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009102 prefixEnd_5009102 := by exact prefixLift 5009102
  have htrace : WordTrace (prefixWord ++ tailWord_5009102) baseStart_5009102 baseEnd_5009102 := by
    simpa [prefixWord, tailWord_5009102, baseEnd_5009102] using wordTrace_append hprefix tailTrace_5009102
  have hstable : (prefixWord ++ tailWord_5009102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009102).length < 2 ^ (prefixWord ++ tailWord_5009102).sum := by decide
  have hdescent : baseEnd_5009102 < baseStart_5009102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009106 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5009106 : Nat := 118140960795 + 5009106 * 2 ^ 59
def prefixEnd_5009106 : Nat := 4983230072969 + 3 ^ 40 * 5009106 * 2
def baseEnd_5009106 : Nat := 2572079027320384083438547

theorem tailTrace_5009106 : CollatzResearch.WordTrace tailWord_5009106 prefixEnd_5009106 2572079027320384083438547 := by
  unfold tailWord_5009106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674276247717981010273793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121798069993914616027396781 45674276247717981010273793)
  ·
    refine ⟨34255707185788485757705345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45674276247717981010273793 34255707185788485757705345)
    ·
      refine ⟨25691780389341364318279009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34255707185788485757705345 25691780389341364318279009)
      ·
        refine ⟨19268835292006023238709257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25691780389341364318279009 19268835292006023238709257)
        ·
          refine ⟨14451626469004517429031943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19268835292006023238709257 14451626469004517429031943)
          ·
            refine ⟨21677439703506776143547915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14451626469004517429031943 21677439703506776143547915)
            ·
              refine ⟨32516159555260164215321873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21677439703506776143547915 32516159555260164215321873)
              ·
                refine ⟨24387119666445123161491405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32516159555260164215321873 24387119666445123161491405)
                ·
                  refine ⟨9145169874916921185559277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24387119666445123161491405 9145169874916921185559277)
                  ·
                    refine ⟨3429438703093845444584729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9145169874916921185559277 3429438703093845444584729)
                    ·
                      refine ⟨2572079027320384083438547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429438703093845444584729 2572079027320384083438547)
                      ·
                        rfl

theorem cell23_5009106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5009106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009106 prefixEnd_5009106 := by exact prefixLift 5009106
  have htrace : WordTrace (prefixWord ++ tailWord_5009106) baseStart_5009106 baseEnd_5009106 := by
    simpa [prefixWord, tailWord_5009106, baseEnd_5009106] using wordTrace_append hprefix tailTrace_5009106
  have hstable : (prefixWord ++ tailWord_5009106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009106).length < 2 ^ (prefixWord ++ tailWord_5009106).sum := by decide
  have hdescent : baseEnd_5009106 < baseStart_5009106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009112 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_5009112 : Nat := 118140960795 + 5009112 * 2 ^ 59
def prefixEnd_5009112 : Nat := 4983230072969 + 3 ^ 40 * 5009112 * 2
def baseEnd_5009112 : Nat := 857360702734770353321173

theorem tailTrace_5009112 : CollatzResearch.WordTrace tailWord_5009112 prefixEnd_5009112 857360702734770353321173 := by
  unfold tailWord_5009112
  simp only [CollatzResearch.WordTrace]
  refine ⟨91348661914425093532906795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121798215885900124710542393 91348661914425093532906795)
  ·
    refine ⟨137022992871637640299360193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91348661914425093532906795 137022992871637640299360193)
    ·
      refine ⟨102767244653728230224520145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137022992871637640299360193 102767244653728230224520145)
      ·
        refine ⟨77075433490296172668390109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102767244653728230224520145 77075433490296172668390109)
        ·
          refine ⟨28903287558861064750646291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77075433490296172668390109 28903287558861064750646291)
          ·
            refine ⟨43354931338291597125969437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28903287558861064750646291 43354931338291597125969437)
            ·
              refine ⟨16258099251859348922238539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43354931338291597125969437 16258099251859348922238539)
              ·
                refine ⟨24387148877789023383357809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16258099251859348922238539 24387148877789023383357809)
                ·
                  refine ⟨18290361658341767537518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24387148877789023383357809 18290361658341767537518357)
                  ·
                    refine ⟨857360702734770353321173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18290361658341767537518357 857360702734770353321173)
                    ·
                      rfl

theorem cell23_5009112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_5009112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009112 prefixEnd_5009112 := by exact prefixLift 5009112
  have htrace : WordTrace (prefixWord ++ tailWord_5009112) baseStart_5009112 baseEnd_5009112 := by
    simpa [prefixWord, tailWord_5009112, baseEnd_5009112] using wordTrace_append hprefix tailTrace_5009112
  have hstable : (prefixWord ++ tailWord_5009112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009112).length < 2 ^ (prefixWord ++ tailWord_5009112).sum := by decide
  have hdescent : baseEnd_5009112 < baseStart_5009112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009115 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_5009115 : Nat := 118140960795 + 5009115 * 2 ^ 59
def prefixEnd_5009115 : Nat := 4983230072969 + 3 ^ 40 * 5009115 * 2
def baseEnd_5009115 : Nat := 2572083648646274548226005

theorem tailTrace_5009115 : CollatzResearch.WordTrace tailWord_5009115 prefixEnd_5009115 2572083648646274548226005 := by
  unfold tailWord_5009115
  simp only [CollatzResearch.WordTrace]
  refine ⟨182697433247839318578172799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121798288831892879052115199 182697433247839318578172799)
  ·
    refine ⟨274046149871758977867259199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182697433247839318578172799 274046149871758977867259199)
    ·
      refine ⟨411069224807638466800888799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274046149871758977867259199 411069224807638466800888799)
      ·
        refine ⟨616603837211457700201333199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411069224807638466800888799 616603837211457700201333199)
        ·
          refine ⟨924905755817186550301999799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616603837211457700201333199 924905755817186550301999799)
          ·
            refine ⟨1387358633725779825452999699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924905755817186550301999799 1387358633725779825452999699)
            ·
              refine ⟨2081037950588669738179499549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387358633725779825452999699 2081037950588669738179499549)
              ·
                refine ⟨780389231470751151817312331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081037950588669738179499549 780389231470751151817312331)
                ·
                  refine ⟨1170583847206126727725968497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780389231470751151817312331 1170583847206126727725968497)
                  ·
                    refine ⟨877937885404595045794476373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1170583847206126727725968497 877937885404595045794476373)
                    ·
                      refine ⟨2572083648646274548226005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 877937885404595045794476373 2572083648646274548226005)
                      ·
                        rfl

theorem cell23_5009115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_5009115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009115 prefixEnd_5009115 := by exact prefixLift 5009115
  have htrace : WordTrace (prefixWord ++ tailWord_5009115) baseStart_5009115 baseEnd_5009115 := by
    simpa [prefixWord, tailWord_5009115, baseEnd_5009115] using wordTrace_append hprefix tailTrace_5009115
  have hstable : (prefixWord ++ tailWord_5009115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009115).length < 2 ^ (prefixWord ++ tailWord_5009115).sum := by decide
  have hdescent : baseEnd_5009115 < baseStart_5009115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009152 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_5009152 : Nat := 118140960795 + 5009152 * 2 ^ 59
def prefixEnd_5009152 : Nat := 4983230072969 + 3 ^ 40 * 5009152 * 2
def baseEnd_5009152 : Nat := 2572102647430490903463335

theorem tailTrace_5009152 : CollatzResearch.WordTrace tailWord_5009152 prefixEnd_5009152 2572102647430490903463335 := by
  unfold tailWord_5009152
  simp only [CollatzResearch.WordTrace]
  refine ⟨91349391374352636948634855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121799188499136849264846473 91349391374352636948634855)
  ·
    refine ⟨137024087061528955422952283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91349391374352636948634855 137024087061528955422952283)
    ·
      refine ⟨205536130592293433134428425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137024087061528955422952283 205536130592293433134428425)
      ·
        refine ⟨154152097944220074850821319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205536130592293433134428425 154152097944220074850821319)
        ·
          refine ⟨231228146916330112276231979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154152097944220074850821319 231228146916330112276231979)
          ·
            refine ⟨346842220374495168414347969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231228146916330112276231979 346842220374495168414347969)
            ·
              refine ⟨260131665280871376310760977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346842220374495168414347969 260131665280871376310760977)
              ·
                refine ⟨195098748960653532233070733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260131665280871376310760977 195098748960653532233070733)
                ·
                  refine ⟨73162030860245074587401525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195098748960653532233070733 73162030860245074587401525)
                  ·
                    refine ⟨6858940393147975742568893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73162030860245074587401525 6858940393147975742568893)
                    ·
                      refine ⟨2572102647430490903463335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6858940393147975742568893 2572102647430490903463335)
                      ·
                        rfl

theorem cell23_5009152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_5009152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009152 prefixEnd_5009152 := by exact prefixLift 5009152
  have htrace : WordTrace (prefixWord ++ tailWord_5009152) baseStart_5009152 baseEnd_5009152 := by
    simpa [prefixWord, tailWord_5009152, baseEnd_5009152] using wordTrace_append hprefix tailTrace_5009152
  have hstable : (prefixWord ++ tailWord_5009152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009152).length < 2 ^ (prefixWord ++ tailWord_5009152).sum := by decide
  have hdescent : baseEnd_5009152 < baseStart_5009152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009153 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_5009153 : Nat := 118140960795 + 5009153 * 2 ^ 59
def prefixEnd_5009153 : Nat := 4983230072969 + 3 ^ 40 * 5009153 * 2
def baseEnd_5009153 : Nat := 2572103160911145399550831

theorem tailTrace_5009153 : CollatzResearch.WordTrace tailWord_5009153 prefixEnd_5009153 2572103160911145399550831 := by
  unfold tailWord_5009153
  simp only [CollatzResearch.WordTrace]
  refine ⟨182698819221701651068056113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121799212814467767378704075 182698819221701651068056113)
  ·
    refine ⟨137024114416276238301042085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182698819221701651068056113 137024114416276238301042085)
    ·
      refine ⟨25692021453051794681445391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137024114416276238301042085 25692021453051794681445391)
      ·
        refine ⟨38538032179577692022168087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25692021453051794681445391 38538032179577692022168087)
        ·
          refine ⟨57807048269366538033252131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38538032179577692022168087 57807048269366538033252131)
          ·
            refine ⟨86710572404049807049878197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57807048269366538033252131 86710572404049807049878197)
            ·
              refine ⟨8129116162879669410926081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86710572404049807049878197 8129116162879669410926081)
              ·
                refine ⟨6096837122159752058194561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8129116162879669410926081 6096837122159752058194561)
                ·
                  refine ⟨4572627841619814043645921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6096837122159752058194561 4572627841619814043645921)
                  ·
                    refine ⟨3429470881214860532734441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4572627841619814043645921 3429470881214860532734441)
                    ·
                      refine ⟨2572103160911145399550831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429470881214860532734441 2572103160911145399550831)
                      ·
                        rfl

theorem cell23_5009153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_5009153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009153 prefixEnd_5009153 := by exact prefixLift 5009153
  have htrace : WordTrace (prefixWord ++ tailWord_5009153) baseStart_5009153 baseEnd_5009153 := by
    simpa [prefixWord, tailWord_5009153, baseEnd_5009153] using wordTrace_append hprefix tailTrace_5009153
  have hstable : (prefixWord ++ tailWord_5009153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009153).length < 2 ^ (prefixWord ++ tailWord_5009153).sum := by decide
  have hdescent : baseEnd_5009153 < baseStart_5009153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009170 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5009170 : Nat := 118140960795 + 5009170 * 2 ^ 59
def prefixEnd_5009170 : Nat := 4983230072969 + 3 ^ 40 * 5009170 * 2
def baseEnd_5009170 : Nat := 2572111890082271833038253

theorem tailTrace_5009170 : CollatzResearch.WordTrace tailWord_5009170 prefixEnd_5009170 2572111890082271833038253 := by
  unfold tailWord_5009170
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674859815660015742856241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121799626175093375314283309 45674859815660015742856241)
  ·
    refine ⟨34256144861745011807142181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45674859815660015742856241 34256144861745011807142181)
    ·
      refine ⟨6423027161577189713839159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34256144861745011807142181 6423027161577189713839159)
      ·
        refine ⟨9634540742365784570758739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6423027161577189713839159 9634540742365784570758739)
        ·
          refine ⟨14451811113548676856138109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9634540742365784570758739 14451811113548676856138109)
          ·
            refine ⟨5419429167580753821051791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14451811113548676856138109 5419429167580753821051791)
            ·
              refine ⟨8129143751371130731577687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419429167580753821051791 8129143751371130731577687)
              ·
                refine ⟨12193715627056696097366531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129143751371130731577687 12193715627056696097366531)
                ·
                  refine ⟨18290573440585044146049797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12193715627056696097366531 18290573440585044146049797)
                  ·
                    refine ⟨3429482520109695777384337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18290573440585044146049797 3429482520109695777384337)
                    ·
                      refine ⟨2572111890082271833038253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429482520109695777384337 2572111890082271833038253)
                      ·
                        rfl

theorem cell23_5009170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5009170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009170 prefixEnd_5009170 := by exact prefixLift 5009170
  have htrace : WordTrace (prefixWord ++ tailWord_5009170) baseStart_5009170 baseEnd_5009170 := by
    simpa [prefixWord, tailWord_5009170, baseEnd_5009170] using wordTrace_append hprefix tailTrace_5009170
  have hstable : (prefixWord ++ tailWord_5009170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009170).length < 2 ^ (prefixWord ++ tailWord_5009170).sum := by decide
  have hdescent : baseEnd_5009170 < baseStart_5009170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009206 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5009206 : Nat := 118140960795 + 5009206 * 2 ^ 59
def prefixEnd_5009206 : Nat := 4983230072969 + 3 ^ 40 * 5009206 * 2
def baseEnd_5009206 : Nat := 857376791795277897396029

theorem tailTrace_5009206 : CollatzResearch.WordTrace tailWord_5009206 prefixEnd_5009206 857376791795277897396029 := by
  unfold tailWord_5009206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418797018156852569983467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121800501527006427413156981 11418797018156852569983467)
  ·
    refine ⟨17128195527235278854975201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11418797018156852569983467 17128195527235278854975201)
    ·
      refine ⟨12846146645426459141231401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17128195527235278854975201 12846146645426459141231401)
      ·
        refine ⟨9634609984069844355923551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12846146645426459141231401 9634609984069844355923551)
        ·
          refine ⟨14451914976104766533885327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9634609984069844355923551 14451914976104766533885327)
          ·
            refine ⟨21677872464157149800827991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14451914976104766533885327 21677872464157149800827991)
            ·
              refine ⟨32516808696235724701241987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21677872464157149800827991 32516808696235724701241987)
              ·
                refine ⟨48775213044353587051862981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32516808696235724701241987 48775213044353587051862981)
                ·
                  refine ⟨9145352445816297572224309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48775213044353587051862981 9145352445816297572224309)
                  ·
                    refine ⟨857376791795277897396029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9145352445816297572224309 857376791795277897396029)
                    ·
                      rfl

theorem cell23_5009206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5009206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009206 prefixEnd_5009206 := by exact prefixLift 5009206
  have htrace : WordTrace (prefixWord ++ tailWord_5009206) baseStart_5009206 baseEnd_5009206 := by
    simpa [prefixWord, tailWord_5009206, baseEnd_5009206] using wordTrace_append hprefix tailTrace_5009206
  have hstable : (prefixWord ++ tailWord_5009206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009206).length < 2 ^ (prefixWord ++ tailWord_5009206).sum := by decide
  have hdescent : baseEnd_5009206 < baseStart_5009206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009269 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5009269 : Nat := 118140960795 + 5009269 * 2 ^ 59
def prefixEnd_5009269 : Nat := 4983230072969 + 3 ^ 40 * 5009269 * 2
def baseEnd_5009269 : Nat := 2572162724667066945700297

theorem tailTrace_5009269 : CollatzResearch.WordTrace tailWord_5009269 prefixEnd_5009269 2572162724667066945700297 := by
  unfold tailWord_5009269
  simp only [CollatzResearch.WordTrace]
  refine ⟨182703050089281402879278861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121802033392854268586185907 182703050089281402879278861)
  ·
    refine ⟨68513643783480526079729573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182703050089281402879278861 68513643783480526079729573)
    ·
      refine ⟨12846308209402598639949295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68513643783480526079729573 12846308209402598639949295)
      ·
        refine ⟨19269462314103897959923943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12846308209402598639949295 19269462314103897959923943)
        ·
          refine ⟨28904193471155846939885915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19269462314103897959923943 28904193471155846939885915)
          ·
            refine ⟨43356290206733770409828873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28904193471155846939885915 43356290206733770409828873)
            ·
              refine ⟨32517217655050327807371655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43356290206733770409828873 32517217655050327807371655)
              ·
                refine ⟨48775826482575491711057483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32517217655050327807371655 48775826482575491711057483)
                ·
                  refine ⟨73163739723863237566586225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48775826482575491711057483 73163739723863237566586225)
                  ·
                    refine ⟨54872804792897428174939669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73163739723863237566586225 54872804792897428174939669)
                    ·
                      refine ⟨2572162724667066945700297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54872804792897428174939669 2572162724667066945700297)
                      ·
                        rfl

theorem cell23_5009269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5009269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009269 prefixEnd_5009269 := by exact prefixLift 5009269
  have htrace : WordTrace (prefixWord ++ tailWord_5009269) baseStart_5009269 baseEnd_5009269 := by
    simpa [prefixWord, tailWord_5009269, baseEnd_5009269] using wordTrace_append hprefix tailTrace_5009269
  have hstable : (prefixWord ++ tailWord_5009269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009269).length < 2 ^ (prefixWord ++ tailWord_5009269).sum := by decide
  have hdescent : baseEnd_5009269 < baseStart_5009269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009303 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_5009303 : Nat := 118140960795 + 5009303 * 2 ^ 59
def prefixEnd_5009303 : Nat := 4983230072969 + 3 ^ 40 * 5009303 * 2
def baseEnd_5009303 : Nat := 2572180183009319812675141

theorem tailTrace_5009303 : CollatzResearch.WordTrace tailWord_5009303 prefixEnd_5009303 2572180183009319812675141 := by
  unfold tailWord_5009303
  simp only [CollatzResearch.WordTrace]
  refine ⟨182704290171158226686016563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121802860114105484457344375 182704290171158226686016563)
  ·
    refine ⟨274056435256737340029024845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182704290171158226686016563 274056435256737340029024845)
    ·
      refine ⟨102771163221276502510884317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274056435256737340029024845 102771163221276502510884317)
      ·
        refine ⟨38539186207978688441581619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102771163221276502510884317 38539186207978688441581619)
        ·
          refine ⟨57808779311968032662372429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38539186207978688441581619 57808779311968032662372429)
          ·
            refine ⟨21678292241988012248389661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57808779311968032662372429 21678292241988012248389661)
            ·
              refine ⟨8129359590745504593146123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21678292241988012248389661 8129359590745504593146123)
              ·
                refine ⟨12194039386118256889719185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129359590745504593146123 12194039386118256889719185)
                ·
                  refine ⟨9145529539588692667289389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12194039386118256889719185 9145529539588692667289389)
                  ·
                    refine ⟨3429573577345759750233521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9145529539588692667289389 3429573577345759750233521)
                    ·
                      refine ⟨2572180183009319812675141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429573577345759750233521 2572180183009319812675141)
                      ·
                        rfl

theorem cell23_5009303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_5009303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009303 prefixEnd_5009303 := by exact prefixLift 5009303
  have htrace : WordTrace (prefixWord ++ tailWord_5009303) baseStart_5009303 baseEnd_5009303 := by
    simpa [prefixWord, tailWord_5009303, baseEnd_5009303] using wordTrace_append hprefix tailTrace_5009303
  have hstable : (prefixWord ++ tailWord_5009303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009303).length < 2 ^ (prefixWord ++ tailWord_5009303).sum := by decide
  have hdescent : baseEnd_5009303 < baseStart_5009303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009313 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_5009313 : Nat := 118140960795 + 5009313 * 2 ^ 59
def prefixEnd_5009313 : Nat := 4983230072969 + 3 ^ 40 * 5009313 * 2
def baseEnd_5009313 : Nat := 857395105938621591183365

theorem tailTrace_5009313 : CollatzResearch.WordTrace tailWord_5009313 prefixEnd_5009313 857395105938621591183365 := by
  unfold tailWord_5009313
  simp only [CollatzResearch.WordTrace]
  refine ⟨182704654901121998393880593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121803103267414665595920395 182704654901121998393880593)
  ·
    refine ⟨137028491175841498795410445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182704654901121998393880593 137028491175841498795410445)
    ·
      refine ⟨51385684190940562048278917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137028491175841498795410445 51385684190940562048278917)
      ·
        refine ⟨9634815785801355384052297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51385684190940562048278917 9634815785801355384052297)
        ·
          refine ⟨7226111839351016538039223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634815785801355384052297 7226111839351016538039223)
          ·
            refine ⟨10839167759026524807058835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226111839351016538039223 10839167759026524807058835)
            ·
              refine ⟨16258751638539787210588253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10839167759026524807058835 16258751638539787210588253)
              ·
                refine ⟨6097031864452420203970595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16258751638539787210588253 6097031864452420203970595)
                ·
                  refine ⟨9145547796678630305955893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097031864452420203970595 9145547796678630305955893)
                  ·
                    refine ⟨857395105938621591183365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9145547796678630305955893 857395105938621591183365)
                    ·
                      rfl

theorem cell23_5009313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_5009313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009313 prefixEnd_5009313 := by exact prefixLift 5009313
  have htrace : WordTrace (prefixWord ++ tailWord_5009313) baseStart_5009313 baseEnd_5009313 := by
    simpa [prefixWord, tailWord_5009313, baseEnd_5009313] using wordTrace_append hprefix tailTrace_5009313
  have hstable : (prefixWord ++ tailWord_5009313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009313).length < 2 ^ (prefixWord ++ tailWord_5009313).sum := by decide
  have hdescent : baseEnd_5009313 < baseStart_5009313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009343 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 2, 4]
def baseStart_5009343 : Nat := 118140960795 + 5009343 * 2 ^ 59
def prefixEnd_5009343 : Nat := 4983230072969 + 3 ^ 40 * 5009343 * 2
def baseEnd_5009343 : Nat := 857400240745166552058319

theorem tailTrace_5009343 : CollatzResearch.WordTrace tailWord_5009343 prefixEnd_5009343 857400240745166552058319 := by
  unfold tailWord_5009343
  simp only [CollatzResearch.WordTrace]
  refine ⟨182705749091013313517472683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121803832727342209011648455 182705749091013313517472683)
  ·
    refine ⟨274058623636519970276209025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182705749091013313517472683 274058623636519970276209025)
    ·
      refine ⟨205543967727389977707156769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274058623636519970276209025 205543967727389977707156769)
      ·
        refine ⟨154157975795542483280367577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205543967727389977707156769 154157975795542483280367577)
        ·
          refine ⟨115618481846656862460275683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154157975795542483280367577 115618481846656862460275683)
          ·
            refine ⟨173427722769985293690413525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115618481846656862460275683 173427722769985293690413525)
            ·
              refine ⟨4064712252421530320869067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173427722769985293690413525 4064712252421530320869067)
              ·
                refine ⟨6097068378632295481303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064712252421530320869067 6097068378632295481303601)
                ·
                  refine ⟨4572801283974221610977701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6097068378632295481303601 4572801283974221610977701)
                  ·
                    refine ⟨857400240745166552058319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572801283974221610977701 857400240745166552058319)
                    ·
                      rfl

theorem cell23_5009343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_5009343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009343 prefixEnd_5009343 := by exact prefixLift 5009343
  have htrace : WordTrace (prefixWord ++ tailWord_5009343) baseStart_5009343 baseEnd_5009343 := by
    simpa [prefixWord, tailWord_5009343, baseEnd_5009343] using wordTrace_append hprefix tailTrace_5009343
  have hstable : (prefixWord ++ tailWord_5009343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009343).length < 2 ^ (prefixWord ++ tailWord_5009343).sum := by decide
  have hdescent : baseEnd_5009343 < baseStart_5009343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009356 : List Nat := [2, 2, 1, 4, 1, 2, 4, 7]
def baseStart_5009356 : Nat := 118140960795 + 5009356 * 2 ^ 59
def prefixEnd_5009356 : Nat := 4983230072969 + 3 ^ 40 * 5009356 * 2
def baseEnd_5009356 : Nat := 95266940647555855752311

theorem tailTrace_5009356 : CollatzResearch.WordTrace tailWord_5009356 prefixEnd_5009356 95266940647555855752311 := by
  unfold tailWord_5009356
  simp only [CollatzResearch.WordTrace]
  refine ⟨91353111619983108368847961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121804148826644144491797281 91353111619983108368847961)
  ·
    refine ⟨68514833714987331276635971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91353111619983108368847961 68514833714987331276635971)
    ·
      refine ⟨102772250572480996914953957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68514833714987331276635971 102772250572480996914953957)
      ·
        refine ⟨19269796982340186921553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102772250572480996914953957 19269796982340186921553867)
        ·
          refine ⟨28904695473510280382330801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19269796982340186921553867 28904695473510280382330801)
          ·
            refine ⟨21678521605132710286748101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28904695473510280382330801 21678521605132710286748101)
            ·
              refine ⟨4064722800962383178765269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21678521605132710286748101 4064722800962383178765269)
              ·
                refine ⟨95266940647555855752311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4064722800962383178765269 95266940647555855752311)
                ·
                  rfl

theorem cell23_5009356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 7].length) (baseStart_5009356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009356 prefixEnd_5009356 := by exact prefixLift 5009356
  have htrace : WordTrace (prefixWord ++ tailWord_5009356) baseStart_5009356 baseEnd_5009356 := by
    simpa [prefixWord, tailWord_5009356, baseEnd_5009356] using wordTrace_append hprefix tailTrace_5009356
  have hstable : (prefixWord ++ tailWord_5009356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009356).length < 2 ^ (prefixWord ++ tailWord_5009356).sum := by decide
  have hdescent : baseEnd_5009356 < baseStart_5009356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009373 : List Nat := [1, 4, 3, 1, 4, 1, 9]
def baseStart_5009373 : Nat := 118140960795 + 5009373 * 2 ^ 59
def prefixEnd_5009373 : Nat := 4983230072969 + 3 ^ 40 * 5009373 * 2
def baseEnd_5009373 : Nat := 31755754650063389367899

theorem tailTrace_5009373 : CollatzResearch.WordTrace tailWord_5009373 prefixEnd_5009373 31755754650063389367899 := by
  unfold tailWord_5009373
  simp only [CollatzResearch.WordTrace]
  refine ⟨182706843280904628641064773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121804562187269752427376515 182706843280904628641064773)
  ·
    refine ⟨34257533115169617870199645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182706843280904628641064773 34257533115169617870199645)
    ·
      refine ⟨12846574918188606701324867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34257533115169617870199645 12846574918188606701324867)
      ·
        refine ⟨19269862377282910051987301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12846574918188606701324867 19269862377282910051987301)
        ·
          refine ⟨3613099195740545634747619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19269862377282910051987301 3613099195740545634747619)
          ·
            refine ⟨5419648793610818452121429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613099195740545634747619 5419648793610818452121429)
            ·
              refine ⟨31755754650063389367899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5419648793610818452121429 31755754650063389367899)
              ·
                rfl

theorem cell23_5009373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 9].length) (baseStart_5009373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009373 prefixEnd_5009373 := by exact prefixLift 5009373
  have htrace : WordTrace (prefixWord ++ tailWord_5009373) baseStart_5009373 baseEnd_5009373 := by
    simpa [prefixWord, tailWord_5009373, baseEnd_5009373] using wordTrace_append hprefix tailTrace_5009373
  have hstable : (prefixWord ++ tailWord_5009373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009373).length < 2 ^ (prefixWord ++ tailWord_5009373).sum := by decide
  have hdescent : baseEnd_5009373 < baseStart_5009373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009400 : List Nat := [2, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_5009400 : Nat := 118140960795 + 5009400 * 2 ^ 59
def prefixEnd_5009400 : Nat := 4983230072969 + 3 ^ 40 * 5009400 * 2
def baseEnd_5009400 : Nat := 2572229990632805933162195

theorem tailTrace_5009400 : CollatzResearch.WordTrace tailWord_5009400 prefixEnd_5009400 2572229990632805933162195 := by
  unfold tailWord_5009400
  simp only [CollatzResearch.WordTrace]
  refine ⟨91353914025903406126148827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121805218701204541501531769 91353914025903406126148827)
  ·
    refine ⟨137030871038855109189223241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91353914025903406126148827 137030871038855109189223241)
    ·
      refine ⟨102773153279141331891917431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137030871038855109189223241 102773153279141331891917431)
      ·
        refine ⟨154159729918711997837876147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102773153279141331891917431 154159729918711997837876147)
        ·
          refine ⟨231239594878067996756814221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154159729918711997837876147 231239594878067996756814221)
          ·
            refine ⟨86714848079275498783805333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231239594878067996756814221 86714848079275498783805333)
            ·
              refine ⟨4064758503716039005490875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86714848079275498783805333 4064758503716039005490875)
              ·
                refine ⟨6097137755574058508236313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064758503716039005490875 6097137755574058508236313)
                ·
                  refine ⟨4572853316680543881177235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6097137755574058508236313 4572853316680543881177235)
                  ·
                    refine ⟨6859279975020815821765853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4572853316680543881177235 6859279975020815821765853)
                    ·
                      refine ⟨2572229990632805933162195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859279975020815821765853 2572229990632805933162195)
                      ·
                        rfl

theorem cell23_5009400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_5009400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009400 prefixEnd_5009400 := by exact prefixLift 5009400
  have htrace : WordTrace (prefixWord ++ tailWord_5009400) baseStart_5009400 baseEnd_5009400 := by
    simpa [prefixWord, tailWord_5009400, baseEnd_5009400] using wordTrace_append hprefix tailTrace_5009400
  have hstable : (prefixWord ++ tailWord_5009400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009400).length < 2 ^ (prefixWord ++ tailWord_5009400).sum := by decide
  have hdescent : baseEnd_5009400 < baseStart_5009400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009414 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5009414 : Nat := 118140960795 + 5009414 * 2 ^ 59
def prefixEnd_5009414 : Nat := 4983230072969 + 3 ^ 40 * 5009414 * 2
def baseEnd_5009414 : Nat := 2572237179361968878387131

theorem tailTrace_5009414 : CollatzResearch.WordTrace tailWord_5009414 prefixEnd_5009414 2572237179361968878387131 := by
  unfold tailWord_5009414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709635583554877895103353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121805559115837395095538197 5709635583554877895103353)
  ·
    refine ⟨4282226687666158421327515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5709635583554877895103353 4282226687666158421327515)
    ·
      refine ⟨6423340031499237631991273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4282226687666158421327515 6423340031499237631991273)
      ·
        refine ⟨4817505023624428223993455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423340031499237631991273 4817505023624428223993455)
        ·
          refine ⟨7226257535436642335990183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817505023624428223993455 7226257535436642335990183)
          ·
            refine ⟨10839386303154963503985275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226257535436642335990183 10839386303154963503985275)
            ·
              refine ⟨16259079454732445255977913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10839386303154963503985275 16259079454732445255977913)
              ·
                refine ⟨12194309591049333941983435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16259079454732445255977913 12194309591049333941983435)
                ·
                  refine ⟨18291464386574000912975153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12194309591049333941983435 18291464386574000912975153)
                  ·
                    refine ⟨13718598289930500684731365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18291464386574000912975153 13718598289930500684731365)
                    ·
                      refine ⟨2572237179361968878387131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13718598289930500684731365 2572237179361968878387131)
                      ·
                        rfl

theorem cell23_5009414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5009414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009414 prefixEnd_5009414 := by exact prefixLift 5009414
  have htrace : WordTrace (prefixWord ++ tailWord_5009414) baseStart_5009414 baseEnd_5009414 := by
    simpa [prefixWord, tailWord_5009414, baseEnd_5009414] using wordTrace_append hprefix tailTrace_5009414
  have hstable : (prefixWord ++ tailWord_5009414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009414).length < 2 ^ (prefixWord ++ tailWord_5009414).sum := by decide
  have hdescent : baseEnd_5009414 < baseStart_5009414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009421 : List Nat := [1, 7, 1, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5009421 : Nat := 118140960795 + 5009421 * 2 ^ 59
def prefixEnd_5009421 : Nat := 4983230072969 + 3 ^ 40 * 5009421 * 2
def baseEnd_5009421 : Nat := 2572240773726550350999599

theorem tailTrace_5009421 : CollatzResearch.WordTrace tailWord_5009421 prefixEnd_5009421 2572240773726550350999599 := by
  unfold tailWord_5009421
  simp only [CollatzResearch.WordTrace]
  refine ⟨182708593984730732838812117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121805729323153821892541411 182708593984730732838812117)
  ·
    refine ⟨4282232671517126550909659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 182708593984730732838812117 4282232671517126550909659)
    ·
      refine ⟨6423349007275689826364489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4282232671517126550909659 6423349007275689826364489)
      ·
        refine ⟨4817511755456767369773367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423349007275689826364489 4817511755456767369773367)
        ·
          refine ⟨7226267633185151054660051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817511755456767369773367 7226267633185151054660051)
          ·
            refine ⟨10839401449777726581990077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226267633185151054660051 10839401449777726581990077)
            ·
              refine ⟨4064775543666647468246279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10839401449777726581990077 4064775543666647468246279)
              ·
                refine ⟨6097163315499971202369419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064775543666647468246279 6097163315499971202369419)
                ·
                  refine ⟨9145744973249956803554129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097163315499971202369419 9145744973249956803554129)
                  ·
                    refine ⟨6859308729937467602665597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9145744973249956803554129 6859308729937467602665597)
                    ·
                      refine ⟨2572240773726550350999599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859308729937467602665597 2572240773726550350999599)
                      ·
                        rfl

theorem cell23_5009421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5009421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009421 prefixEnd_5009421 := by exact prefixLift 5009421
  have htrace : WordTrace (prefixWord ++ tailWord_5009421) baseStart_5009421 baseEnd_5009421 := by
    simpa [prefixWord, tailWord_5009421, baseEnd_5009421] using wordTrace_append hprefix tailTrace_5009421
  have hstable : (prefixWord ++ tailWord_5009421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009421).length < 2 ^ (prefixWord ++ tailWord_5009421).sum := by decide
  have hdescent : baseEnd_5009421 < baseStart_5009421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009456 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_5009456 : Nat := 118140960795 + 5009456 * 2 ^ 59
def prefixEnd_5009456 : Nat := 4983230072969 + 3 ^ 40 * 5009456 * 2
def baseEnd_5009456 : Nat := 2572258745549457714061937

theorem tailTrace_5009456 : CollatzResearch.WordTrace tailWord_5009456 prefixEnd_5009456 2572258745549457714061937 := by
  unfold tailWord_5009456
  simp only [CollatzResearch.WordTrace]
  refine ⟨91354935269801966908168111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121806580359735955877557481 91354935269801966908168111)
  ·
    refine ⟨137032402904702950362252167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91354935269801966908168111 137032402904702950362252167)
    ·
      refine ⟨205548604357054425543378251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137032402904702950362252167 205548604357054425543378251)
      ·
        refine ⟨308322906535581638315067377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205548604357054425543378251 308322906535581638315067377)
        ·
          refine ⟨231242179901686228736300533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308322906535581638315067377 231242179901686228736300533)
          ·
            refine ⟨21678954365783083944028175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231242179901686228736300533 21678954365783083944028175)
            ·
              refine ⟨32518431548674625916042263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21678954365783083944028175 32518431548674625916042263)
              ·
                refine ⟨48777647323011938874063395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32518431548674625916042263 48777647323011938874063395)
                ·
                  refine ⟨73166470984517908311095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48777647323011938874063395 73166470984517908311095093)
                  ·
                    refine ⟨6859356654798553904165165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73166470984517908311095093 6859356654798553904165165)
                    ·
                      refine ⟨2572258745549457714061937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859356654798553904165165 2572258745549457714061937)
                      ·
                        rfl

theorem cell23_5009456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_5009456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009456 prefixEnd_5009456 := by exact prefixLift 5009456
  have htrace : WordTrace (prefixWord ++ tailWord_5009456) baseStart_5009456 baseEnd_5009456 := by
    simpa [prefixWord, tailWord_5009456, baseEnd_5009456] using wordTrace_append hprefix tailTrace_5009456
  have hstable : (prefixWord ++ tailWord_5009456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009456).length < 2 ^ (prefixWord ++ tailWord_5009456).sum := by decide
  have hdescent : baseEnd_5009456 < baseStart_5009456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009513 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 2, 4, 2]
def baseStart_5009513 : Nat := 118140960795 + 5009513 * 2 ^ 59
def prefixEnd_5009513 : Nat := 4983230072969 + 3 ^ 40 * 5009513 * 2
def baseEnd_5009513 : Nat := 2572288013946763991049175

theorem tailTrace_5009513 : CollatzResearch.WordTrace tailWord_5009513 prefixEnd_5009513 2572288013946763991049175 := by
  unfold tailWord_5009513
  simp only [CollatzResearch.WordTrace]
  refine ⟨182711949500397432551161193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121807966333598288367440795 182711949500397432551161193)
  ·
    refine ⟨137033962125298074413370895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182711949500397432551161193 137033962125298074413370895)
    ·
      refine ⟨205550943187947111620056343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137033962125298074413370895 205550943187947111620056343)
      ·
        refine ⟨308326414781920667430084515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205550943187947111620056343 308326414781920667430084515)
        ·
          refine ⟨462489622172881001145126773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308326414781920667430084515 462489622172881001145126773)
          ·
            refine ⟨43358402078707593857355635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 462489622172881001145126773 43358402078707593857355635)
            ·
              refine ⟨65037603118061390786033453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43358402078707593857355635 65037603118061390786033453)
              ·
                refine ⟨24389101169273021544762545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65037603118061390786033453 24389101169273021544762545)
                ·
                  refine ⟨18291825876954766158571909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24389101169273021544762545 18291825876954766158571909)
                  ·
                    refine ⟨3429717351929018654732233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18291825876954766158571909 3429717351929018654732233)
                    ·
                      refine ⟨2572288013946763991049175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429717351929018654732233 2572288013946763991049175)
                      ·
                        rfl

theorem cell23_5009513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4, 2].length) (baseStart_5009513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009513 prefixEnd_5009513 := by exact prefixLift 5009513
  have htrace : WordTrace (prefixWord ++ tailWord_5009513) baseStart_5009513 baseEnd_5009513 := by
    simpa [prefixWord, tailWord_5009513, baseEnd_5009513] using wordTrace_append hprefix tailTrace_5009513
  have hstable : (prefixWord ++ tailWord_5009513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009513).length < 2 ^ (prefixWord ++ tailWord_5009513).sum := by decide
  have hdescent : baseEnd_5009513 < baseStart_5009513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009533 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_5009533 : Nat := 118140960795 + 5009533 * 2 ^ 59
def prefixEnd_5009533 : Nat := 4983230072969 + 3 ^ 40 * 5009533 * 2
def baseEnd_5009533 : Nat := 2572298283559853912799083

theorem tailTrace_5009533 : CollatzResearch.WordTrace tailWord_5009533 prefixEnd_5009533 2572298283559853912799083 := by
  unfold tailWord_5009533
  simp only [CollatzResearch.WordTrace]
  refine ⟨182712678960324975966889253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121808452640216650644592835 182712678960324975966889253)
  ·
    refine ⟨34258627305060932993791735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182712678960324975966889253 34258627305060932993791735)
    ·
      refine ⟨51387940957591399490687603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34258627305060932993791735 51387940957591399490687603)
      ·
        refine ⟨77081911436387099236031405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51387940957591399490687603 77081911436387099236031405)
        ·
          refine ⟨28905716788645162213511777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77081911436387099236031405 28905716788645162213511777)
          ·
            refine ⟨21679287591483871660133833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28905716788645162213511777 21679287591483871660133833)
            ·
              refine ⟨16259465693612903745100375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21679287591483871660133833 16259465693612903745100375)
              ·
                refine ⟨24389198540419355617650563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16259465693612903745100375 24389198540419355617650563)
                ·
                  refine ⟨36583797810629033426475845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24389198540419355617650563 36583797810629033426475845)
                  ·
                    refine ⟨6859462089492943767464221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36583797810629033426475845 6859462089492943767464221)
                    ·
                      refine ⟨2572298283559853912799083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859462089492943767464221 2572298283559853912799083)
                      ·
                        rfl

theorem cell23_5009533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_5009533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009533 prefixEnd_5009533 := by exact prefixLift 5009533
  have htrace : WordTrace (prefixWord ++ tailWord_5009533) baseStart_5009533 baseEnd_5009533 := by
    simpa [prefixWord, tailWord_5009533, baseEnd_5009533] using wordTrace_append hprefix tailTrace_5009533
  have hstable : (prefixWord ++ tailWord_5009533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009533).length < 2 ^ (prefixWord ++ tailWord_5009533).sum := by decide
  have hdescent : baseEnd_5009533 < baseStart_5009533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009557 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_5009557 : Nat := 118140960795 + 5009557 * 2 ^ 59
def prefixEnd_5009557 : Nat := 4983230072969 + 3 ^ 40 * 5009557 * 2
def baseEnd_5009557 : Nat := 857436869031853939632991

theorem tailTrace_5009557 : CollatzResearch.WordTrace tailWord_5009557 prefixEnd_5009557 857436869031853939632991 := by
  unfold tailWord_5009557
  simp only [CollatzResearch.WordTrace]
  refine ⟨182713554312238028065762925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121809036208158685377175283 182713554312238028065762925)
  ·
    refine ⟨68517582867089260524661097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182713554312238028065762925 68517582867089260524661097)
    ·
      refine ⟨51388187150316945393495823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68517582867089260524661097 51388187150316945393495823)
      ·
        refine ⟨77082280725475418090243735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51388187150316945393495823 77082280725475418090243735)
        ·
          refine ⟨115623421088213127135365603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77082280725475418090243735 115623421088213127135365603)
          ·
            refine ⟨173435131632319690703048405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115623421088213127135365603 173435131632319690703048405)
            ·
              refine ⟨4064885897632492750852697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173435131632319690703048405 4064885897632492750852697)
              ·
                refine ⟨3048664423224369563139523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064885897632492750852697 3048664423224369563139523)
                ·
                  refine ⟨4572996634836554344709285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048664423224369563139523 4572996634836554344709285)
                  ·
                    refine ⟨857436869031853939632991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572996634836554344709285 857436869031853939632991)
                    ·
                      rfl

theorem cell23_5009557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_5009557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009557 prefixEnd_5009557 := by exact prefixLift 5009557
  have htrace : WordTrace (prefixWord ++ tailWord_5009557) baseStart_5009557 baseEnd_5009557 := by
    simpa [prefixWord, tailWord_5009557, baseEnd_5009557] using wordTrace_append hprefix tailTrace_5009557
  have hstable : (prefixWord ++ tailWord_5009557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009557).length < 2 ^ (prefixWord ++ tailWord_5009557).sum := by decide
  have hdescent : baseEnd_5009557 < baseStart_5009557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009563 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 3]
def baseStart_5009563 : Nat := 118140960795 + 5009563 * 2 ^ 59
def prefixEnd_5009563 : Nat := 4983230072969 + 3 ^ 40 * 5009563 * 2
def baseEnd_5009563 : Nat := 2572313687979488795423945

theorem tailTrace_5009563 : CollatzResearch.WordTrace tailWord_5009563 prefixEnd_5009563 2572313687979488795423945 := by
  unfold tailWord_5009563
  simp only [CollatzResearch.WordTrace]
  refine ⟨182713773150216291090481343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121809182100144194060320895 182713773150216291090481343)
  ·
    refine ⟨274070659725324436635722015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182713773150216291090481343 274070659725324436635722015)
    ·
      refine ⟨411105989587986654953583023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274070659725324436635722015 411105989587986654953583023)
      ·
        refine ⟨616658984381979982430374535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411105989587986654953583023 616658984381979982430374535)
        ·
          refine ⟨924988476572969973645561803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616658984381979982430374535 924988476572969973645561803)
          ·
            refine ⟨1387482714859454960468342705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924988476572969973645561803 1387482714859454960468342705)
            ·
              refine ⟨1040612036144591220351257029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387482714859454960468342705 1040612036144591220351257029)
              ·
                refine ⟨195114756777110853815860693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1040612036144591220351257029 195114756777110853815860693)
                ·
                  refine ⟨4573002111963535636309235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 195114756777110853815860693 4573002111963535636309235)
                  ·
                    refine ⟨6859503167945303454463853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573002111963535636309235 6859503167945303454463853)
                    ·
                      refine ⟨2572313687979488795423945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859503167945303454463853 2572313687979488795423945)
                      ·
                        rfl

theorem cell23_5009563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 3].length) (baseStart_5009563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009563 prefixEnd_5009563 := by exact prefixLift 5009563
  have htrace : WordTrace (prefixWord ++ tailWord_5009563) baseStart_5009563 baseEnd_5009563 := by
    simpa [prefixWord, tailWord_5009563, baseEnd_5009563] using wordTrace_append hprefix tailTrace_5009563
  have hstable : (prefixWord ++ tailWord_5009563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009563).length < 2 ^ (prefixWord ++ tailWord_5009563).sum := by decide
  have hdescent : baseEnd_5009563 < baseStart_5009563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009570 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_5009570 : Nat := 118140960795 + 5009570 * 2 ^ 59
def prefixEnd_5009570 : Nat := 4983230072969 + 3 ^ 40 * 5009570 * 2
def baseEnd_5009570 : Nat := 285813031371563363115157

theorem tailTrace_5009570 : CollatzResearch.WordTrace tailWord_5009570 prefixEnd_5009570 285813031371563363115157 := by
  unfold tailWord_5009570
  simp only [CollatzResearch.WordTrace]
  refine ⟨45678507115297732821496541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121809352307460620857324109 45678507115297732821496541)
  ·
    refine ⟨17129440168236649808061203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45678507115297732821496541 17129440168236649808061203)
    ·
      refine ⟨25694160252354974712091805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17129440168236649808061203 25694160252354974712091805)
      ·
        refine ⟨9635310094633115517034427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25694160252354974712091805 9635310094633115517034427)
        ·
          refine ⟨14452965141949673275551641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9635310094633115517034427 14452965141949673275551641)
          ·
            refine ⟨10839723856462254956663731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14452965141949673275551641 10839723856462254956663731)
            ·
              refine ⟨16259585784693382434995597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10839723856462254956663731 16259585784693382434995597)
              ·
                refine ⟨6097344669260018413123349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16259585784693382434995597 6097344669260018413123349)
                ·
                  refine ⟨285813031371563363115157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6097344669260018413123349 285813031371563363115157)
                  ·
                    rfl

theorem cell23_5009570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_5009570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009570 prefixEnd_5009570 := by exact prefixLift 5009570
  have htrace : WordTrace (prefixWord ++ tailWord_5009570) baseStart_5009570 baseEnd_5009570 := by
    simpa [prefixWord, tailWord_5009570, baseEnd_5009570] using wordTrace_append hprefix tailTrace_5009570
  have hstable : (prefixWord ++ tailWord_5009570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009570).length < 2 ^ (prefixWord ++ tailWord_5009570).sum := by decide
  have hdescent : baseEnd_5009570 < baseStart_5009570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_5009597 : Nat := 118140960795 + 5009597 * 2 ^ 59
def prefixEnd_5009597 : Nat := 4983230072969 + 3 ^ 40 * 5009597 * 2
def baseEnd_5009597 : Nat := 2572331146321741662398789

theorem tailTrace_5009597 : CollatzResearch.WordTrace tailWord_5009597 prefixEnd_5009597 2572331146321741662398789 := by
  unfold tailWord_5009597
  simp only [CollatzResearch.WordTrace]
  refine ⟨182715013232093114897219045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121810008821395409931479363 182715013232093114897219045)
  ·
    refine ⟨34259064981017459043228571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182715013232093114897219045 34259064981017459043228571)
    ·
      refine ⟨51388597471526188564842857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34259064981017459043228571 51388597471526188564842857)
      ·
        refine ⟨38541448103644641423632143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51388597471526188564842857 38541448103644641423632143)
        ·
          refine ⟨57812172155466962135448215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38541448103644641423632143 57812172155466962135448215)
          ·
            refine ⟨86718258233200443203172323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57812172155466962135448215 86718258233200443203172323)
            ·
              refine ⟨130077387349800664804758485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86718258233200443203172323 130077387349800664804758485)
              ·
                refine ⟨3048688766010953081361527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 130077387349800664804758485 3048688766010953081361527)
                ·
                  refine ⟨4573033149016429622042291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048688766010953081361527 4573033149016429622042291)
                  ·
                    refine ⟨6859549723524644433063437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573033149016429622042291 6859549723524644433063437)
                    ·
                      refine ⟨2572331146321741662398789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859549723524644433063437 2572331146321741662398789)
                      ·
                        rfl

theorem cell23_5009597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_5009597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009597 prefixEnd_5009597 := by exact prefixLift 5009597
  have htrace : WordTrace (prefixWord ++ tailWord_5009597) baseStart_5009597 baseEnd_5009597 := by
    simpa [prefixWord, tailWord_5009597, baseEnd_5009597] using wordTrace_append hprefix tailTrace_5009597
  have hstable : (prefixWord ++ tailWord_5009597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009597).length < 2 ^ (prefixWord ++ tailWord_5009597).sum := by decide
  have hdescent : baseEnd_5009597 < baseStart_5009597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009603 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 6, 2]
def baseStart_5009603 : Nat := 118140960795 + 5009603 * 2 ^ 59
def prefixEnd_5009603 : Nat := 4983230072969 + 3 ^ 40 * 5009603 * 2
def baseEnd_5009603 : Nat := 2572334227205668638923761

theorem tailTrace_5009603 : CollatzResearch.WordTrace tailWord_5009603 prefixEnd_5009603 2572334227205668638923761 := by
  unfold tailWord_5009603
  simp only [CollatzResearch.WordTrace]
  refine ⟨182715232070071377921937463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121810154713380918614624975 182715232070071377921937463)
  ·
    refine ⟨274072848105107066882906195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182715232070071377921937463 274072848105107066882906195)
    ·
      refine ⟨411109272157660600324359293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274072848105107066882906195 411109272157660600324359293)
      ·
        refine ⟨154165977059122725121634735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411109272157660600324359293 154165977059122725121634735)
        ·
          refine ⟨231248965588684087682452103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154165977059122725121634735 231248965588684087682452103)
          ·
            refine ⟨346873448383026131523678155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231248965588684087682452103 346873448383026131523678155)
            ·
              refine ⟨520310172574539197285517233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346873448383026131523678155 520310172574539197285517233)
              ·
                refine ⟨390232629430904397964137925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520310172574539197285517233 390232629430904397964137925)
                ·
                  refine ⟨73168618018294574618275861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390232629430904397964137925 73168618018294574618275861)
                  ·
                    refine ⟨3429778969607558185231681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73168618018294574618275861 3429778969607558185231681)
                    ·
                      refine ⟨2572334227205668638923761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429778969607558185231681 2572334227205668638923761)
                      ·
                        rfl

theorem cell23_5009603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_5009603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009603 prefixEnd_5009603 := by exact prefixLift 5009603
  have htrace : WordTrace (prefixWord ++ tailWord_5009603) baseStart_5009603 baseEnd_5009603 := by
    simpa [prefixWord, tailWord_5009603, baseEnd_5009603] using wordTrace_append hprefix tailTrace_5009603
  have hstable : (prefixWord ++ tailWord_5009603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009603).length < 2 ^ (prefixWord ++ tailWord_5009603).sum := by decide
  have hdescent : baseEnd_5009603 < baseStart_5009603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009614 : List Nat := [4, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_5009614 : Nat := 118140960795 + 5009614 * 2 ^ 59
def prefixEnd_5009614 : Nat := 4983230072969 + 3 ^ 40 * 5009614 * 2
def baseEnd_5009614 : Nat := 2572339875492868095886211

theorem tailTrace_5009614 : CollatzResearch.WordTrace tailWord_5009614 prefixEnd_5009614 2572339875492868095886211 := by
  unfold tailWord_5009614
  simp only [CollatzResearch.WordTrace]
  refine ⟨22839454159128940850073487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121810422182021017867058597 22839454159128940850073487)
  ·
    refine ⟨34259181238693411275110231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22839454159128940850073487 34259181238693411275110231)
    ·
      refine ⟨51388771858040116912665347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34259181238693411275110231 51388771858040116912665347)
      ·
        refine ⟨77083157787060175368998021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51388771858040116912665347 77083157787060175368998021)
        ·
          refine ⟨14453092085073782881687129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77083157787060175368998021 14453092085073782881687129)
          ·
            refine ⟨10839819063805337161265347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14453092085073782881687129 10839819063805337161265347)
            ·
              refine ⟨16259728595708005741898021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10839819063805337161265347 16259728595708005741898021)
              ·
                refine ⟨3048699111695251076605879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16259728595708005741898021 3048699111695251076605879)
                ·
                  refine ⟨4573048667542876614908819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048699111695251076605879 4573048667542876614908819)
                  ·
                    refine ⟨6859573001314314922363229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573048667542876614908819 6859573001314314922363229)
                    ·
                      refine ⟨2572339875492868095886211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859573001314314922363229 2572339875492868095886211)
                      ·
                        rfl

theorem cell23_5009614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_5009614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009614 prefixEnd_5009614 := by exact prefixLift 5009614
  have htrace : WordTrace (prefixWord ++ tailWord_5009614) baseStart_5009614 baseEnd_5009614 := by
    simpa [prefixWord, tailWord_5009614, baseEnd_5009614] using wordTrace_append hprefix tailTrace_5009614
  have hstable : (prefixWord ++ tailWord_5009614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009614).length < 2 ^ (prefixWord ++ tailWord_5009614).sum := by decide
  have hdescent : baseEnd_5009614 < baseStart_5009614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009637 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5009637 : Nat := 118140960795 + 5009637 * 2 ^ 59
def prefixEnd_5009637 : Nat := 4983230072969 + 3 ^ 40 * 5009637 * 2
def baseEnd_5009637 : Nat := 2572351685547921505898605

theorem tailTrace_5009637 : CollatzResearch.WordTrace tailWord_5009637 prefixEnd_5009637 2572351685547921505898605 := by
  unfold tailWord_5009637
  simp only [CollatzResearch.WordTrace]
  refine ⟨182716472151948201728675165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121810981434632134485783443 182716472151948201728675165)
  ·
    refine ⟨68518677056980575648253187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182716472151948201728675165 68518677056980575648253187)
    ·
      refine ⟨102778015585470863472379781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68518677056980575648253187 102778015585470863472379781)
      ·
        refine ⟨19270877922275786901071209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102778015585470863472379781 19270877922275786901071209)
        ·
          refine ⟨14453158441706840175803407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19270877922275786901071209 14453158441706840175803407)
          ·
            refine ⟨21679737662560260263705111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14453158441706840175803407 21679737662560260263705111)
            ·
              refine ⟨32519606493840390395557667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21679737662560260263705111 32519606493840390395557667)
              ·
                refine ⟨48779409740760585593336501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32519606493840390395557667 48779409740760585593336501)
                ·
                  refine ⟨4573069663196304899375297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48779409740760585593336501 4573069663196304899375297)
                  ·
                    refine ⟨3429802247397228674531473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573069663196304899375297 3429802247397228674531473)
                    ·
                      refine ⟨2572351685547921505898605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429802247397228674531473 2572351685547921505898605)
                      ·
                        rfl

theorem cell23_5009637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5009637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009637 prefixEnd_5009637 := by exact prefixLift 5009637
  have htrace : WordTrace (prefixWord ++ tailWord_5009637) baseStart_5009637 baseEnd_5009637 := by
    simpa [prefixWord, tailWord_5009637, baseEnd_5009637] using wordTrace_append hprefix tailTrace_5009637
  have hstable : (prefixWord ++ tailWord_5009637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009637).length < 2 ^ (prefixWord ++ tailWord_5009637).sum := by decide
  have hdescent : baseEnd_5009637 < baseStart_5009637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009640 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5009640 : Nat := 118140960795 + 5009640 * 2 ^ 59
def prefixEnd_5009640 : Nat := 4983230072969 + 3 ^ 40 * 5009640 * 2
def baseEnd_5009640 : Nat := 2572353225989884994161091

theorem tailTrace_5009640 : CollatzResearch.WordTrace tailWord_5009640 prefixEnd_5009640 2572353225989884994161091 := by
  unfold tailWord_5009640
  simp only [CollatzResearch.WordTrace]
  refine ⟨91358290785468666620517187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121811054380624888827356249 91358290785468666620517187)
  ·
    refine ⟨137037436178202999930775781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91358290785468666620517187 137037436178202999930775781)
    ·
      refine ⟨25694519283413062487020459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137037436178202999930775781 25694519283413062487020459)
      ·
        refine ⟨38541778925119593730530689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25694519283413062487020459 38541778925119593730530689)
        ·
          refine ⟨28906334193839695297898017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38541778925119593730530689 28906334193839695297898017)
          ·
            refine ⟨21679750645379771473423513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28906334193839695297898017 21679750645379771473423513)
            ·
              refine ⟨16259812984034828605067635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21679750645379771473423513 16259812984034828605067635)
              ·
                refine ⟨24389719476052242907601453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16259812984034828605067635 24389719476052242907601453)
                ·
                  refine ⟨9146144803519591090350545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24389719476052242907601453 9146144803519591090350545)
                  ·
                    refine ⟨6859608602639693317762909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9146144803519591090350545 6859608602639693317762909)
                    ·
                      refine ⟨2572353225989884994161091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859608602639693317762909 2572353225989884994161091)
                      ·
                        rfl

theorem cell23_5009640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5009640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009640 prefixEnd_5009640 := by exact prefixLift 5009640
  have htrace : WordTrace (prefixWord ++ tailWord_5009640) baseStart_5009640 baseEnd_5009640 := by
    simpa [prefixWord, tailWord_5009640, baseEnd_5009640] using wordTrace_append hprefix tailTrace_5009640
  have hstable : (prefixWord ++ tailWord_5009640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009640).length < 2 ^ (prefixWord ++ tailWord_5009640).sum := by decide
  have hdescent : baseEnd_5009640 < baseStart_5009640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009643 : List Nat := [1, 1, 1, 1, 2, 5, 5, 7]
def baseStart_5009643 : Nat := 118140960795 + 5009643 * 2 ^ 59
def prefixEnd_5009643 : Nat := 4983230072969 + 3 ^ 40 * 5009643 * 2
def baseEnd_5009643 : Nat := 95272398756735128978651

theorem tailTrace_5009643 : CollatzResearch.WordTrace tailWord_5009643 prefixEnd_5009643 95272398756735128978651 := by
  unfold tailWord_5009643
  simp only [CollatzResearch.WordTrace]
  refine ⟨182716690989926464753393583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121811127326617643168929055 182716690989926464753393583)
  ·
    refine ⟨274075036484889697130090375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182716690989926464753393583 274075036484889697130090375)
    ·
      refine ⟨411112554727334545695135563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274075036484889697130090375 411112554727334545695135563)
      ·
        refine ⟨616668832091001818542703345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411112554727334545695135563 616668832091001818542703345)
        ·
          refine ⟨462501624068251363907027509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616668832091001818542703345 462501624068251363907027509)
          ·
            refine ⟨43359527256398565366283829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 462501624068251363907027509 43359527256398565366283829)
            ·
              refine ⟨4064955680287365503089109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43359527256398565366283829 4064955680287365503089109)
              ·
                refine ⟨95272398756735128978651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4064955680287365503089109 95272398756735128978651)
                ·
                  rfl

theorem cell23_5009643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 7].length) (baseStart_5009643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009643 prefixEnd_5009643 := by exact prefixLift 5009643
  have htrace : WordTrace (prefixWord ++ tailWord_5009643) baseStart_5009643 baseEnd_5009643 := by
    simpa [prefixWord, tailWord_5009643, baseEnd_5009643] using wordTrace_append hprefix tailTrace_5009643
  have hstable : (prefixWord ++ tailWord_5009643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009643).length < 2 ^ (prefixWord ++ tailWord_5009643).sum := by decide
  have hdescent : baseEnd_5009643 < baseStart_5009643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009650 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5009650 : Nat := 118140960795 + 5009650 * 2 ^ 59
def prefixEnd_5009650 : Nat := 4983230072969 + 3 ^ 40 * 5009650 * 2
def baseEnd_5009650 : Nat := 2572358360796429955036045

theorem tailTrace_5009650 : CollatzResearch.WordTrace tailWord_5009650 prefixEnd_5009650 2572358360796429955036045 := by
  unfold tailWord_5009650
  simp only [CollatzResearch.WordTrace]
  refine ⟨45679236575225276237224601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121811297533934069965932269 45679236575225276237224601)
  ·
    refine ⟨34259427431418957177918451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45679236575225276237224601 34259427431418957177918451)
    ·
      refine ⟨51389141147128435766877677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34259427431418957177918451 51389141147128435766877677)
      ·
        refine ⟨19270927930173163412579129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51389141147128435766877677 19270927930173163412579129)
        ·
          refine ⟨14453195947629872559434347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19270927930173163412579129 14453195947629872559434347)
          ·
            refine ⟨21679793921444808839151521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14453195947629872559434347 21679793921444808839151521)
            ·
              refine ⟨16259845441083606629363641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21679793921444808839151521 16259845441083606629363641)
              ·
                refine ⟨12194884080812704972022731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16259845441083606629363641 12194884080812704972022731)
                ·
                  refine ⟨18292326121219057458034097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12194884080812704972022731 18292326121219057458034097)
                  ·
                    refine ⟨13719244590914293093525573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18292326121219057458034097 13719244590914293093525573)
                    ·
                      refine ⟨2572358360796429955036045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13719244590914293093525573 2572358360796429955036045)
                      ·
                        rfl

theorem cell23_5009650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5009650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009650 prefixEnd_5009650 := by exact prefixLift 5009650
  have htrace : WordTrace (prefixWord ++ tailWord_5009650) baseStart_5009650 baseEnd_5009650 := by
    simpa [prefixWord, tailWord_5009650, baseEnd_5009650] using wordTrace_append hprefix tailTrace_5009650
  have hstable : (prefixWord ++ tailWord_5009650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009650).length < 2 ^ (prefixWord ++ tailWord_5009650).sum := by decide
  have hdescent : baseEnd_5009650 < baseStart_5009650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009671 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5009671 : Nat := 118140960795 + 5009671 * 2 ^ 59
def prefixEnd_5009671 : Nat := 4983230072969 + 3 ^ 40 * 5009671 * 2
def baseEnd_5009671 : Nat := 2572369143890174372873449

theorem tailTrace_5009671 : CollatzResearch.WordTrace tailWord_5009671 prefixEnd_5009671 2572369143890174372873449 := by
  unfold tailWord_5009671
  simp only [CollatzResearch.WordTrace]
  refine ⟨182717712233825025535412867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121811808155883350356941911 182717712233825025535412867)
  ·
    refine ⟨274076568350737538303119301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182717712233825025535412867 274076568350737538303119301)
    ·
      refine ⟨51389356565763288431834869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274076568350737538303119301 51389356565763288431834869)
      ·
        refine ⟨4817752178040308290484519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51389356565763288431834869 4817752178040308290484519)
        ·
          refine ⟨7226628267060462435726779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817752178040308290484519 7226628267060462435726779)
          ·
            refine ⟨10839942400590693653590169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226628267060462435726779 10839942400590693653590169)
            ·
              refine ⟨8129956800443020240192627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10839942400590693653590169 8129956800443020240192627)
              ·
                refine ⟨12194935200664530360288941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129956800443020240192627 12194935200664530360288941)
                ·
                  refine ⟨4573100700249198885108353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12194935200664530360288941 4573100700249198885108353)
                  ·
                    refine ⟨3429825525186899163831265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573100700249198885108353 3429825525186899163831265)
                    ·
                      refine ⟨2572369143890174372873449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429825525186899163831265 2572369143890174372873449)
                      ·
                        rfl

theorem cell23_5009671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5009671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009671 prefixEnd_5009671 := by exact prefixLift 5009671
  have htrace : WordTrace (prefixWord ++ tailWord_5009671) baseStart_5009671 baseEnd_5009671 := by
    simpa [prefixWord, tailWord_5009671, baseEnd_5009671] using wordTrace_append hprefix tailTrace_5009671
  have hstable : (prefixWord ++ tailWord_5009671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009671).length < 2 ^ (prefixWord ++ tailWord_5009671).sum := by decide
  have hdescent : baseEnd_5009671 < baseStart_5009671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009687 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5009687 : Nat := 118140960795 + 5009687 * 2 ^ 59
def prefixEnd_5009687 : Nat := 4983230072969 + 3 ^ 40 * 5009687 * 2
def baseEnd_5009687 : Nat := 2572377359580646310273375

theorem tailTrace_5009687 : CollatzResearch.WordTrace tailWord_5009687 prefixEnd_5009687 2572377359580646310273375 := by
  unfold tailWord_5009687
  simp only [CollatzResearch.WordTrace]
  refine ⟨182718295801767060267995315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121812197201178040178663543 182718295801767060267995315)
  ·
    refine ⟨274077443702650590401992973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182718295801767060267995315 274077443702650590401992973)
    ·
      refine ⟨102779041388493971400747365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274077443702650590401992973 102779041388493971400747365)
      ·
        refine ⟨19271070260342619637640131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102779041388493971400747365 19271070260342619637640131)
        ·
          refine ⟨28906605390513929456460197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19271070260342619637640131 28906605390513929456460197)
          ·
            refine ⟨5419988510721361773086287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28906605390513929456460197 5419988510721361773086287)
            ·
              refine ⟨8129982766082042659629431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419988510721361773086287 8129982766082042659629431)
              ·
                refine ⟨12194974149123063989444147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129982766082042659629431 12194974149123063989444147)
                ·
                  refine ⟨18292461223684595984166221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12194974149123063989444147 18292461223684595984166221)
                  ·
                    refine ⟨6859672958881723494062333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18292461223684595984166221 6859672958881723494062333)
                    ·
                      refine ⟨2572377359580646310273375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859672958881723494062333 2572377359580646310273375)
                      ·
                        rfl

theorem cell23_5009687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5009687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009687 prefixEnd_5009687 := by exact prefixLift 5009687
  have htrace : WordTrace (prefixWord ++ tailWord_5009687) baseStart_5009687 baseEnd_5009687 := by
    simpa [prefixWord, tailWord_5009687, baseEnd_5009687] using wordTrace_append hprefix tailTrace_5009687
  have hstable : (prefixWord ++ tailWord_5009687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009687).length < 2 ^ (prefixWord ++ tailWord_5009687).sum := by decide
  have hdescent : baseEnd_5009687 < baseStart_5009687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009694 : List Nat := [4, 3, 2, 1, 1, 3, 2, 7]
def baseStart_5009694 : Nat := 118140960795 + 5009694 * 2 ^ 59
def prefixEnd_5009694 : Nat := 4983230072969 + 3 ^ 40 * 5009694 * 2
def baseEnd_5009694 : Nat := 95273368664638066032809

theorem tailTrace_5009694 : CollatzResearch.WordTrace tailWord_5009694 prefixEnd_5009694 95273368664638066032809 := by
  unfold tailWord_5009694
  simp only [CollatzResearch.WordTrace]
  refine ⟨22839818889092712557937517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121812367408494466975666757 22839818889092712557937517)
  ·
    refine ⟨8564932083409767209226569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22839818889092712557937517 8564932083409767209226569)
    ·
      refine ⟨6423699062557325406919927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8564932083409767209226569 6423699062557325406919927)
      ·
        refine ⟨9635548593835988110379891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6423699062557325406919927 9635548593835988110379891)
        ·
          refine ⟨14453322890753982165569837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9635548593835988110379891 14453322890753982165569837)
          ·
            refine ⟨5419996084032743312088689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14453322890753982165569837 5419996084032743312088689)
            ·
              refine ⟨4064997063024557484066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419996084032743312088689 4064997063024557484066517)
              ·
                refine ⟨95273368664638066032809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4064997063024557484066517 95273368664638066032809)
                ·
                  rfl

theorem cell23_5009694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_5009694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009694 prefixEnd_5009694 := by exact prefixLift 5009694
  have htrace : WordTrace (prefixWord ++ tailWord_5009694) baseStart_5009694 baseEnd_5009694 := by
    simpa [prefixWord, tailWord_5009694, baseEnd_5009694] using wordTrace_append hprefix tailTrace_5009694
  have hstable : (prefixWord ++ tailWord_5009694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009694).length < 2 ^ (prefixWord ++ tailWord_5009694).sum := by decide
  have hdescent : baseEnd_5009694 < baseStart_5009694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009697 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 1, 3, 2]
def baseStart_5009697 : Nat := 118140960795 + 5009697 * 2 ^ 59
def prefixEnd_5009697 : Nat := 4983230072969 + 3 ^ 40 * 5009697 * 2
def baseEnd_5009697 : Nat := 2572382494387191271148329

theorem tailTrace_5009697 : CollatzResearch.WordTrace tailWord_5009697 prefixEnd_5009697 2572382494387191271148329 := by
  unfold tailWord_5009697
  simp only [CollatzResearch.WordTrace]
  refine ⟨182718660531730831975859345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121812440354487221317239563 182718660531730831975859345)
  ·
    refine ⟨137038995398798123981894509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182718660531730831975859345 137038995398798123981894509)
    ·
      refine ⟨51389623274549296493210441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137038995398798123981894509 51389623274549296493210441)
      ·
        refine ⟨38542217455911972369907831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51389623274549296493210441 38542217455911972369907831)
        ·
          refine ⟨57813326183867958554861747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38542217455911972369907831 57813326183867958554861747)
          ·
            refine ⟨86719989275801937832292621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57813326183867958554861747 86719989275801937832292621)
            ·
              refine ⟨32519995978425726687109733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86719989275801937832292621 32519995978425726687109733)
              ·
                refine ⟨6097499245954823753833075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32519995978425726687109733 6097499245954823753833075)
                ·
                  refine ⟨9146248868932235630749613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097499245954823753833075 9146248868932235630749613)
                  ·
                    refine ⟨3429843325849588361531105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9146248868932235630749613 3429843325849588361531105)
                    ·
                      refine ⟨2572382494387191271148329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429843325849588361531105 2572382494387191271148329)
                      ·
                        rfl

theorem cell23_5009697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_5009697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009697 prefixEnd_5009697 := by exact prefixLift 5009697
  have htrace : WordTrace (prefixWord ++ tailWord_5009697) baseStart_5009697 baseEnd_5009697 := by
    simpa [prefixWord, tailWord_5009697, baseEnd_5009697] using wordTrace_append hprefix tailTrace_5009697
  have hstable : (prefixWord ++ tailWord_5009697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009697).length < 2 ^ (prefixWord ++ tailWord_5009697).sum := by decide
  have hdescent : baseEnd_5009697 < baseStart_5009697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009727 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 4, 2, 2]
def baseStart_5009727 : Nat := 118140960795 + 5009727 * 2 ^ 59
def prefixEnd_5009727 : Nat := 4983230072969 + 3 ^ 40 * 5009727 * 2
def baseEnd_5009727 : Nat := 2572397898806826153773191

theorem tailTrace_5009727 : CollatzResearch.WordTrace tailWord_5009727 prefixEnd_5009727 2572397898806826153773191 := by
  unfold tailWord_5009727
  simp only [CollatzResearch.WordTrace]
  refine ⟨182719754721622147099451435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121813169814414764732967623 182719754721622147099451435)
  ·
    refine ⟨274079632082433220649177153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182719754721622147099451435 274079632082433220649177153)
    ·
      refine ⟨205559724061824915486882865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274079632082433220649177153 205559724061824915486882865)
      ·
        refine ⟨154169793046368686615162149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205559724061824915486882865 154169793046368686615162149)
        ·
          refine ⟨28906836196194128740342903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154169793046368686615162149 28906836196194128740342903)
          ·
            refine ⟨43360254294291193110514355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28906836196194128740342903 43360254294291193110514355)
            ·
              refine ⟨65040381441436789665771533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43360254294291193110514355 65040381441436789665771533)
              ·
                refine ⟨24390143040538796124664325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65040381441436789665771533 24390143040538796124664325)
                ·
                  refine ⟨4573151820101024273374561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24390143040538796124664325 4573151820101024273374561)
                  ·
                    refine ⟨3429863865075768205030921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573151820101024273374561 3429863865075768205030921)
                    ·
                      refine ⟨2572397898806826153773191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429863865075768205030921 2572397898806826153773191)
                      ·
                        rfl

theorem cell23_5009727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_5009727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009727 prefixEnd_5009727 := by exact prefixLift 5009727
  have htrace : WordTrace (prefixWord ++ tailWord_5009727) baseStart_5009727 baseEnd_5009727 := by
    simpa [prefixWord, tailWord_5009727, baseEnd_5009727] using wordTrace_append hprefix tailTrace_5009727
  have hstable : (prefixWord ++ tailWord_5009727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009727).length < 2 ^ (prefixWord ++ tailWord_5009727).sum := by decide
  have hdescent : baseEnd_5009727 < baseStart_5009727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009744 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2]
def baseStart_5009744 : Nat := 118140960795 + 5009744 * 2 ^ 59
def prefixEnd_5009744 : Nat := 4983230072969 + 3 ^ 40 * 5009744 * 2
def baseEnd_5009744 : Nat := 2572406627977952587260613

theorem tailTrace_5009744 : CollatzResearch.WordTrace tailWord_5009744 prefixEnd_5009744 2572406627977952587260613 := by
  unfold tailWord_5009744
  simp only [CollatzResearch.WordTrace]
  refine ⟨91360187381280279501410143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121813583175040372668546857 91360187381280279501410143)
  ·
    refine ⟨137040281071920419252115215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91360187381280279501410143 137040281071920419252115215)
    ·
      refine ⟨205560421607880628878172823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137040281071920419252115215 205560421607880628878172823)
      ·
        refine ⟨308340632411820943317259235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205560421607880628878172823 308340632411820943317259235)
        ·
          refine ⟨462510948617731414975888853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308340632411820943317259235 462510948617731414975888853)
          ·
            refine ⟨10840100358228080038497395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 462510948617731414975888853 10840100358228080038497395)
            ·
              refine ⟨16260150537342120057746093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10840100358228080038497395 16260150537342120057746093)
              ·
                refine ⟨6097556451503295021654785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16260150537342120057746093 6097556451503295021654785)
                ·
                  refine ⟨4573167338627471266241089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6097556451503295021654785 4573167338627471266241089)
                  ·
                    refine ⟨3429875503970603449680817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573167338627471266241089 3429875503970603449680817)
                    ·
                      refine ⟨2572406627977952587260613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3429875503970603449680817 2572406627977952587260613)
                      ·
                        rfl

theorem cell23_5009744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 2, 2].length) (baseStart_5009744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009744 prefixEnd_5009744 := by exact prefixLift 5009744
  have htrace : WordTrace (prefixWord ++ tailWord_5009744) baseStart_5009744 baseEnd_5009744 := by
    simpa [prefixWord, tailWord_5009744, baseEnd_5009744] using wordTrace_append hprefix tailTrace_5009744
  have hstable : (prefixWord ++ tailWord_5009744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009744).length < 2 ^ (prefixWord ++ tailWord_5009744).sum := by decide
  have hdescent : baseEnd_5009744 < baseStart_5009744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009800 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_5009800 : Nat := 118140960795 + 5009800 * 2 ^ 59
def prefixEnd_5009800 : Nat := 4983230072969 + 3 ^ 40 * 5009800 * 2
def baseEnd_5009800 : Nat := 2572435382894604368160355

theorem tailTrace_5009800 : CollatzResearch.WordTrace tailWord_5009800 prefixEnd_5009800 2572435382894604368160355 := by
  unfold tailWord_5009800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91361208625178840283429427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121814944833571787044572569 91361208625178840283429427)
  ·
    refine ⟨137041812937768260425144141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91361208625178840283429427 137041812937768260425144141)
    ·
      refine ⟨51390679851663097659429053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137041812937768260425144141 51390679851663097659429053)
      ·
        refine ⟨19271504944373661622285895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51390679851663097659429053 19271504944373661622285895)
        ·
          refine ⟨28907257416560492433428843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19271504944373661622285895 28907257416560492433428843)
          ·
            refine ⟨43360886124840738650143265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28907257416560492433428843 43360886124840738650143265)
            ·
              refine ⟨32520664593630553987607449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43360886124840738650143265 32520664593630553987607449)
              ·
                refine ⟨24390498445222915490705587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32520664593630553987607449 24390498445222915490705587)
                ·
                  refine ⟨36585747667834373236058381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24390498445222915490705587 36585747667834373236058381)
                  ·
                    refine ⟨13719655375437889963521893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36585747667834373236058381 13719655375437889963521893)
                    ·
                      refine ⟨2572435382894604368160355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13719655375437889963521893 2572435382894604368160355)
                      ·
                        rfl

theorem cell23_5009800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_5009800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009800 prefixEnd_5009800 := by exact prefixLift 5009800
  have htrace : WordTrace (prefixWord ++ tailWord_5009800) baseStart_5009800 baseEnd_5009800 := by
    simpa [prefixWord, tailWord_5009800, baseEnd_5009800] using wordTrace_append hprefix tailTrace_5009800
  have hstable : (prefixWord ++ tailWord_5009800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009800).length < 2 ^ (prefixWord ++ tailWord_5009800).sum := by decide
  have hdescent : baseEnd_5009800 < baseStart_5009800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009887 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 1, 5]
def baseStart_5009887 : Nat := 118140960795 + 5009887 * 2 ^ 59
def prefixEnd_5009887 : Nat := 4983230072969 + 3 ^ 40 * 5009887 * 2
def baseEnd_5009887 : Nat := 857493351903848509257485

theorem tailTrace_5009887 : CollatzResearch.WordTrace tailWord_5009887 prefixEnd_5009887 857493351903848509257485 := by
  unfold tailWord_5009887
  simp only [CollatzResearch.WordTrace]
  refine ⟨182725590401042494425275915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121817060267361662950183943 182725590401042494425275915)
  ·
    refine ⟨274088385601563741637913873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182725590401042494425275915 274088385601563741637913873)
    ·
      refine ⟨205566289201172806228435405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274088385601563741637913873 205566289201172806228435405)
      ·
        refine ⟨77087358450439802335663277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205566289201172806228435405 77087358450439802335663277)
        ·
          refine ⟨28907759418914925875873729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77087358450439802335663277 28907759418914925875873729)
          ·
            refine ⟨21680819564186194406905297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28907759418914925875873729 21680819564186194406905297)
            ·
              refine ⟨16260614673139645805178973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21680819564186194406905297 16260614673139645805178973)
              ·
                refine ⟨6097730502427367176942115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16260614673139645805178973 6097730502427367176942115)
                ·
                  refine ⟨9146595753641050765413173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097730502427367176942115 9146595753641050765413173)
                  ·
                    refine ⟨857493351903848509257485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9146595753641050765413173 857493351903848509257485)
                    ·
                      rfl

theorem cell23_5009887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_5009887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009887 prefixEnd_5009887 := by exact prefixLift 5009887
  have htrace : WordTrace (prefixWord ++ tailWord_5009887) baseStart_5009887 baseEnd_5009887 := by
    simpa [prefixWord, tailWord_5009887, baseEnd_5009887] using wordTrace_append hprefix tailTrace_5009887
  have hstable : (prefixWord ++ tailWord_5009887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009887).length < 2 ^ (prefixWord ++ tailWord_5009887).sum := by decide
  have hdescent : baseEnd_5009887 < baseStart_5009887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009901 : List Nat := [1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5009901 : Nat := 118140960795 + 5009901 * 2 ^ 59
def prefixEnd_5009901 : Nat := 4983230072969 + 3 ^ 40 * 5009901 * 2
def baseEnd_5009901 : Nat := 2572487244440708472997391

theorem tailTrace_5009901 : CollatzResearch.WordTrace tailWord_5009901 prefixEnd_5009901 2572487244440708472997391 := by
  unfold tailWord_5009901
  simp only [CollatzResearch.WordTrace]
  refine ⟨182726101022991774816285557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121817400681994516544190371 182726101022991774816285557)
  ·
    refine ⟨17130571970905478889026771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182726101022991774816285557 17130571970905478889026771)
    ·
      refine ⟨25695857956358218333540157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17130571970905478889026771 25695857956358218333540157)
      ·
        refine ⟨9635946733634331875077559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25695857956358218333540157 9635946733634331875077559)
        ·
          refine ⟨14453920100451497812616339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9635946733634331875077559 14453920100451497812616339)
          ·
            refine ⟨21680880150677246718924509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14453920100451497812616339 21680880150677246718924509)
            ·
              refine ⟨8130330056503967519596691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21680880150677246718924509 8130330056503967519596691)
              ·
                refine ⟨12195495084755951279395037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130330056503967519596691 12195495084755951279395037)
                ·
                  refine ⟨4573310656783481729773139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12195495084755951279395037 4573310656783481729773139)
                  ·
                    refine ⟨6859965985175222594659709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573310656783481729773139 6859965985175222594659709)
                    ·
                      refine ⟨2572487244440708472997391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6859965985175222594659709 2572487244440708472997391)
                      ·
                        rfl

theorem cell23_5009901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5009901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009901 prefixEnd_5009901 := by exact prefixLift 5009901
  have htrace : WordTrace (prefixWord ++ tailWord_5009901) baseStart_5009901 baseEnd_5009901 := by
    simpa [prefixWord, tailWord_5009901, baseEnd_5009901] using wordTrace_append hprefix tailTrace_5009901
  have hstable : (prefixWord ++ tailWord_5009901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009901).length < 2 ^ (prefixWord ++ tailWord_5009901).sum := by decide
  have hdescent : baseEnd_5009901 < baseStart_5009901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009920 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_5009920 : Nat := 118140960795 + 5009920 * 2 ^ 59
def prefixEnd_5009920 : Nat := 4983230072969 + 3 ^ 40 * 5009920 * 2
def baseEnd_5009920 : Nat := 2572497000573143898659803

theorem tailTrace_5009920 : CollatzResearch.WordTrace tailWord_5009920 prefixEnd_5009920 2572497000573143898659803 := by
  unfold tailWord_5009920
  simp only [CollatzResearch.WordTrace]
  refine ⟨91363397004961470530613607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121817862673281960707484809 91363397004961470530613607)
  ·
    refine ⟨137045095507442205795920411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91363397004961470530613607 137045095507442205795920411)
    ·
      refine ⟨205567643261163308693880617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137045095507442205795920411 205567643261163308693880617)
      ·
        refine ⟨154175732445872481520410463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205567643261163308693880617 154175732445872481520410463)
        ·
          refine ⟨231263598668808722280615695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154175732445872481520410463 231263598668808722280615695)
          ·
            refine ⟨346895398003213083420923543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231263598668808722280615695 346895398003213083420923543)
            ·
              refine ⟨520343097004819625131385315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346895398003213083420923543 520343097004819625131385315)
              ·
                refine ⟨780514645507229437697077973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520343097004819625131385315 780514645507229437697077973)
                ·
                  refine ⟨18293312004075689946025265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 780514645507229437697077973 18293312004075689946025265)
                  ·
                    refine ⟨13719984003056767459518949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18293312004075689946025265 13719984003056767459518949)
                    ·
                      refine ⟨2572497000573143898659803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13719984003056767459518949 2572497000573143898659803)
                      ·
                        rfl

theorem cell23_5009920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_5009920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009920 prefixEnd_5009920 := by exact prefixLift 5009920
  have htrace : WordTrace (prefixWord ++ tailWord_5009920) baseStart_5009920 baseEnd_5009920 := by
    simpa [prefixWord, tailWord_5009920, baseEnd_5009920] using wordTrace_append hprefix tailTrace_5009920
  have hstable : (prefixWord ++ tailWord_5009920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009920).length < 2 ^ (prefixWord ++ tailWord_5009920).sum := by decide
  have hdescent : baseEnd_5009920 < baseStart_5009920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009924 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5009924 : Nat := 118140960795 + 5009924 * 2 ^ 59
def prefixEnd_5009924 : Nat := 4983230072969 + 3 ^ 40 * 5009924 * 2
def baseEnd_5009924 : Nat := 2572499054495761883009785

theorem tailTrace_5009924 : CollatzResearch.WordTrace tailWord_5009924 prefixEnd_5009924 2572499054495761883009785 := by
  unfold tailWord_5009924
  simp only [CollatzResearch.WordTrace]
  refine ⟨91363469950954224872186413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121817959934605633162915217 91363469950954224872186413)
  ·
    refine ⟨34261301231607834327069905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91363469950954224872186413 34261301231607834327069905)
    ·
      refine ⟨25695975923705875745302429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34261301231607834327069905 25695975923705875745302429)
      ·
        refine ⟨9635990971389703404488411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25695975923705875745302429 9635990971389703404488411)
        ·
          refine ⟨14453986457084555106732617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9635990971389703404488411 14453986457084555106732617)
          ·
            refine ⟨10840489842813416330049463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14453986457084555106732617 10840489842813416330049463)
            ·
              refine ⟨16260734764220124495074195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10840489842813416330049463 16260734764220124495074195)
              ·
                refine ⟨24391102146330186742611293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16260734764220124495074195 24391102146330186742611293)
                ·
                  refine ⟨9146663304873820028479235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24391102146330186742611293 9146663304873820028479235)
                  ·
                    refine ⟨13719994957310730042718853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9146663304873820028479235 13719994957310730042718853)
                    ·
                      refine ⟨2572499054495761883009785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13719994957310730042718853 2572499054495761883009785)
                      ·
                        rfl

theorem cell23_5009924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5009924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009924 prefixEnd_5009924 := by exact prefixLift 5009924
  have htrace : WordTrace (prefixWord ++ tailWord_5009924) baseStart_5009924 baseEnd_5009924 := by
    simpa [prefixWord, tailWord_5009924, baseEnd_5009924] using wordTrace_append hprefix tailTrace_5009924
  have hstable : (prefixWord ++ tailWord_5009924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009924).length < 2 ^ (prefixWord ++ tailWord_5009924).sum := by decide
  have hdescent : baseEnd_5009924 < baseStart_5009924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009930 : List Nat := [3, 1, 2, 2, 2, 1, 1, 11]
def baseStart_5009930 : Nat := 118140960795 + 5009930 * 2 ^ 59
def prefixEnd_5009930 : Nat := 4983230072969 + 3 ^ 40 * 5009930 * 2
def baseEnd_5009930 : Nat := 95277856865914402204991

theorem tailTrace_5009930 : CollatzResearch.WordTrace tailWord_5009930 prefixEnd_5009930 95277856865914402204991 := by
  unfold tailWord_5009930
  simp only [CollatzResearch.WordTrace]
  refine ⟨45681789684971678192272811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121818105826591141846060829 45681789684971678192272811)
  ·
    refine ⟨68522684527457517288409217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45681789684971678192272811 68522684527457517288409217)
    ·
      refine ⟨51392013395593137966306913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68522684527457517288409217 51392013395593137966306913)
      ·
        refine ⟨38544010046694853474730185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51392013395593137966306913 38544010046694853474730185)
        ·
          refine ⟨28908007535021140106047639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38544010046694853474730185 28908007535021140106047639)
          ·
            refine ⟨43362011302531710159071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28908007535021140106047639 43362011302531710159071459)
            ·
              refine ⟨65043016953797565238607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43362011302531710159071459 65043016953797565238607189)
              ·
                refine ⟨95277856865914402204991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65043016953797565238607189 95277856865914402204991)
                ·
                  rfl

theorem cell23_5009930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_5009930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009930 prefixEnd_5009930 := by exact prefixLift 5009930
  have htrace : WordTrace (prefixWord ++ tailWord_5009930) baseStart_5009930 baseEnd_5009930 := by
    simpa [prefixWord, tailWord_5009930, baseEnd_5009930] using wordTrace_append hprefix tailTrace_5009930
  have hstable : (prefixWord ++ tailWord_5009930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009930).length < 2 ^ (prefixWord ++ tailWord_5009930).sum := by decide
  have hdescent : baseEnd_5009930 < baseStart_5009930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009944 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5009944 : Nat := 118140960795 + 5009944 * 2 ^ 59
def prefixEnd_5009944 : Nat := 4983230072969 + 3 ^ 40 * 5009944 * 2
def baseEnd_5009944 : Nat := 2572509324108851804759693

theorem tailTrace_5009944 : CollatzResearch.WordTrace tailWord_5009944 prefixEnd_5009944 2572509324108851804759693 := by
  unfold tailWord_5009944
  simp only [CollatzResearch.WordTrace]
  refine ⟨91363834680917996580050443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121818446241223995440067257 91363834680917996580050443)
  ·
    refine ⟨137045752021376994870075665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91363834680917996580050443 137045752021376994870075665)
    ·
      refine ⟨102784314016032746152556749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137045752021376994870075665 102784314016032746152556749)
      ·
        refine ⟨38544117756012279807208781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102784314016032746152556749 38544117756012279807208781)
        ·
          refine ⟨14454044158504604927703293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38544117756012279807208781 14454044158504604927703293)
          ·
            refine ⟨5420266559439226847888735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14454044158504604927703293 5420266559439226847888735)
            ·
              refine ⟨8130399839158840271833103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420266559439226847888735 8130399839158840271833103)
              ·
                refine ⟨12195599758738260407749655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130399839158840271833103 12195599758738260407749655)
                ·
                  refine ⟨18293399638107390611624483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12195599758738260407749655 18293399638107390611624483)
                  ·
                    refine ⟨27440099457161085917436725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18293399638107390611624483 27440099457161085917436725)
                    ·
                      refine ⟨2572509324108851804759693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27440099457161085917436725 2572509324108851804759693)
                      ·
                        rfl

theorem cell23_5009944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5009944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009944 prefixEnd_5009944 := by exact prefixLift 5009944
  have htrace : WordTrace (prefixWord ++ tailWord_5009944) baseStart_5009944 baseEnd_5009944 := by
    simpa [prefixWord, tailWord_5009944, baseEnd_5009944] using wordTrace_append hprefix tailTrace_5009944
  have hstable : (prefixWord ++ tailWord_5009944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009944).length < 2 ^ (prefixWord ++ tailWord_5009944).sum := by decide
  have hdescent : baseEnd_5009944 < baseStart_5009944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009952 : List Nat := [2, 1, 1, 6, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5009952 : Nat := 118140960795 + 5009952 * 2 ^ 59
def prefixEnd_5009952 : Nat := 4983230072969 + 3 ^ 40 * 5009952 * 2
def baseEnd_5009952 : Nat := 2572513431954087773459657

theorem tailTrace_5009952 : CollatzResearch.WordTrace tailWord_5009952 prefixEnd_5009952 2572513431954087773459657 := by
  unfold tailWord_5009952
  simp only [CollatzResearch.WordTrace]
  refine ⟨91363980572903505263196055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121818640763871340350928073 91363980572903505263196055)
  ·
    refine ⟨137045970859355257894794083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91363980572903505263196055 137045970859355257894794083)
    ·
      refine ⟨205568956289032886842191125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137045970859355257894794083 205568956289032886842191125)
      ·
        refine ⟨9636044826048416570727709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 205568956289032886842191125 9636044826048416570727709)
        ·
          refine ⟨3613516809768156214022891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9636044826048416570727709 3613516809768156214022891)
          ·
            refine ⟨5420275214652234321034337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613516809768156214022891 5420275214652234321034337)
            ·
              refine ⟨4065206410989175740775753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5420275214652234321034337 4065206410989175740775753)
              ·
                refine ⟨3048904808241881805581815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065206410989175740775753 3048904808241881805581815)
                ·
                  refine ⟨4573357212362822708372723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048904808241881805581815 4573357212362822708372723)
                  ·
                    refine ⟨6860035818544234062559085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573357212362822708372723 6860035818544234062559085)
                    ·
                      refine ⟨2572513431954087773459657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860035818544234062559085 2572513431954087773459657)
                      ·
                        rfl

theorem cell23_5009952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5009952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009952 prefixEnd_5009952 := by exact prefixLift 5009952
  have htrace : WordTrace (prefixWord ++ tailWord_5009952) baseStart_5009952 baseEnd_5009952 := by
    simpa [prefixWord, tailWord_5009952, baseEnd_5009952] using wordTrace_append hprefix tailTrace_5009952
  have hstable : (prefixWord ++ tailWord_5009952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009952).length < 2 ^ (prefixWord ++ tailWord_5009952).sum := by decide
  have hdescent : baseEnd_5009952 < baseStart_5009952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5009984 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2]
def baseStart_5009984 : Nat := 118140960795 + 5009984 * 2 ^ 59
def prefixEnd_5009984 : Nat := 4983230072969 + 3 ^ 40 * 5009984 * 2
def baseEnd_5009984 : Nat := 2572529863335031648259509

theorem tailTrace_5009984 : CollatzResearch.WordTrace tailWord_5009984 prefixEnd_5009984 2572529863335031648259509 := by
  unfold tailWord_5009984
  simp only [CollatzResearch.WordTrace]
  refine ⟨91364564140845539995778503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121819418854460719994371337 91364564140845539995778503)
  ·
    refine ⟨137046846211268309993667755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91364564140845539995778503 137046846211268309993667755)
    ·
      refine ⟨205570269316902464990501633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137046846211268309993667755 205570269316902464990501633)
      ·
        refine ⟨154177701987676848742876225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205570269316902464990501633 154177701987676848742876225)
        ·
          refine ⟨115633276490757636557157169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154177701987676848742876225 115633276490757636557157169)
          ·
            refine ⟨86724957368068227417867877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115633276490757636557157169 86724957368068227417867877)
            ·
              refine ⟨16260929506512792640850227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86724957368068227417867877 16260929506512792640850227)
              ·
                refine ⟨24391394259769188961275341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16260929506512792640850227 24391394259769188961275341)
                ·
                  refine ⟨9146772847413445860478253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24391394259769188961275341 9146772847413445860478253)
                  ·
                    refine ⟨3430039817780042197679345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9146772847413445860478253 3430039817780042197679345)
                    ·
                      refine ⟨2572529863335031648259509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430039817780042197679345 2572529863335031648259509)
                      ·
                        rfl

theorem cell23_5009984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_5009984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5009984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5009984 prefixEnd_5009984 := by exact prefixLift 5009984
  have htrace : WordTrace (prefixWord ++ tailWord_5009984) baseStart_5009984 baseEnd_5009984 := by
    simpa [prefixWord, tailWord_5009984, baseEnd_5009984] using wordTrace_append hprefix tailTrace_5009984
  have hstable : (prefixWord ++ tailWord_5009984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5009984).length < 2 ^ (prefixWord ++ tailWord_5009984).sum := by decide
  have hdescent : baseEnd_5009984 < baseStart_5009984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5009984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010001 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 1, 3, 2]
def baseStart_5010001 : Nat := 118140960795 + 5010001 * 2 ^ 59
def prefixEnd_5010001 : Nat := 4983230072969 + 3 ^ 40 * 5010001 * 2
def baseEnd_5010001 : Nat := 2572538592506158081746931

theorem tailTrace_5010001 : CollatzResearch.WordTrace tailWord_5010001 prefixEnd_5010001 2572538592506158081746931 := by
  unfold tailWord_5010001
  simp only [CollatzResearch.WordTrace]
  refine ⟨182729748322629491894925857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121819832215086327929950571 182729748322629491894925857)
  ·
    refine ⟨137047311241972118921194393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182729748322629491894925857 137047311241972118921194393)
    ·
      refine ⟨102785483431479089190895795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137047311241972118921194393 102785483431479089190895795)
      ·
        refine ⟨154178225147218633786343693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102785483431479089190895795 154178225147218633786343693)
        ·
          refine ⟨57816834430206987669878885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154178225147218633786343693 57816834430206987669878885)
          ·
            refine ⟨10840656455663810188102291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57816834430206987669878885 10840656455663810188102291)
            ·
              refine ⟨16260984683495715282153437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10840656455663810188102291 16260984683495715282153437)
              ·
                refine ⟨6097869256310893230807539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16260984683495715282153437 6097869256310893230807539)
                ·
                  refine ⟨9146803884466339846211309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097869256310893230807539 9146803884466339846211309)
                  ·
                    refine ⟨3430051456674877442329241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9146803884466339846211309 3430051456674877442329241)
                    ·
                      refine ⟨2572538592506158081746931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430051456674877442329241 2572538592506158081746931)
                      ·
                        rfl

theorem cell23_5010001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_5010001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010001 prefixEnd_5010001 := by exact prefixLift 5010001
  have htrace : WordTrace (prefixWord ++ tailWord_5010001) baseStart_5010001 baseEnd_5010001 := by
    simpa [prefixWord, tailWord_5010001, baseEnd_5010001] using wordTrace_append hprefix tailTrace_5010001
  have hstable : (prefixWord ++ tailWord_5010001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010001).length < 2 ^ (prefixWord ++ tailWord_5010001).sum := by decide
  have hdescent : baseEnd_5010001 < baseStart_5010001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010031 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 2, 2, 2]
def baseStart_5010031 : Nat := 118140960795 + 5010031 * 2 ^ 59
def prefixEnd_5010031 : Nat := 4983230072969 + 3 ^ 40 * 5010031 * 2
def baseEnd_5010031 : Nat := 2572553996925792964371793

theorem tailTrace_5010031 : CollatzResearch.WordTrace tailWord_5010031 prefixEnd_5010031 2572553996925792964371793 := by
  unfold tailWord_5010031
  simp only [CollatzResearch.WordTrace]
  refine ⟨182730842512520807018517947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121820561675013871345678631 182730842512520807018517947)
  ·
    refine ⟨274096263768781210527776921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182730842512520807018517947 274096263768781210527776921)
    ·
      refine ⟨205572197826585907895832691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274096263768781210527776921 205572197826585907895832691)
      ·
        refine ⟨308358296739878861843749037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205572197826585907895832691 308358296739878861843749037)
        ·
          refine ⟨115634361277454573191405889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308358296739878861843749037 115634361277454573191405889)
          ·
            refine ⟨86725770958090929893554417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115634361277454573191405889 86725770958090929893554417)
            ·
              refine ⟨65044328218568197420165813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86725770958090929893554417 65044328218568197420165813)
              ·
                refine ⟨6097905770490768508140545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65044328218568197420165813 6097905770490768508140545)
                ·
                  refine ⟨4573429327868076381105409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6097905770490768508140545 4573429327868076381105409)
                  ·
                    refine ⟨3430071995901057285829057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4573429327868076381105409 3430071995901057285829057)
                    ·
                      refine ⟨2572553996925792964371793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430071995901057285829057 2572553996925792964371793)
                      ·
                        rfl

theorem cell23_5010031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2, 2].length) (baseStart_5010031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010031 prefixEnd_5010031 := by exact prefixLift 5010031
  have htrace : WordTrace (prefixWord ++ tailWord_5010031) baseStart_5010031 baseEnd_5010031 := by
    simpa [prefixWord, tailWord_5010031, baseEnd_5010031] using wordTrace_append hprefix tailTrace_5010031
  have hstable : (prefixWord ++ tailWord_5010031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010031).length < 2 ^ (prefixWord ++ tailWord_5010031).sum := by decide
  have hdescent : baseEnd_5010031 < baseStart_5010031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_5010047 : Nat := 118140960795 + 5010047 * 2 ^ 59
def prefixEnd_5010047 : Nat := 4983230072969 + 3 ^ 40 * 5010047 * 2
def baseEnd_5010047 : Nat := 2572562212616264901771719

theorem tailTrace_5010047 : CollatzResearch.WordTrace tailWord_5010047 prefixEnd_5010047 2572562212616264901771719 := by
  unfold tailWord_5010047
  simp only [CollatzResearch.WordTrace]
  refine ⟨182731426080462841751100395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121820950720308561167400263 182731426080462841751100395)
  ·
    refine ⟨274097139120694262626650593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182731426080462841751100395 274097139120694262626650593)
    ·
      refine ⟨205572854340520696969987945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274097139120694262626650593 205572854340520696969987945)
      ·
        refine ⟨154179640755390522727490959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205572854340520696969987945 154179640755390522727490959)
        ·
          refine ⟨231269461133085784091236439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154179640755390522727490959 231269461133085784091236439)
          ·
            refine ⟨346904191699628676136854659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231269461133085784091236439 346904191699628676136854659)
            ·
              refine ⟨520356287549443014205281989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346904191699628676136854659 520356287549443014205281989)
              ·
                refine ⟨97566803915520565163490373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 520356287549443014205281989 97566803915520565163490373)
                ·
                  refine ⟨18293775734160105968154445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97566803915520565163490373 18293775734160105968154445)
                  ·
                    refine ⟨6860165900310039738057917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18293775734160105968154445 6860165900310039738057917)
                    ·
                      refine ⟨2572562212616264901771719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860165900310039738057917 2572562212616264901771719)
                      ·
                        rfl

theorem cell23_5010047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_5010047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010047 prefixEnd_5010047 := by exact prefixLift 5010047
  have htrace : WordTrace (prefixWord ++ tailWord_5010047) baseStart_5010047 baseEnd_5010047 := by
    simpa [prefixWord, tailWord_5010047, baseEnd_5010047] using wordTrace_append hprefix tailTrace_5010047
  have hstable : (prefixWord ++ tailWord_5010047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010047).length < 2 ^ (prefixWord ++ tailWord_5010047).sum := by decide
  have hdescent : baseEnd_5010047 < baseStart_5010047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010067 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 2, 5]
def baseStart_5010067 : Nat := 118140960795 + 5010067 * 2 ^ 59
def prefixEnd_5010067 : Nat := 4983230072969 + 3 ^ 40 * 5010067 * 2
def baseEnd_5010067 : Nat := 857524160743118274507209

theorem tailTrace_5010067 : CollatzResearch.WordTrace tailWord_5010067 prefixEnd_5010067 857524160743118274507209 := by
  unfold tailWord_5010067
  simp only [CollatzResearch.WordTrace]
  refine ⟨182732155540390385166828455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121821437026926923444552303 182732155540390385166828455)
  ·
    refine ⟨274098233310585577750242683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182732155540390385166828455 274098233310585577750242683)
    ·
      refine ⟨411147349965878366625364025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274098233310585577750242683 411147349965878366625364025)
      ·
        refine ⟨308360512474408774969023019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411147349965878366625364025 308360512474408774969023019)
        ·
          refine ⟨462540768711613162453534529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308360512474408774969023019 462540768711613162453534529)
          ·
            refine ⟨346905576533709871840150897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462540768711613162453534529 346905576533709871840150897)
            ·
              refine ⟨260179182400282403880113173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346905576533709871840150897 260179182400282403880113173)
              ·
                refine ⟨12195899175013237681880305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260179182400282403880113173 12195899175013237681880305)
                ·
                  refine ⟨9146924381259928261410229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12195899175013237681880305 9146924381259928261410229)
                  ·
                    refine ⟨857524160743118274507209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9146924381259928261410229 857524160743118274507209)
                    ·
                      rfl

theorem cell23_5010067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 5].length) (baseStart_5010067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010067 prefixEnd_5010067 := by exact prefixLift 5010067
  have htrace : WordTrace (prefixWord ++ tailWord_5010067) baseStart_5010067 baseEnd_5010067 := by
    simpa [prefixWord, tailWord_5010067, baseEnd_5010067] using wordTrace_append hprefix tailTrace_5010067
  have hstable : (prefixWord ++ tailWord_5010067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010067).length < 2 ^ (prefixWord ++ tailWord_5010067).sum := by decide
  have hdescent : baseEnd_5010067 < baseStart_5010067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010071 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 5]
def baseStart_5010071 : Nat := 118140960795 + 5010071 * 2 ^ 59
def prefixEnd_5010071 : Nat := 4983230072969 + 3 ^ 40 * 5010071 * 2
def baseEnd_5010071 : Nat := 285841615127996978652401

theorem tailTrace_5010071 : CollatzResearch.WordTrace tailWord_5010071 prefixEnd_5010071 285841615127996978652401 := by
  unfold tailWord_5010071
  simp only [CollatzResearch.WordTrace]
  refine ⟨182732301432375893849974067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121821534288250595899982711 182732301432375893849974067)
  ·
    refine ⟨274098452148563840774961101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182732301432375893849974067 274098452148563840774961101)
    ·
      refine ⟨102786919555711440290610413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274098452148563840774961101 102786919555711440290610413)
      ·
        refine ⟨38545094833391790108978905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102786919555711440290610413 38545094833391790108978905)
        ·
          refine ⟨28908821125043842581734179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38545094833391790108978905 28908821125043842581734179)
          ·
            refine ⟨43363231687565763872601269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28908821125043842581734179 43363231687565763872601269)
            ·
              refine ⟨4065302970709290363056369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43363231687565763872601269 4065302970709290363056369)
              ·
                refine ⟨3048977228031967772292277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065302970709290363056369 3048977228031967772292277)
                ·
                  refine ⟨285841615127996978652401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3048977228031967772292277 285841615127996978652401)
                  ·
                    rfl

theorem cell23_5010071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 5].length) (baseStart_5010071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010071 prefixEnd_5010071 := by exact prefixLift 5010071
  have htrace : WordTrace (prefixWord ++ tailWord_5010071) baseStart_5010071 baseEnd_5010071 := by
    simpa [prefixWord, tailWord_5010071, baseEnd_5010071] using wordTrace_append hprefix tailTrace_5010071
  have hstable : (prefixWord ++ tailWord_5010071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010071).length < 2 ^ (prefixWord ++ tailWord_5010071).sum := by decide
  have hdescent : baseEnd_5010071 < baseStart_5010071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010077 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5010077 : Nat := 118140960795 + 5010077 * 2 ^ 59
def prefixEnd_5010077 : Nat := 4983230072969 + 3 ^ 40 * 5010077 * 2
def baseEnd_5010077 : Nat := 2572577617035899784396581

theorem tailTrace_5010077 : CollatzResearch.WordTrace tailWord_5010077 prefixEnd_5010077 2572577617035899784396581 := by
  unfold tailWord_5010077
  simp only [CollatzResearch.WordTrace]
  refine ⟨182732520270354156874692485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121821680180236104583128323 182732520270354156874692485)
  ·
    refine ⟨34262347550691404414004841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182732520270354156874692485 34262347550691404414004841)
    ·
      refine ⟨25696760663018553310503631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34262347550691404414004841 25696760663018553310503631)
      ·
        refine ⟨38545140994527829965755447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25696760663018553310503631 38545140994527829965755447)
        ·
          refine ⟨57817711491791744948633171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38545140994527829965755447 57817711491791744948633171)
          ·
            refine ⟨86726567237687617422949757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57817711491791744948633171 86726567237687617422949757)
            ·
              refine ⟨32522462714132856533606159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86726567237687617422949757 32522462714132856533606159)
              ·
                refine ⟨48783694071199284800409239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32522462714132856533606159 48783694071199284800409239)
                ·
                  refine ⟨73175541106798927200613859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48783694071199284800409239 73175541106798927200613859)
                  ·
                    refine ⟨109763311660198390800920789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73175541106798927200613859 109763311660198390800920789)
                    ·
                      refine ⟨2572577617035899784396581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109763311660198390800920789 2572577617035899784396581)
                      ·
                        rfl

theorem cell23_5010077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5010077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010077 prefixEnd_5010077 := by exact prefixLift 5010077
  have htrace : WordTrace (prefixWord ++ tailWord_5010077) baseStart_5010077 baseEnd_5010077 := by
    simpa [prefixWord, tailWord_5010077, baseEnd_5010077] using wordTrace_append hprefix tailTrace_5010077
  have hstable : (prefixWord ++ tailWord_5010077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010077).length < 2 ^ (prefixWord ++ tailWord_5010077).sum := by decide
  have hdescent : baseEnd_5010077 < baseStart_5010077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010101 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_5010101 : Nat := 118140960795 + 5010101 * 2 ^ 59
def prefixEnd_5010101 : Nat := 4983230072969 + 3 ^ 40 * 5010101 * 2
def baseEnd_5010101 : Nat := 857529980190535896832157

theorem tailTrace_5010101 : CollatzResearch.WordTrace tailWord_5010101 prefixEnd_5010101 857529980190535896832157 := by
  unfold tailWord_5010101
  simp only [CollatzResearch.WordTrace]
  refine ⟨182733395622267208973566157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121822263748178139315710771 182733395622267208973566157)
  ·
    refine ⟨68525023358350203365087309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182733395622267208973566157 68525023358350203365087309)
    ·
      refine ⟨25696883759381326261907741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68525023358350203365087309 25696883759381326261907741)
      ·
        refine ⟨9636331409767997348215403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25696883759381326261907741 9636331409767997348215403)
        ·
          refine ⟨14454497114651996022323105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636331409767997348215403 14454497114651996022323105)
          ·
            refine ⟨10840872835988997016742329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14454497114651996022323105 10840872835988997016742329)
            ·
              refine ⟨8130654626991747762556747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10840872835988997016742329 8130654626991747762556747)
              ·
                refine ⟨12195981940487621643835121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130654626991747762556747 12195981940487621643835121)
                ·
                  refine ⟨9146986455365716232876341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12195981940487621643835121 9146986455365716232876341)
                  ·
                    refine ⟨857529980190535896832157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9146986455365716232876341 857529980190535896832157)
                    ·
                      rfl

theorem cell23_5010101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_5010101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010101 prefixEnd_5010101 := by exact prefixLift 5010101
  have htrace : WordTrace (prefixWord ++ tailWord_5010101) baseStart_5010101 baseEnd_5010101 := by
    simpa [prefixWord, tailWord_5010101, baseEnd_5010101] using wordTrace_append hprefix tailTrace_5010101
  have hstable : (prefixWord ++ tailWord_5010101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010101).length < 2 ^ (prefixWord ++ tailWord_5010101).sum := by decide
  have hdescent : baseEnd_5010101 < baseStart_5010101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010104 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_5010104 : Nat := 118140960795 + 5010104 * 2 ^ 59
def prefixEnd_5010104 : Nat := 4983230072969 + 3 ^ 40 * 5010104 * 2
def baseEnd_5010104 : Nat := 2572591481013571178758957

theorem tailTrace_5010104 : CollatzResearch.WordTrace tailWord_5010104 prefixEnd_5010104 2572591481013571178758957 := by
  unfold tailWord_5010104
  simp only [CollatzResearch.WordTrace]
  refine ⟨91366752520628170242962683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121822336694170893657283577 91366752520628170242962683)
  ·
    refine ⟨137050128780942255364444025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91366752520628170242962683 137050128780942255364444025)
    ·
      refine ⟨102787596585706691523333019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137050128780942255364444025 102787596585706691523333019)
      ·
        refine ⟨154181394878560037284999529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102787596585706691523333019 154181394878560037284999529)
        ·
          refine ⟨115636046158920027963749647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154181394878560037284999529 115636046158920027963749647)
          ·
            refine ⟨173454069238380041945624471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115636046158920027963749647 173454069238380041945624471)
            ·
              refine ⟨260181103857570062918436707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173454069238380041945624471 260181103857570062918436707)
              ·
                refine ⟨390271655786355094377655061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260181103857570062918436707 390271655786355094377655061)
                ·
                  refine ⟨18293983864985395048952581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 390271655786355094377655061 18293983864985395048952581)
                  ·
                    refine ⟨3430121974684761571678609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18293983864985395048952581 3430121974684761571678609)
                    ·
                      refine ⟨2572591481013571178758957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430121974684761571678609 2572591481013571178758957)
                      ·
                        rfl

theorem cell23_5010104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_5010104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010104 prefixEnd_5010104 := by exact prefixLift 5010104
  have htrace : WordTrace (prefixWord ++ tailWord_5010104) baseStart_5010104 baseEnd_5010104 := by
    simpa [prefixWord, tailWord_5010104, baseEnd_5010104] using wordTrace_append hprefix tailTrace_5010104
  have hstable : (prefixWord ++ tailWord_5010104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010104).length < 2 ^ (prefixWord ++ tailWord_5010104).sum := by decide
  have hdescent : baseEnd_5010104 < baseStart_5010104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010158 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_5010158 : Nat := 118140960795 + 5010158 * 2 ^ 59
def prefixEnd_5010158 : Nat := 4983230072969 + 3 ^ 40 * 5010158 * 2
def baseEnd_5010158 : Nat := 2572619208968913967483709

theorem tailTrace_5010158 : CollatzResearch.WordTrace tailWord_5010158 prefixEnd_5010158 2572619208968913967483709 := by
  unfold tailWord_5010158
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841934322882588463548891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121823649722040471805594085 22841934322882588463548891)
  ·
    refine ⟨34262901484323882695323337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22841934322882588463548891 34262901484323882695323337)
    ·
      refine ⟨25697176113242912021492503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34262901484323882695323337 25697176113242912021492503)
      ·
        refine ⟨38545764169864368032238755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25697176113242912021492503 38545764169864368032238755)
        ·
          refine ⟨57818646254796552048358133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38545764169864368032238755 57818646254796552048358133)
          ·
            refine ⟨5420498086387176754533575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57818646254796552048358133 5420498086387176754533575)
            ·
              refine ⟨8130747129580765131800363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420498086387176754533575 8130747129580765131800363)
              ·
                refine ⟨12196120694371147697700545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130747129580765131800363 12196120694371147697700545)
                ·
                  refine ⟨9147090520778360773275409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12196120694371147697700545 9147090520778360773275409)
                  ·
                    refine ⟨6860317890583770579956557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9147090520778360773275409 6860317890583770579956557)
                    ·
                      refine ⟨2572619208968913967483709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860317890583770579956557 2572619208968913967483709)
                      ·
                        rfl

theorem cell23_5010158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_5010158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010158 prefixEnd_5010158 := by exact prefixLift 5010158
  have htrace : WordTrace (prefixWord ++ tailWord_5010158) baseStart_5010158 baseEnd_5010158 := by
    simpa [prefixWord, tailWord_5010158, baseEnd_5010158] using wordTrace_append hprefix tailTrace_5010158
  have hstable : (prefixWord ++ tailWord_5010158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010158).length < 2 ^ (prefixWord ++ tailWord_5010158).sum := by decide
  have hdescent : baseEnd_5010158 < baseStart_5010158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010167 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_5010167 : Nat := 118140960795 + 5010167 * 2 ^ 59
def prefixEnd_5010167 : Nat := 4983230072969 + 3 ^ 40 * 5010167 * 2
def baseEnd_5010167 : Nat := 2572623830294804432271167

theorem tailTrace_5010167 : CollatzResearch.WordTrace tailWord_5010167 prefixEnd_5010167 2572623830294804432271167 := by
  unfold tailWord_5010167
  simp only [CollatzResearch.WordTrace]
  refine ⟨182735802840028102245468755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121823868560018734830312503 182735802840028102245468755)
  ·
    refine ⟨274103704260042153368203133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182735802840028102245468755 274103704260042153368203133)
    ·
      refine ⟨102788889097515807513076175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274103704260042153368203133 102788889097515807513076175)
      ·
        refine ⟨154183333646273711269614263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102788889097515807513076175 154183333646273711269614263)
        ·
          refine ⟨231275000469410566904421395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154183333646273711269614263 231275000469410566904421395)
          ·
            refine ⟨346912500704115850356632093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231275000469410566904421395 346912500704115850356632093)
            ·
              refine ⟨130092187764043443883737035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346912500704115850356632093 130092187764043443883737035)
              ·
                refine ⟨195138281646065165825605553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130092187764043443883737035 195138281646065165825605553)
                ·
                  refine ⟨146353711234548874369204165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195138281646065165825605553 146353711234548874369204165)
                  ·
                    refine ⟨27441320856477913944225781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146353711234548874369204165 27441320856477913944225781)
                    ·
                      refine ⟨2572623830294804432271167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27441320856477913944225781 2572623830294804432271167)
                      ·
                        rfl

theorem cell23_5010167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_5010167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010167 prefixEnd_5010167 := by exact prefixLift 5010167
  have htrace : WordTrace (prefixWord ++ tailWord_5010167) baseStart_5010167 baseEnd_5010167 := by
    simpa [prefixWord, tailWord_5010167, baseEnd_5010167] using wordTrace_append hprefix tailTrace_5010167
  have hstable : (prefixWord ++ tailWord_5010167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010167).length < 2 ^ (prefixWord ++ tailWord_5010167).sum := by decide
  have hdescent : baseEnd_5010167 < baseStart_5010167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010178 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_5010178 : Nat := 118140960795 + 5010178 * 2 ^ 59
def prefixEnd_5010178 : Nat := 4983230072969 + 3 ^ 40 * 5010178 * 2
def baseEnd_5010178 : Nat := 285847719842444876581513

theorem tailTrace_5010178 : CollatzResearch.WordTrace tailWord_5010178 prefixEnd_5010178 285847719842444876581513 := by
  unfold tailWord_5010178
  simp only [CollatzResearch.WordTrace]
  refine ⟨45684051010747062781029797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121824136028658834082746125 45684051010747062781029797)
  ·
    refine ⟨8565759564515074271443087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45684051010747062781029797 8565759564515074271443087)
    ·
      refine ⟨12848639346772611407164631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8565759564515074271443087 12848639346772611407164631)
      ·
        refine ⟨19272959020158917110746947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12848639346772611407164631 19272959020158917110746947)
        ·
          refine ⟨28909438530238375666120421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19272959020158917110746947 28909438530238375666120421)
          ·
            refine ⟨5420519724419695437397579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28909438530238375666120421 5420519724419695437397579)
            ·
              refine ⟨8130779586629543156096369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420519724419695437397579 8130779586629543156096369)
              ·
                refine ⟨6098084689972157367072277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8130779586629543156096369 6098084689972157367072277)
                ·
                  refine ⟨285847719842444876581513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6098084689972157367072277 285847719842444876581513)
                  ·
                    rfl

theorem cell23_5010178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_5010178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010178 prefixEnd_5010178 := by exact prefixLift 5010178
  have htrace : WordTrace (prefixWord ++ tailWord_5010178) baseStart_5010178 baseEnd_5010178 := by
    simpa [prefixWord, tailWord_5010178, baseEnd_5010178] using wordTrace_append hprefix tailTrace_5010178
  have hstable : (prefixWord ++ tailWord_5010178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010178).length < 2 ^ (prefixWord ++ tailWord_5010178).sum := by decide
  have hdescent : baseEnd_5010178 < baseStart_5010178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010181 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_5010181 : Nat := 118140960795 + 5010181 * 2 ^ 59
def prefixEnd_5010181 : Nat := 4983230072969 + 3 ^ 40 * 5010181 * 2
def baseEnd_5010181 : Nat := 2572631019023967377496103

theorem tailTrace_5010181 : CollatzResearch.WordTrace tailWord_5010181 prefixEnd_5010181 2572631019023967377496103 := by
  unfold tailWord_5010181
  simp only [CollatzResearch.WordTrace]
  refine ⟨182736313461977382636478397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121824208974651588424318931 182736313461977382636478397)
  ·
    refine ⟨68526117548241518488679399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182736313461977382636478397 68526117548241518488679399)
    ·
      refine ⟨102789176322362277733019099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68526117548241518488679399 102789176322362277733019099)
      ·
        refine ⟨154183764483543416599528649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102789176322362277733019099 154183764483543416599528649)
        ·
          refine ⟨115637823362657562449646487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154183764483543416599528649 115637823362657562449646487)
          ·
            refine ⟨173456735043986343674469731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115637823362657562449646487 173456735043986343674469731)
            ·
              refine ⟨260185102565979515511704597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173456735043986343674469731 260185102565979515511704597)
              ·
                refine ⟨12196176682780289789611153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260185102565979515511704597 12196176682780289789611153)
                ·
                  refine ⟨9147132512085217342208365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12196176682780289789611153 9147132512085217342208365)
                  ·
                    refine ⟨3430174692031956503328137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9147132512085217342208365 3430174692031956503328137)
                    ·
                      refine ⟨2572631019023967377496103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430174692031956503328137 2572631019023967377496103)
                      ·
                        rfl

theorem cell23_5010181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_5010181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010181 prefixEnd_5010181 := by exact prefixLift 5010181
  have htrace : WordTrace (prefixWord ++ tailWord_5010181) baseStart_5010181 baseEnd_5010181 := by
    simpa [prefixWord, tailWord_5010181, baseEnd_5010181] using wordTrace_append hprefix tailTrace_5010181
  have hstable : (prefixWord ++ tailWord_5010181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010181).length < 2 ^ (prefixWord ++ tailWord_5010181).sum := by decide
  have hdescent : baseEnd_5010181 < baseStart_5010181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010217 : List Nat := [1, 2, 1, 1, 1, 1, 1, 15]
def baseStart_5010217 : Nat := 118140960795 + 5010217 * 2 ^ 59
def prefixEnd_5010217 : Nat := 4983230072969 + 3 ^ 40 * 5010217 * 2
def baseEnd_5010217 : Nat := 95283314975093675431331

theorem tailTrace_5010217 : CollatzResearch.WordTrace tailWord_5010217 prefixEnd_5010217 95283314975093675431331 := by
  unfold tailWord_5010217
  simp only [CollatzResearch.WordTrace]
  refine ⟨182737626489846960784788905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121825084326564640523192603 182737626489846960784788905)
  ·
    refine ⟨137053219867385220588591679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182737626489846960784788905 137053219867385220588591679)
    ·
      refine ⟨205579829801077830882887519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137053219867385220588591679 205579829801077830882887519)
      ·
        refine ⟨308369744701616746324331279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205579829801077830882887519 308369744701616746324331279)
        ·
          refine ⟨462554617052425119486496919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308369744701616746324331279 462554617052425119486496919)
          ·
            refine ⟨693831925578637679229745379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462554617052425119486496919 693831925578637679229745379)
            ·
              refine ⟨1040747888367956518844618069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693831925578637679229745379 1040747888367956518844618069)
              ·
                refine ⟨95283314975093675431331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 1040747888367956518844618069 95283314975093675431331)
                ·
                  rfl

theorem cell23_5010217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 15].length) (baseStart_5010217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010217 prefixEnd_5010217 := by exact prefixLift 5010217
  have htrace : WordTrace (prefixWord ++ tailWord_5010217) baseStart_5010217 baseEnd_5010217 := by
    simpa [prefixWord, tailWord_5010217, baseEnd_5010217] using wordTrace_append hprefix tailTrace_5010217
  have hstable : (prefixWord ++ tailWord_5010217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010217).length < 2 ^ (prefixWord ++ tailWord_5010217).sum := by decide
  have hdescent : baseEnd_5010217 < baseStart_5010217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010222 : List Nat := [4, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5010222 : Nat := 118140960795 + 5010222 * 2 ^ 59
def prefixEnd_5010222 : Nat := 4983230072969 + 3 ^ 40 * 5010222 * 2
def baseEnd_5010222 : Nat := 2572652071730801717083415

theorem tailTrace_5010222 : CollatzResearch.WordTrace tailWord_5010222 prefixEnd_5010222 2572652071730801717083415 := by
  unfold tailWord_5010222
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842226106853605829840115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121825205903219231092480613 22842226106853605829840115)
  ·
    refine ⟨34263339160280408744760173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22842226106853605829840115 34263339160280408744760173)
    ·
      refine ⟨12848752185105153279285065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34263339160280408744760173 12848752185105153279285065)
      ·
        refine ⟨9636564138828864959463799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12848752185105153279285065 9636564138828864959463799)
        ·
          refine ⟨14454846208243297439195699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636564138828864959463799 14454846208243297439195699)
          ·
            refine ⟨21682269312364946158793549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14454846208243297439195699 21682269312364946158793549)
            ·
              refine ⟨8130850992136854809547581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21682269312364946158793549 8130850992136854809547581)
              ·
                refine ⟨3049069122051320553580343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8130850992136854809547581 3049069122051320553580343)
                ·
                  refine ⟨4573603683076980830370515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049069122051320553580343 4573603683076980830370515)
                  ·
                    refine ⟨6860405524615471245555773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573603683076980830370515 6860405524615471245555773)
                    ·
                      refine ⟨2572652071730801717083415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860405524615471245555773 2572652071730801717083415)
                      ·
                        rfl

theorem cell23_5010222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5010222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010222 prefixEnd_5010222 := by exact prefixLift 5010222
  have htrace : WordTrace (prefixWord ++ tailWord_5010222) baseStart_5010222 baseEnd_5010222 := by
    simpa [prefixWord, tailWord_5010222, baseEnd_5010222] using wordTrace_append hprefix tailTrace_5010222
  have hstable : (prefixWord ++ tailWord_5010222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010222).length < 2 ^ (prefixWord ++ tailWord_5010222).sum := by decide
  have hdescent : baseEnd_5010222 < baseStart_5010222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010224 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_5010224 : Nat := 118140960795 + 5010224 * 2 ^ 59
def prefixEnd_5010224 : Nat := 4983230072969 + 3 ^ 40 * 5010224 * 2
def baseEnd_5010224 : Nat := 2572653098692110709258405

theorem tailTrace_5010224 : CollatzResearch.WordTrace tailWord_5010224 prefixEnd_5010224 2572653098692110709258405 := by
  unfold tailWord_5010224
  simp only [CollatzResearch.WordTrace]
  refine ⟨91368940900410800490146863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121825254533881067320195817 91368940900410800490146863)
  ·
    refine ⟨137053411350616200735220295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91368940900410800490146863 137053411350616200735220295)
    ·
      refine ⟨205580117025924301102830443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137053411350616200735220295 205580117025924301102830443)
      ·
        refine ⟨308370175538886451654245665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205580117025924301102830443 308370175538886451654245665)
        ·
          refine ⟨231277631654164838740684249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308370175538886451654245665 231277631654164838740684249)
          ·
            refine ⟨173458223740623629055513187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231277631654164838740684249 173458223740623629055513187)
            ·
              refine ⟨260187335610935443583269781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173458223740623629055513187 260187335610935443583269781)
              ·
                refine ⟨12196281356762598917965771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260187335610935443583269781 12196281356762598917965771)
                ·
                  refine ⟨18294422035143898376948657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12196281356762598917965771 18294422035143898376948657)
                  ·
                    refine ⟨13720816526357923782711493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18294422035143898376948657 13720816526357923782711493)
                    ·
                      refine ⟨2572653098692110709258405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13720816526357923782711493 2572653098692110709258405)
                      ·
                        rfl

theorem cell23_5010224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_5010224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010224 prefixEnd_5010224 := by exact prefixLift 5010224
  have htrace : WordTrace (prefixWord ++ tailWord_5010224) baseStart_5010224 baseEnd_5010224 := by
    simpa [prefixWord, tailWord_5010224, baseEnd_5010224] using wordTrace_append hprefix tailTrace_5010224
  have hstable : (prefixWord ++ tailWord_5010224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010224).length < 2 ^ (prefixWord ++ tailWord_5010224).sum := by decide
  have hdescent : baseEnd_5010224 < baseStart_5010224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010231 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_5010231 : Nat := 118140960795 + 5010231 * 2 ^ 59
def prefixEnd_5010231 : Nat := 4983230072969 + 3 ^ 40 * 5010231 * 2
def baseEnd_5010231 : Nat := 2572656693056692181870873

theorem tailTrace_5010231 : CollatzResearch.WordTrace tailWord_5010231 prefixEnd_5010231 2572656693056692181870873 := by
  unfold tailWord_5010231
  simp only [CollatzResearch.WordTrace]
  refine ⟨182738137111796241175798547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121825424741197494117199031 182738137111796241175798547)
  ·
    refine ⟨274107205667694361763697821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182738137111796241175798547 274107205667694361763697821)
    ·
      refine ⟨102790202125385385661386683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274107205667694361763697821 102790202125385385661386683)
      ·
        refine ⟨154185303188078078492080025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102790202125385385661386683 154185303188078078492080025)
        ·
          refine ⟨115638977391058558869060019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154185303188078078492080025 115638977391058558869060019)
          ·
            refine ⟨173458466086587838303590029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115638977391058558869060019 173458466086587838303590029)
            ·
              refine ⟨65046924782470439363846261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173458466086587838303590029 65046924782470439363846261)
              ·
                refine ⟨6098149198356603690360587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65046924782470439363846261 6098149198356603690360587)
                ·
                  refine ⟨9147223797534905535540881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6098149198356603690360587 9147223797534905535540881)
                  ·
                    refine ⟨6860417848151179151655661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9147223797534905535540881 6860417848151179151655661)
                    ·
                      refine ⟨2572656693056692181870873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860417848151179151655661 2572656693056692181870873)
                      ·
                        rfl

theorem cell23_5010231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_5010231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010231 prefixEnd_5010231 := by exact prefixLift 5010231
  have htrace : WordTrace (prefixWord ++ tailWord_5010231) baseStart_5010231 baseEnd_5010231 := by
    simpa [prefixWord, tailWord_5010231, baseEnd_5010231] using wordTrace_append hprefix tailTrace_5010231
  have hstable : (prefixWord ++ tailWord_5010231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010231).length < 2 ^ (prefixWord ++ tailWord_5010231).sum := by decide
  have hdescent : baseEnd_5010231 < baseStart_5010231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010261 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_5010261 : Nat := 118140960795 + 5010261 * 2 ^ 59
def prefixEnd_5010261 : Nat := 4983230072969 + 3 ^ 40 * 5010261 * 2
def baseEnd_5010261 : Nat := 2572672097476327064495735

theorem tailTrace_5010261 : CollatzResearch.WordTrace tailWord_5010261 prefixEnd_5010261 2572672097476327064495735 := by
  unfold tailWord_5010261
  simp only [CollatzResearch.WordTrace]
  refine ⟨182739231301687556299390637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121826154201125037532927091 182739231301687556299390637)
  ·
    refine ⟨68527211738132833612271489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182739231301687556299390637 68527211738132833612271489)
    ·
      refine ⟨51395408803599625209203617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68527211738132833612271489 51395408803599625209203617)
      ·
        refine ⟨38546556602699718906902713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51395408803599625209203617 38546556602699718906902713)
        ·
          refine ⟨28909917452024789180177035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38546556602699718906902713 28909917452024789180177035)
          ·
            refine ⟨43364876178037183770265553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28909917452024789180177035 43364876178037183770265553)
            ·
              refine ⟨32523657133527887827699165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43364876178037183770265553 32523657133527887827699165)
              ·
                refine ⟨12196371425072957935387187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32523657133527887827699165 12196371425072957935387187)
                ·
                  refine ⟨18294557137609436903080781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12196371425072957935387187 18294557137609436903080781)
                  ·
                    refine ⟨6860458926603538838655293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18294557137609436903080781 6860458926603538838655293)
                    ·
                      refine ⟨2572672097476327064495735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860458926603538838655293 2572672097476327064495735)
                      ·
                        rfl

theorem cell23_5010261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_5010261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010261 prefixEnd_5010261 := by exact prefixLift 5010261
  have htrace : WordTrace (prefixWord ++ tailWord_5010261) baseStart_5010261 baseEnd_5010261 := by
    simpa [prefixWord, tailWord_5010261, baseEnd_5010261] using wordTrace_append hprefix tailTrace_5010261
  have hstable : (prefixWord ++ tailWord_5010261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010261).length < 2 ^ (prefixWord ++ tailWord_5010261).sum := by decide
  have hdescent : baseEnd_5010261 < baseStart_5010261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010288 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2]
def baseStart_5010288 : Nat := 118140960795 + 5010288 * 2 ^ 59
def prefixEnd_5010288 : Nat := 4983230072969 + 3 ^ 40 * 5010288 * 2
def baseEnd_5010288 : Nat := 2572685961453998458858111

theorem tailTrace_5010288 : CollatzResearch.WordTrace tailWord_5010288 prefixEnd_5010288 2572685961453998458858111 := by
  unfold tailWord_5010288
  simp only [CollatzResearch.WordTrace]
  refine ⟨91370108036294869955311759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121826810715059826607082345 91370108036294869955311759)
  ·
    refine ⟨137055162054442304932967639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91370108036294869955311759 137055162054442304932967639)
    ·
      refine ⟨205582743081663457399451459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137055162054442304932967639 205582743081663457399451459)
      ·
        refine ⟨308374114622495186099177189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205582743081663457399451459 308374114622495186099177189)
        ·
          refine ⟨57820146491717847393595723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308374114622495186099177189 57820146491717847393595723)
          ·
            refine ⟨86730219737576771090393585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57820146491717847393595723 86730219737576771090393585)
            ·
              refine ⟨65047664803182578317795189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86730219737576771090393585 65047664803182578317795189)
              ·
                refine ⟨6098218575298366717293299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65047664803182578317795189 6098218575298366717293299)
                ·
                  refine ⟨9147327862947550075939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6098218575298366717293299 9147327862947550075939949)
                  ·
                    refine ⟨3430247948605331278477481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9147327862947550075939949 3430247948605331278477481)
                    ·
                      refine ⟨2572685961453998458858111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430247948605331278477481 2572685961453998458858111)
                      ·
                        rfl

theorem cell23_5010288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 1, 3, 2].length) (baseStart_5010288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010288 prefixEnd_5010288 := by exact prefixLift 5010288
  have htrace : WordTrace (prefixWord ++ tailWord_5010288) baseStart_5010288 baseEnd_5010288 := by
    simpa [prefixWord, tailWord_5010288, baseEnd_5010288] using wordTrace_append hprefix tailTrace_5010288
  have hstable : (prefixWord ++ tailWord_5010288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010288).length < 2 ^ (prefixWord ++ tailWord_5010288).sum := by decide
  have hdescent : baseEnd_5010288 < baseStart_5010288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010304 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_5010304 : Nat := 118140960795 + 5010304 * 2 ^ 59
def prefixEnd_5010304 : Nat := 4983230072969 + 3 ^ 40 * 5010304 * 2
def baseEnd_5010304 : Nat := 2572694177144470396258037

theorem tailTrace_5010304 : CollatzResearch.WordTrace tailWord_5010304 prefixEnd_5010304 2572694177144470396258037 := by
  unfold tailWord_5010304
  simp only [CollatzResearch.WordTrace]
  refine ⟨91370399820265887321602983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121827199760354516428803977 91370399820265887321602983)
  ·
    refine ⟨137055599730398830982404475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91370399820265887321602983 137055599730398830982404475)
    ·
      refine ⟨205583399595598246473606713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137055599730398830982404475 205583399595598246473606713)
      ·
        refine ⟨154187549696698684855205035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205583399595598246473606713 154187549696698684855205035)
        ·
          refine ⟨231281324545048027282807553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154187549696698684855205035 231281324545048027282807553)
          ·
            refine ⟨173460993408786020462105665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231281324545048027282807553 173460993408786020462105665)
            ·
              refine ⟨130095745056589515346579249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173460993408786020462105665 130095745056589515346579249)
              ·
                refine ⟨97571808792442136509934437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130095745056589515346579249 97571808792442136509934437)
                ·
                  refine ⟨18294714148582900595612707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97571808792442136509934437 18294714148582900595612707)
                  ·
                    refine ⟨27442071222874350893419061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18294714148582900595612707 27442071222874350893419061)
                    ·
                      refine ⟨2572694177144470396258037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27442071222874350893419061 2572694177144470396258037)
                      ·
                        rfl

theorem cell23_5010304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_5010304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010304 prefixEnd_5010304 := by exact prefixLift 5010304
  have htrace : WordTrace (prefixWord ++ tailWord_5010304) baseStart_5010304 baseEnd_5010304 := by
    simpa [prefixWord, tailWord_5010304, baseEnd_5010304] using wordTrace_append hprefix tailTrace_5010304
  have hstable : (prefixWord ++ tailWord_5010304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010304).length < 2 ^ (prefixWord ++ tailWord_5010304).sum := by decide
  have hdescent : baseEnd_5010304 < baseStart_5010304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010311 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 2, 6]
def baseStart_5010311 : Nat := 118140960795 + 5010311 * 2 ^ 59
def prefixEnd_5010311 : Nat := 4983230072969 + 3 ^ 40 * 5010311 * 2
def baseEnd_5010311 : Nat := 857565923836350622956835

theorem tailTrace_5010311 : CollatzResearch.WordTrace tailWord_5010311 prefixEnd_5010311 857565923836350622956835 := by
  unfold tailWord_5010311
  simp only [CollatzResearch.WordTrace]
  refine ⟨182741054951506414838710787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121827369967670943225807191 182741054951506414838710787)
  ·
    refine ⟨274111582427259622258066181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182741054951506414838710787 274111582427259622258066181)
    ·
      refine ⟨51395921705111179173387409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274111582427259622258066181 51395921705111179173387409)
      ·
        refine ⟨38546941278833384380040557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51395921705111179173387409 38546941278833384380040557)
        ·
          refine ⟨14455102979562519142515209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38546941278833384380040557 14455102979562519142515209)
          ·
            refine ⟨10841327234671889356886407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14455102979562519142515209 10841327234671889356886407)
            ·
              refine ⟨16261990852007834035329611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841327234671889356886407 16261990852007834035329611)
              ·
                refine ⟨24392986278011751052994417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16261990852007834035329611 24392986278011751052994417)
                ·
                  refine ⟨18294739708508813289745813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24392986278011751052994417 18294739708508813289745813)
                  ·
                    refine ⟨857565923836350622956835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18294739708508813289745813 857565923836350622956835)
                    ·
                      rfl

theorem cell23_5010311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_5010311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010311 prefixEnd_5010311 := by exact prefixLift 5010311
  have htrace : WordTrace (prefixWord ++ tailWord_5010311) baseStart_5010311 baseEnd_5010311 := by
    simpa [prefixWord, tailWord_5010311, baseEnd_5010311] using wordTrace_append hprefix tailTrace_5010311
  have hstable : (prefixWord ++ tailWord_5010311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010311).length < 2 ^ (prefixWord ++ tailWord_5010311).sum := by decide
  have hdescent : baseEnd_5010311 < baseStart_5010311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010384 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_5010384 : Nat := 118140960795 + 5010384 * 2 ^ 59
def prefixEnd_5010384 : Nat := 4983230072969 + 3 ^ 40 * 5010384 * 2
def baseEnd_5010384 : Nat := 857578418532276694419223

theorem tailTrace_5010384 : CollatzResearch.WordTrace tailWord_5010384 prefixEnd_5010384 857578418532276694419223 := by
  unfold tailWord_5010384
  simp only [CollatzResearch.WordTrace]
  refine ⟨91371858740120974153059103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121829144986827965537412137 91371858740120974153059103)
  ·
    refine ⟨137057788110181461229588655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91371858740120974153059103 137057788110181461229588655)
    ·
      refine ⟨205586682165272191844382983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137057788110181461229588655 205586682165272191844382983)
      ·
        refine ⟨308380023247908287766574475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205586682165272191844382983 308380023247908287766574475)
        ·
          refine ⟨462570034871862431649861713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308380023247908287766574475 462570034871862431649861713)
          ·
            refine ⟨346927526153896823737396285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462570034871862431649861713 346927526153896823737396285)
            ·
              refine ⟨130097822307711308901523607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346927526153896823737396285 130097822307711308901523607)
              ·
                refine ⟨195146733461566963352285411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130097822307711308901523607 195146733461566963352285411)
                ·
                  refine ⟨292720100192350445028428117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195146733461566963352285411 292720100192350445028428117)
                  ·
                    refine ⟨857578418532276694419223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 292720100192350445028428117 857578418532276694419223)
                    ·
                      rfl

theorem cell23_5010384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_5010384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010384 prefixEnd_5010384 := by exact prefixLift 5010384
  have htrace : WordTrace (prefixWord ++ tailWord_5010384) baseStart_5010384 baseEnd_5010384 := by
    simpa [prefixWord, tailWord_5010384, baseEnd_5010384] using wordTrace_append hprefix tailTrace_5010384
  have hstable : (prefixWord ++ tailWord_5010384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010384).length < 2 ^ (prefixWord ++ tailWord_5010384).sum := by decide
  have hdescent : baseEnd_5010384 < baseStart_5010384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010405 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_5010405 : Nat := 118140960795 + 5010405 * 2 ^ 59
def prefixEnd_5010405 : Nat := 4983230072969 + 3 ^ 40 * 5010405 * 2
def baseEnd_5010405 : Nat := 857582012896858167031691

theorem tailTrace_5010405 : CollatzResearch.WordTrace tailWord_5010405 prefixEnd_5010405 857582012896858167031691 := by
  unfold tailWord_5010405
  simp only [CollatzResearch.WordTrace]
  refine ⟨182744483413165868892632669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121829655608777245928421779 182744483413165868892632669)
  ·
    refine ⟨68529181279937200834737251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182744483413165868892632669 68529181279937200834737251)
    ·
      refine ⟨102793771919905801252105877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68529181279937200834737251 102793771919905801252105877)
      ·
        refine ⟨4818458058745584433692463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102793771919905801252105877 4818458058745584433692463)
        ·
          refine ⟨7227687088118376650538695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4818458058745584433692463 7227687088118376650538695)
          ·
            refine ⟨10841530632177564975808043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227687088118376650538695 10841530632177564975808043)
            ·
              refine ⟨16262295948266347463712065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841530632177564975808043 16262295948266347463712065)
              ·
                refine ⟨12196721961199760597784049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16262295948266347463712065 12196721961199760597784049)
                ·
                  refine ⟨9147541470899820448338037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12196721961199760597784049 9147541470899820448338037)
                  ·
                    refine ⟨857582012896858167031691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9147541470899820448338037 857582012896858167031691)
                    ·
                      rfl

theorem cell23_5010405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_5010405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010405 prefixEnd_5010405 := by exact prefixLift 5010405
  have htrace : WordTrace (prefixWord ++ tailWord_5010405) baseStart_5010405 baseEnd_5010405 := by
    simpa [prefixWord, tailWord_5010405, baseEnd_5010405] using wordTrace_append hprefix tailTrace_5010405
  have hstable : (prefixWord ++ tailWord_5010405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010405).length < 2 ^ (prefixWord ++ tailWord_5010405).sum := by decide
  have hdescent : baseEnd_5010405 < baseStart_5010405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010408 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5010408 : Nat := 118140960795 + 5010408 * 2 ^ 59
def prefixEnd_5010408 : Nat := 4983230072969 + 3 ^ 40 * 5010408 * 2
def baseEnd_5010408 : Nat := 2572747579132537989357559

theorem tailTrace_5010408 : CollatzResearch.WordTrace tailWord_5010408 prefixEnd_5010408 2572747579132537989357559 := by
  unfold tailWord_5010408
  simp only [CollatzResearch.WordTrace]
  refine ⟨91372296416077500202495939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121829728554770000269994585 91372296416077500202495939)
  ·
    refine ⟨137058444624116250303743909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91372296416077500202495939 137058444624116250303743909)
    ·
      refine ⟨25698458367021796931951983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137058444624116250303743909 25698458367021796931951983)
      ·
        refine ⟨38547687550532695397927975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25698458367021796931951983 38547687550532695397927975)
        ·
          refine ⟨57821531325799043096891963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38547687550532695397927975 57821531325799043096891963)
          ·
            refine ⟨86732296988698564645337945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57821531325799043096891963 86732296988698564645337945)
            ·
              refine ⟨65049222741523923484003459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86732296988698564645337945 65049222741523923484003459)
              ·
                refine ⟨97573834112285885226005189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65049222741523923484003459 97573834112285885226005189)
                ·
                  refine ⟨18295093896053603479875973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97573834112285885226005189 18295093896053603479875973)
                  ·
                    refine ⟨3430330105510050652476745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18295093896053603479875973 3430330105510050652476745)
                    ·
                      refine ⟨2572747579132537989357559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430330105510050652476745 2572747579132537989357559)
                      ·
                        rfl

theorem cell23_5010408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5010408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010408 prefixEnd_5010408 := by exact prefixLift 5010408
  have htrace : WordTrace (prefixWord ++ tailWord_5010408) baseStart_5010408 baseEnd_5010408 := by
    simpa [prefixWord, tailWord_5010408, baseEnd_5010408] using wordTrace_append hprefix tailTrace_5010408
  have hstable : (prefixWord ++ tailWord_5010408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010408).length < 2 ^ (prefixWord ++ tailWord_5010408).sum := by decide
  have hdescent : baseEnd_5010408 < baseStart_5010408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010441 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_5010441 : Nat := 118140960795 + 5010441 * 2 ^ 59
def prefixEnd_5010441 : Nat := 4983230072969 + 3 ^ 40 * 5010441 * 2
def baseEnd_5010441 : Nat := 2572764523994136360244907

theorem tailTrace_5010441 : CollatzResearch.WordTrace tailWord_5010441 prefixEnd_5010441 2572764523994136360244907 := by
  unfold tailWord_5010441
  simp only [CollatzResearch.WordTrace]
  refine ⟨182745796441035447040943177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121830530960690298027295451 182745796441035447040943177)
  ·
    refine ⟨137059347330776585280707383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182745796441035447040943177 137059347330776585280707383)
    ·
      refine ⟨205589020996164877921061075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137059347330776585280707383 205589020996164877921061075)
      ·
        refine ⟨308383531494247316881591613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205589020996164877921061075 308383531494247316881591613)
        ·
          refine ⟨115643824310342743830596855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308383531494247316881591613 115643824310342743830596855)
          ·
            refine ⟨173465736465514115745895283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115643824310342743830596855 173465736465514115745895283)
            ·
              refine ⟨260198604698271173618842925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173465736465514115745895283 260198604698271173618842925)
              ·
                refine ⟨97574476761851690107066097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260198604698271173618842925 97574476761851690107066097)
                ·
                  refine ⟨73180857571388767580299573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97574476761851690107066097 73180857571388767580299573)
                  ·
                    refine ⟨6860705397317696960653085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73180857571388767580299573 6860705397317696960653085)
                    ·
                      refine ⟨2572764523994136360244907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860705397317696960653085 2572764523994136360244907)
                      ·
                        rfl

theorem cell23_5010441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_5010441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010441 prefixEnd_5010441 := by exact prefixLift 5010441
  have htrace : WordTrace (prefixWord ++ tailWord_5010441) baseStart_5010441 baseEnd_5010441 := by
    simpa [prefixWord, tailWord_5010441, baseEnd_5010441] using wordTrace_append hprefix tailTrace_5010441
  have hstable : (prefixWord ++ tailWord_5010441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010441).length < 2 ^ (prefixWord ++ tailWord_5010441).sum := by decide
  have hdescent : baseEnd_5010441 < baseStart_5010441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010478 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5010478 : Nat := 118140960795 + 5010478 * 2 ^ 59
def prefixEnd_5010478 : Nat := 4983230072969 + 3 ^ 40 * 5010478 * 2
def baseEnd_5010478 : Nat := 857594507592784238494079

theorem tailTrace_5010478 : CollatzResearch.WordTrace tailWord_5010478 prefixEnd_5010478 857594507592784238494079 := by
  unfold tailWord_5010478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843393242737675295005011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121831430627934268240026725 22843393242737675295005011)
  ·
    refine ⟨34265089864106512942507517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22843393242737675295005011 34265089864106512942507517)
    ·
      refine ⟨12849408699039942353440319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34265089864106512942507517 12849408699039942353440319)
      ·
        refine ⟨19274113048559913530160479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849408699039942353440319 19274113048559913530160479)
        ·
          refine ⟨28911169572839870295240719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19274113048559913530160479 28911169572839870295240719)
          ·
            refine ⟨43366754359259805442861079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28911169572839870295240719 43366754359259805442861079)
            ·
              refine ⟨65050131538889708164291619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43366754359259805442861079 65050131538889708164291619)
              ·
                refine ⟨97575197308334562246437429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65050131538889708164291619 97575197308334562246437429)
                ·
                  refine ⟨9147674747656365210603509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97575197308334562246437429 9147674747656365210603509)
                  ·
                    refine ⟨857594507592784238494079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9147674747656365210603509 857594507592784238494079)
                    ·
                      rfl

theorem cell23_5010478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5010478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010478 prefixEnd_5010478 := by exact prefixLift 5010478
  have htrace : WordTrace (prefixWord ++ tailWord_5010478) baseStart_5010478 baseEnd_5010478 := by
    simpa [prefixWord, tailWord_5010478, baseEnd_5010478] using wordTrace_append hprefix tailTrace_5010478
  have hstable : (prefixWord ++ tailWord_5010478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010478).length < 2 ^ (prefixWord ++ tailWord_5010478).sum := by decide
  have hdescent : baseEnd_5010478 < baseStart_5010478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010508 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_5010508 : Nat := 118140960795 + 5010508 * 2 ^ 59
def prefixEnd_5010508 : Nat := 4983230072969 + 3 ^ 40 * 5010508 * 2
def baseEnd_5010508 : Nat := 857599642399329199369033

theorem tailTrace_5010508 : CollatzResearch.WordTrace tailWord_5010508 prefixEnd_5010508 857599642399329199369033 := by
  unfold tailWord_5010508
  simp only [CollatzResearch.WordTrace]
  refine ⟨91374120065896358741816089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121832160087861811655754785 91374120065896358741816089)
  ·
    refine ⟨68530590049422269056362067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91374120065896358741816089 68530590049422269056362067)
    ·
      refine ⟨102795885074133403584543101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68530590049422269056362067 102795885074133403584543101)
      ·
        refine ⟨38548456902800026344203663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102795885074133403584543101 38548456902800026344203663)
        ·
          refine ⟨57822685354200039516305495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38548456902800026344203663 57822685354200039516305495)
          ·
            refine ⟨86734028031300059274458243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57822685354200039516305495 86734028031300059274458243)
            ·
              refine ⟨130101042046950088911687365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86734028031300059274458243 130101042046950088911687365)
              ·
                refine ⟨24393945383803141670941381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130101042046950088911687365 24393945383803141670941381)
                ·
                  refine ⟨4573864759463089063301509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24393945383803141670941381 4573864759463089063301509)
                  ·
                    refine ⟨857599642399329199369033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4573864759463089063301509 857599642399329199369033)
                    ·
                      rfl

theorem cell23_5010508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_5010508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010508 prefixEnd_5010508 := by exact prefixLift 5010508
  have htrace : WordTrace (prefixWord ++ tailWord_5010508) baseStart_5010508 baseEnd_5010508 := by
    simpa [prefixWord, tailWord_5010508, baseEnd_5010508] using wordTrace_append hprefix tailTrace_5010508
  have hstable : (prefixWord ++ tailWord_5010508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010508).length < 2 ^ (prefixWord ++ tailWord_5010508).sum := by decide
  have hdescent : baseEnd_5010508 < baseStart_5010508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010509 : List Nat := [1, 6, 1, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5010509 : Nat := 118140960795 + 5010509 * 2 ^ 59
def prefixEnd_5010509 : Nat := 4983230072969 + 3 ^ 40 * 5010509 * 2
def baseEnd_5010509 : Nat := 2572799440678642094194595

theorem tailTrace_5010509 : CollatzResearch.WordTrace tailWord_5010509 prefixEnd_5010509 2572799440678642094194595 := by
  unfold tailWord_5010509
  simp only [CollatzResearch.WordTrace]
  refine ⟨182748276604789094654418581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121832184403192729769612387 182748276604789094654418581)
  ·
    refine ⟨8566325465849488811925871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182748276604789094654418581 8566325465849488811925871)
    ·
      refine ⟨12849488198774233217888807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566325465849488811925871 12849488198774233217888807)
      ·
        refine ⟨19274232298161349826833211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849488198774233217888807 19274232298161349826833211)
        ·
          refine ⟨28911348447242024740249817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19274232298161349826833211 28911348447242024740249817)
          ·
            refine ⟨21683511335431518555187363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28911348447242024740249817 21683511335431518555187363)
            ·
              refine ⟨32525267003147277832781045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21683511335431518555187363 32525267003147277832781045)
              ·
                refine ⟨3049243781545057296823223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32525267003147277832781045 3049243781545057296823223)
                ·
                  refine ⟨4573865672317585945234835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049243781545057296823223 4573865672317585945234835)
                  ·
                    refine ⟨6860798508476378917852253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573865672317585945234835 6860798508476378917852253)
                    ·
                      refine ⟨2572799440678642094194595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860798508476378917852253 2572799440678642094194595)
                      ·
                        rfl

theorem cell23_5010509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5010509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010509 prefixEnd_5010509 := by exact prefixLift 5010509
  have htrace : WordTrace (prefixWord ++ tailWord_5010509) baseStart_5010509 baseEnd_5010509 := by
    simpa [prefixWord, tailWord_5010509, baseEnd_5010509] using wordTrace_append hprefix tailTrace_5010509
  have hstable : (prefixWord ++ tailWord_5010509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010509).length < 2 ^ (prefixWord ++ tailWord_5010509).sum := by decide
  have hdescent : baseEnd_5010509 < baseStart_5010509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010526 : List Nat := [4, 4, 1, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5010526 : Nat := 118140960795 + 5010526 * 2 ^ 59
def prefixEnd_5010526 : Nat := 4983230072969 + 3 ^ 40 * 5010526 * 2
def baseEnd_5010526 : Nat := 2572808169849768527682017

theorem tailTrace_5010526 : CollatzResearch.WordTrace tailWord_5010526 prefixEnd_5010526 2572808169849768527682017 := by
  unfold tailWord_5010526
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843612080715938319723429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121832597763818337705191621 22843612080715938319723429)
  ·
    refine ⟨4283177265134238434948143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22843612080715938319723429 4283177265134238434948143)
    ·
      refine ⟨6424765897701357652422215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283177265134238434948143 6424765897701357652422215)
      ·
        refine ⟨9637148846552036478633323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6424765897701357652422215 9637148846552036478633323)
        ·
          refine ⟨14455723269828054717949985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637148846552036478633323 14455723269828054717949985)
          ·
            refine ⟨10841792452371041038462489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14455723269828054717949985 10841792452371041038462489)
            ·
              refine ⟨8131344339278280778846867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10841792452371041038462489 8131344339278280778846867)
              ·
                refine ⟨12197016508917421168270301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8131344339278280778846867 12197016508917421168270301)
                ·
                  refine ⟨4573881190844032938101363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12197016508917421168270301 4573881190844032938101363)
                  ·
                    refine ⟨6860821786266049407152045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573881190844032938101363 6860821786266049407152045)
                    ·
                      refine ⟨2572808169849768527682017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860821786266049407152045 2572808169849768527682017)
                      ·
                        rfl

theorem cell23_5010526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5010526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010526 prefixEnd_5010526 := by exact prefixLift 5010526
  have htrace : WordTrace (prefixWord ++ tailWord_5010526) baseStart_5010526 baseEnd_5010526 := by
    simpa [prefixWord, tailWord_5010526, baseEnd_5010526] using wordTrace_append hprefix tailTrace_5010526
  have hstable : (prefixWord ++ tailWord_5010526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010526).length < 2 ^ (prefixWord ++ tailWord_5010526).sum := by decide
  have hdescent : baseEnd_5010526 < baseStart_5010526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010531 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5010531 : Nat := 118140960795 + 5010531 * 2 ^ 59
def prefixEnd_5010531 : Nat := 4983230072969 + 3 ^ 40 * 5010531 * 2
def baseEnd_5010531 : Nat := 2572810737253041008119493

theorem tailTrace_5010531 : CollatzResearch.WordTrace tailWord_5010531 prefixEnd_5010531 2572810737253041008119493 := by
  unfold tailWord_5010531
  simp only [CollatzResearch.WordTrace]
  refine ⟨182749079010709392411719447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121832719340472928274479631 182749079010709392411719447)
  ·
    refine ⟨274123618516064088617579171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182749079010709392411719447 274123618516064088617579171)
    ·
      refine ⟨411185427774096132926368757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274123618516064088617579171 411185427774096132926368757)
      ·
        refine ⟨38548633853821512461847071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 411185427774096132926368757 38548633853821512461847071)
        ·
          refine ⟨57822950780732268692770607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38548633853821512461847071 57822950780732268692770607)
          ·
            refine ⟨86734426171098403039155911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57822950780732268692770607 86734426171098403039155911)
            ·
              refine ⟨130101639256647604558733867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86734426171098403039155911 130101639256647604558733867)
              ·
                refine ⟨195152458884971406838100801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130101639256647604558733867 195152458884971406838100801)
                ·
                  refine ⟨146364344163728555128575601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195152458884971406838100801 146364344163728555128575601)
                  ·
                    refine ⟨109773258122796416346431701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146364344163728555128575601 109773258122796416346431701)
                    ·
                      refine ⟨2572810737253041008119493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109773258122796416346431701 2572810737253041008119493)
                      ·
                        rfl

theorem cell23_5010531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5010531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010531 prefixEnd_5010531 := by exact prefixLift 5010531
  have htrace : WordTrace (prefixWord ++ tailWord_5010531) baseStart_5010531 baseEnd_5010531 := by
    simpa [prefixWord, tailWord_5010531, baseEnd_5010531] using wordTrace_append hprefix tailTrace_5010531
  have hstable : (prefixWord ++ tailWord_5010531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010531).length < 2 ^ (prefixWord ++ tailWord_5010531).sum := by decide
  have hdescent : baseEnd_5010531 < baseStart_5010531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010549 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5010549 : Nat := 118140960795 + 5010549 * 2 ^ 59
def prefixEnd_5010549 : Nat := 4983230072969 + 3 ^ 40 * 5010549 * 2
def baseEnd_5010549 : Nat := 2572819979904821937694411

theorem tailTrace_5010549 : CollatzResearch.WordTrace tailWord_5010549 prefixEnd_5010549 2572819979904821937694411 := by
  unfold tailWord_5010549
  simp only [CollatzResearch.WordTrace]
  refine ⟨182749735524644181485874701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121833157016429454323916467 182749735524644181485874701)
  ·
    refine ⟨68531150821741568057203013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182749735524644181485874701 68531150821741568057203013)
    ·
      refine ⟨12849590779076544010725565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68531150821741568057203013 12849590779076544010725565)
      ·
        refine ⟨4818596542153704004022087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12849590779076544010725565 4818596542153704004022087)
        ·
          refine ⟨7227894813230556006033131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4818596542153704004022087 7227894813230556006033131)
          ·
            refine ⟨10841842219845834009049697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227894813230556006033131 10841842219845834009049697)
            ·
              refine ⟨8131381664884375506787273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10841842219845834009049697 8131381664884375506787273)
              ·
                refine ⟨6098536248663281630090455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8131381664884375506787273 6098536248663281630090455)
                ·
                  refine ⟨9147804372994922445135683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6098536248663281630090455 9147804372994922445135683)
                  ·
                    refine ⟨13721706559492383667703525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9147804372994922445135683 13721706559492383667703525)
                    ·
                      refine ⟨2572819979904821937694411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13721706559492383667703525 2572819979904821937694411)
                      ·
                        rfl

theorem cell23_5010549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5010549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010549 prefixEnd_5010549 := by exact prefixLift 5010549
  have htrace : WordTrace (prefixWord ++ tailWord_5010549) baseStart_5010549 baseEnd_5010549 := by
    simpa [prefixWord, tailWord_5010549, baseEnd_5010549] using wordTrace_append hprefix tailTrace_5010549
  have hstable : (prefixWord ++ tailWord_5010549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010549).length < 2 ^ (prefixWord ++ tailWord_5010549).sum := by decide
  have hdescent : baseEnd_5010549 < baseStart_5010549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010571 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_5010571 : Nat := 118140960795 + 5010571 * 2 ^ 59
def prefixEnd_5010571 : Nat := 4983230072969 + 3 ^ 40 * 5010571 * 2
def baseEnd_5010571 : Nat := 2572831276479220851619309

theorem tailTrace_5010571 : CollatzResearch.WordTrace tailWord_5010571 prefixEnd_5010571 2572831276479220851619309 := by
  unfold tailWord_5010571
  simp only [CollatzResearch.WordTrace]
  refine ⟨182750537930564479243175567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121833691953709652828783711 182750537930564479243175567)
  ·
    refine ⟨274125806895846718864763351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182750537930564479243175567 274125806895846718864763351)
    ·
      refine ⟨411188710343770078297145027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274125806895846718864763351 411188710343770078297145027)
      ·
        refine ⟨616783065515655117445717541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411188710343770078297145027 616783065515655117445717541)
        ·
          refine ⟨115646824784185334521072039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 616783065515655117445717541 115646824784185334521072039)
          ·
            refine ⟨173470237176278001781608059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115646824784185334521072039 173470237176278001781608059)
            ·
              refine ⟨260205355764417002672412089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173470237176278001781608059 260205355764417002672412089)
              ·
                refine ⟨195154016823312752004309067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260205355764417002672412089 195154016823312752004309067)
                ·
                  refine ⟨292731025234969128006463601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195154016823312752004309067 292731025234969128006463601)
                  ·
                    refine ⟨219548268926226846004847701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292731025234969128006463601 219548268926226846004847701)
                    ·
                      refine ⟨2572831276479220851619309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219548268926226846004847701 2572831276479220851619309)
                      ·
                        rfl

theorem cell23_5010571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_5010571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010571 prefixEnd_5010571 := by exact prefixLift 5010571
  have htrace : WordTrace (prefixWord ++ tailWord_5010571) baseStart_5010571 baseEnd_5010571 := by
    simpa [prefixWord, tailWord_5010571, baseEnd_5010571] using wordTrace_append hprefix tailTrace_5010571
  have hstable : (prefixWord ++ tailWord_5010571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010571).length < 2 ^ (prefixWord ++ tailWord_5010571).sum := by decide
  have hdescent : baseEnd_5010571 < baseStart_5010571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010599 : List Nat := [1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5010599 : Nat := 118140960795 + 5010599 * 2 ^ 59
def prefixEnd_5010599 : Nat := 4983230072969 + 3 ^ 40 * 5010599 * 2
def baseEnd_5010599 : Nat := 2572845653937546742069181

theorem tailTrace_5010599 : CollatzResearch.WordTrace tailWord_5010599 prefixEnd_5010599 2572845653937546742069181 := by
  unfold tailWord_5010599
  simp only [CollatzResearch.WordTrace]
  refine ⟨182751559174463040025194851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121834372782975360016796567 182751559174463040025194851)
  ·
    refine ⟨274127338761694560037792277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182751559174463040025194851 274127338761694560037792277)
    ·
      refine ⟨12849719004454432501771513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 274127338761694560037792277 12849719004454432501771513)
      ·
        refine ⟨9637289253340824376328635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12849719004454432501771513 9637289253340824376328635)
        ·
          refine ⟨14455933880011236564492953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637289253340824376328635 14455933880011236564492953)
          ·
            refine ⟨10841950410008427423369715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14455933880011236564492953 10841950410008427423369715)
            ·
              refine ⟨16262925615012641135054573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841950410008427423369715 16262925615012641135054573)
              ·
                refine ⟨6098597105629740425645465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16262925615012641135054573 6098597105629740425645465)
                ·
                  refine ⟨4573947829222305319234099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6098597105629740425645465 4573947829222305319234099)
                  ·
                    refine ⟨6860921743833457978851149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573947829222305319234099 6860921743833457978851149)
                    ·
                      refine ⟨2572845653937546742069181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860921743833457978851149 2572845653937546742069181)
                      ·
                        rfl

theorem cell23_5010599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5010599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010599 prefixEnd_5010599 := by exact prefixLift 5010599
  have htrace : WordTrace (prefixWord ++ tailWord_5010599) baseStart_5010599 baseEnd_5010599 := by
    simpa [prefixWord, tailWord_5010599, baseEnd_5010599] using wordTrace_append hprefix tailTrace_5010599
  have hstable : (prefixWord ++ tailWord_5010599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010599).length < 2 ^ (prefixWord ++ tailWord_5010599).sum := by decide
  have hdescent : baseEnd_5010599 < baseStart_5010599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010608 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_5010608 : Nat := 118140960795 + 5010608 * 2 ^ 59
def prefixEnd_5010608 : Nat := 4983230072969 + 3 ^ 40 * 5010608 * 2
def baseEnd_5010608 : Nat := 2572850275263437206856639

theorem tailTrace_5010608 : CollatzResearch.WordTrace tailWord_5010608 prefixEnd_5010608 2572850275263437206856639 := by
  unfold tailWord_5010608
  simp only [CollatzResearch.WordTrace]
  refine ⟨91375943715715217281136239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121834591620953623041514985 91375943715715217281136239)
  ·
    refine ⟨137063915573572825921704359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91375943715715217281136239 137063915573572825921704359)
    ·
      refine ⟨205595873360359238882556539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137063915573572825921704359 205595873360359238882556539)
      ·
        refine ⟨308393810040538858323834809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205595873360359238882556539 308393810040538858323834809)
        ·
          refine ⟨231295357530404143742876107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308393810040538858323834809 231295357530404143742876107)
          ·
            refine ⟨346943036295606215614314161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231295357530404143742876107 346943036295606215614314161)
            ·
              refine ⟨260207277221704661710735621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346943036295606215614314161 260207277221704661710735621)
              ·
                refine ⟨48788864479069624070762929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260207277221704661710735621 48788864479069624070762929)
                ·
                  refine ⟨36591648359302218053072197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48788864479069624070762929 36591648359302218053072197)
                  ·
                    refine ⟨6860934067369165884951037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36591648359302218053072197 6860934067369165884951037)
                    ·
                      refine ⟨2572850275263437206856639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6860934067369165884951037 2572850275263437206856639)
                      ·
                        rfl

theorem cell23_5010608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_5010608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010608 prefixEnd_5010608 := by exact prefixLift 5010608
  have htrace : WordTrace (prefixWord ++ tailWord_5010608) baseStart_5010608 baseEnd_5010608 := by
    simpa [prefixWord, tailWord_5010608, baseEnd_5010608] using wordTrace_append hprefix tailTrace_5010608
  have hstable : (prefixWord ++ tailWord_5010608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010608).length < 2 ^ (prefixWord ++ tailWord_5010608).sum := by decide
  have hdescent : baseEnd_5010608 < baseStart_5010608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010609 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5010609 : Nat := 118140960795 + 5010609 * 2 ^ 59
def prefixEnd_5010609 : Nat := 4983230072969 + 3 ^ 40 * 5010609 * 2
def baseEnd_5010609 : Nat := 2572850788744091702944135

theorem tailTrace_5010609 : CollatzResearch.WordTrace tailWord_5010609 prefixEnd_5010609 2572850788744091702944135 := by
  unfold tailWord_5010609
  simp only [CollatzResearch.WordTrace]
  refine ⟨182751923904426811733058881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121834615936284541155372587 182751923904426811733058881)
  ·
    refine ⟨137063942928320108799794161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182751923904426811733058881 137063942928320108799794161)
    ·
      refine ⟨102797957196240081599845621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137063942928320108799794161 102797957196240081599845621)
      ·
        refine ⟨9637308487147507649985527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102797957196240081599845621 9637308487147507649985527)
        ·
          refine ⟨14455962730721261474978291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637308487147507649985527 14455962730721261474978291)
          ·
            refine ⟨21683944096081892212467437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14455962730721261474978291 21683944096081892212467437)
            ·
              refine ⟨8131479036030709579675289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21683944096081892212467437 8131479036030709579675289)
              ·
                refine ⟨6098609277023032184756467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8131479036030709579675289 6098609277023032184756467)
                ·
                  refine ⟨9147913915534548277134701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6098609277023032184756467 9147913915534548277134701)
                  ·
                    refine ⟨3430467718325455603925513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9147913915534548277134701 3430467718325455603925513)
                    ·
                      refine ⟨2572850788744091702944135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430467718325455603925513 2572850788744091702944135)
                      ·
                        rfl

theorem cell23_5010609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5010609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010609 prefixEnd_5010609 := by exact prefixLift 5010609
  have htrace : WordTrace (prefixWord ++ tailWord_5010609) baseStart_5010609 baseEnd_5010609 := by
    simpa [prefixWord, tailWord_5010609, baseEnd_5010609] using wordTrace_append hprefix tailTrace_5010609
  have hstable : (prefixWord ++ tailWord_5010609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010609).length < 2 ^ (prefixWord ++ tailWord_5010609).sum := by decide
  have hdescent : baseEnd_5010609 < baseStart_5010609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010618 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_5010618 : Nat := 118140960795 + 5010618 * 2 ^ 59
def prefixEnd_5010618 : Nat := 4983230072969 + 3 ^ 40 * 5010618 * 2
def baseEnd_5010618 : Nat := 2572855410069982167731593

theorem tailTrace_5010618 : CollatzResearch.WordTrace tailWord_5010618 prefixEnd_5010618 2572855410069982167731593 := by
  unfold tailWord_5010618
  simp only [CollatzResearch.WordTrace]
  refine ⟨45688063040348551567534127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121834834774262804180091005 45688063040348551567534127)
  ·
    refine ⟨68532094560522827351301191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45688063040348551567534127 68532094560522827351301191)
    ·
      refine ⟨102798141840784241026951787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68532094560522827351301191 102798141840784241026951787)
      ·
        refine ⟨154197212761176361540427681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102798141840784241026951787 154197212761176361540427681)
        ·
          refine ⟨115647909570882271155320761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154197212761176361540427681 115647909570882271155320761)
          ·
            refine ⟨86735932178161703366490571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115647909570882271155320761 86735932178161703366490571)
            ·
              refine ⟨130103898267242555049735857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86735932178161703366490571 130103898267242555049735857)
              ·
                refine ⟨97577923700431916287301893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130103898267242555049735857 97577923700431916287301893)
                ·
                  refine ⟨18295860693830984303869105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97577923700431916287301893 18295860693830984303869105)
                  ·
                    refine ⟨13721895520373238227901829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18295860693830984303869105 13721895520373238227901829)
                    ·
                      refine ⟨2572855410069982167731593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13721895520373238227901829 2572855410069982167731593)
                      ·
                        rfl

theorem cell23_5010618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_5010618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010618 prefixEnd_5010618 := by exact prefixLift 5010618
  have htrace : WordTrace (prefixWord ++ tailWord_5010618) baseStart_5010618 baseEnd_5010618 := by
    simpa [prefixWord, tailWord_5010618, baseEnd_5010618] using wordTrace_append hprefix tailTrace_5010618
  have hstable : (prefixWord ++ tailWord_5010618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010618).length < 2 ^ (prefixWord ++ tailWord_5010618).sum := by decide
  have hdescent : baseEnd_5010618 < baseStart_5010618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010622 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_5010622 : Nat := 118140960795 + 5010622 * 2 ^ 59
def prefixEnd_5010622 : Nat := 4983230072969 + 3 ^ 40 * 5010622 * 2
def baseEnd_5010622 : Nat := 2572857463992600152081575

theorem tailTrace_5010622 : CollatzResearch.WordTrace tailWord_5010622 prefixEnd_5010622 2572857463992600152081575 := by
  unfold tailWord_5010622
  simp only [CollatzResearch.WordTrace]
  refine ⟨22844049756672464369160265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121834932035586476635521413 22844049756672464369160265)
  ·
    refine ⟨17133037317504348276870199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22844049756672464369160265 17133037317504348276870199)
    ·
      refine ⟨25699555976256522415305299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17133037317504348276870199 25699555976256522415305299)
      ·
        refine ⟨38549333964384783622957949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25699555976256522415305299 38549333964384783622957949)
        ·
          refine ⟨14456000236644293858609231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38549333964384783622957949 14456000236644293858609231)
          ·
            refine ⟨21684000354966440787913847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14456000236644293858609231 21684000354966440787913847)
            ·
              refine ⟨32526000532449661181870771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21684000354966440787913847 32526000532449661181870771)
              ·
                refine ⟨48789000798674491772806157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32526000532449661181870771 48789000798674491772806157)
                ·
                  refine ⟨18295875299502934414802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48789000798674491772806157 18295875299502934414802309)
                  ·
                    refine ⟨3430476618656800202775433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18295875299502934414802309 3430476618656800202775433)
                    ·
                      refine ⟨2572857463992600152081575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430476618656800202775433 2572857463992600152081575)
                      ·
                        rfl

theorem cell23_5010622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_5010622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010622 prefixEnd_5010622 := by exact prefixLift 5010622
  have htrace : WordTrace (prefixWord ++ tailWord_5010622) baseStart_5010622 baseEnd_5010622 := by
    simpa [prefixWord, tailWord_5010622, baseEnd_5010622] using wordTrace_append hprefix tailTrace_5010622
  have hstable : (prefixWord ++ tailWord_5010622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010622).length < 2 ^ (prefixWord ++ tailWord_5010622).sum := by decide
  have hdescent : baseEnd_5010622 < baseStart_5010622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010675 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 2, 5]
def baseStart_5010675 : Nat := 118140960795 + 5010675 * 2 ^ 59
def prefixEnd_5010675 : Nat := 4983230072969 + 3 ^ 40 * 5010675 * 2
def baseEnd_5010675 : Nat := 857628226155762814906277

theorem tailTrace_5010675 : CollatzResearch.WordTrace tailWord_5010675 prefixEnd_5010675 857628226155762814906277 := by
  unfold tailWord_5010675
  simp only [CollatzResearch.WordTrace]
  refine ⟨182754331122187705004961479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121836220748125136669974319 182754331122187705004961479)
  ·
    refine ⟨274131496683281557507442219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182754331122187705004961479 274131496683281557507442219)
    ·
      refine ⟨411197245024922336261163329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274131496683281557507442219 411197245024922336261163329)
      ·
        refine ⟨308397933768691752195872497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411197245024922336261163329 308397933768691752195872497)
        ·
          refine ⟨231298450326518814146904373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308397933768691752195872497 231298450326518814146904373)
          ·
            refine ⟨21684229718111138826272285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231298450326518814146904373 21684229718111138826272285)
            ·
              refine ⟨8131586144291677059852107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21684229718111138826272285 8131586144291677059852107)
              ·
                refine ⟨12197379216437515589778161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8131586144291677059852107 12197379216437515589778161)
                ·
                  refine ⟨9148034412328136692333621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12197379216437515589778161 9148034412328136692333621)
                  ·
                    refine ⟨857628226155762814906277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9148034412328136692333621 857628226155762814906277)
                    ·
                      rfl

theorem cell23_5010675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 5].length) (baseStart_5010675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010675 prefixEnd_5010675 := by exact prefixLift 5010675
  have htrace : WordTrace (prefixWord ++ tailWord_5010675) baseStart_5010675 baseEnd_5010675 := by
    simpa [prefixWord, tailWord_5010675, baseEnd_5010675] using wordTrace_append hprefix tailTrace_5010675
  have hstable : (prefixWord ++ tailWord_5010675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010675).length < 2 ^ (prefixWord ++ tailWord_5010675).sum := by decide
  have hdescent : baseEnd_5010675 < baseStart_5010675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010690 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_5010690 : Nat := 118140960795 + 5010690 * 2 ^ 59
def prefixEnd_5010690 : Nat := 4983230072969 + 3 ^ 40 * 5010690 * 2
def baseEnd_5010690 : Nat := 2572892380677105886031263

theorem tailTrace_5010690 : CollatzResearch.WordTrace tailWord_5010690 prefixEnd_5010690 2572892380677105886031263 := by
  unfold tailWord_5010690
  simp only [CollatzResearch.WordTrace]
  refine ⟨45688719554283340641689381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121836585478088908377838349 45688719554283340641689381)
  ·
    refine ⟨8566634916428126370316759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45688719554283340641689381 8566634916428126370316759)
    ·
      refine ⟨12849952374642189555475139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566634916428126370316759 12849952374642189555475139)
      ·
        refine ⟨19274928561963284333212709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849952374642189555475139 19274928561963284333212709)
        ·
          refine ⟨3614049105368115812477383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19274928561963284333212709 3614049105368115812477383)
          ·
            refine ⟨5421073658052173718716075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614049105368115812477383 5421073658052173718716075)
            ·
              refine ⟨8131610487078260578074113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421073658052173718716075 8131610487078260578074113)
              ·
                refine ⟨6098707865308695433555585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8131610487078260578074113 6098707865308695433555585)
                ·
                  refine ⟨4574030898981521575166689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6098707865308695433555585 4574030898981521575166689)
                  ·
                    refine ⟨3430523174236141181375017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4574030898981521575166689 3430523174236141181375017)
                    ·
                      refine ⟨2572892380677105886031263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430523174236141181375017 2572892380677105886031263)
                      ·
                        rfl

theorem cell23_5010690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_5010690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010690 prefixEnd_5010690 := by exact prefixLift 5010690
  have htrace : WordTrace (prefixWord ++ tailWord_5010690) baseStart_5010690 baseEnd_5010690 := by
    simpa [prefixWord, tailWord_5010690, baseEnd_5010690] using wordTrace_append hprefix tailTrace_5010690
  have hstable : (prefixWord ++ tailWord_5010690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010690).length < 2 ^ (prefixWord ++ tailWord_5010690).sum := by decide
  have hdescent : baseEnd_5010690 < baseStart_5010690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010712 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5010712 : Nat := 118140960795 + 5010712 * 2 ^ 59
def prefixEnd_5010712 : Nat := 4983230072969 + 3 ^ 40 * 5010712 * 2
def baseEnd_5010712 : Nat := 2572903677251504799956161

theorem tailTrace_5010712 : CollatzResearch.WordTrace tailWord_5010712 prefixEnd_5010712 2572903677251504799956161 := by
  unfold tailWord_5010712
  simp only [CollatzResearch.WordTrace]
  refine ⟨91377840311526830162029195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121837120415369106882705593 91377840311526830162029195)
  ·
    refine ⟨137066760467290245243043793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91377840311526830162029195 137066760467290245243043793)
    ·
      refine ⟨102800070350467683932282845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137066760467290245243043793 102800070350467683932282845)
      ·
        refine ⟨38550026381425381474606067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102800070350467683932282845 38550026381425381474606067)
        ·
          refine ⟨57825039572138072211909101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38550026381425381474606067 57825039572138072211909101)
          ·
            refine ⟨21684389839551777079465913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57825039572138072211909101 21684389839551777079465913)
            ·
              refine ⟨16263292379663832809599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21684389839551777079465913 16263292379663832809599435)
              ·
                refine ⟨24394938569495749214399153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16263292379663832809599435 24394938569495749214399153)
                ·
                  refine ⟨18296203927121811910799365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24394938569495749214399153 18296203927121811910799365)
                  ·
                    refine ⟨3430538236335339733274881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18296203927121811910799365 3430538236335339733274881)
                    ·
                      refine ⟨2572903677251504799956161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430538236335339733274881 2572903677251504799956161)
                      ·
                        rfl

theorem cell23_5010712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5010712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010712 prefixEnd_5010712 := by exact prefixLift 5010712
  have htrace : WordTrace (prefixWord ++ tailWord_5010712) baseStart_5010712 baseEnd_5010712 := by
    simpa [prefixWord, tailWord_5010712, baseEnd_5010712] using wordTrace_append hprefix tailTrace_5010712
  have hstable : (prefixWord ++ tailWord_5010712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010712).length < 2 ^ (prefixWord ++ tailWord_5010712).sum := by decide
  have hdescent : baseEnd_5010712 < baseStart_5010712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010739 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 1, 4]
def baseStart_5010739 : Nat := 118140960795 + 5010739 * 2 ^ 59
def prefixEnd_5010739 : Nat := 4983230072969 + 3 ^ 40 * 5010739 * 2
def baseEnd_5010739 : Nat := 857639180409725398106179

theorem tailTrace_5010739 : CollatzResearch.WordTrace tailWord_5010739 prefixEnd_5010739 857639180409725398106179 := by
  unfold tailWord_5010739
  simp only [CollatzResearch.WordTrace]
  refine ⟨182756665393955843935291271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121837776929303895956860847 182756665393955843935291271)
  ·
    refine ⟨274134998090933765902936907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182756665393955843935291271 274134998090933765902936907)
    ·
      refine ⟨411202497136400648854405361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274134998090933765902936907 411202497136400648854405361)
      ·
        refine ⟨308401872852300486640804021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411202497136400648854405361 308401872852300486640804021)
        ·
          refine ⟨28912675579903170622575377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308401872852300486640804021 28912675579903170622575377)
          ·
            refine ⟨21684506684927377966931533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28912675579903170622575377 21684506684927377966931533)
            ·
              refine ⟨8131690006847766737599325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21684506684927377966931533 8131690006847766737599325)
              ·
                refine ⟨3049383752567912526599747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8131690006847766737599325 3049383752567912526599747)
                ·
                  refine ⟨4574075628851868789899621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049383752567912526599747 4574075628851868789899621)
                  ·
                    refine ⟨857639180409725398106179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4574075628851868789899621 857639180409725398106179)
                    ·
                      rfl

theorem cell23_5010739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 4].length) (baseStart_5010739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010739 prefixEnd_5010739 := by exact prefixLift 5010739
  have htrace : WordTrace (prefixWord ++ tailWord_5010739) baseStart_5010739 baseEnd_5010739 := by
    simpa [prefixWord, tailWord_5010739, baseEnd_5010739] using wordTrace_append hprefix tailTrace_5010739
  have hstable : (prefixWord ++ tailWord_5010739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010739).length < 2 ^ (prefixWord ++ tailWord_5010739).sum := by decide
  have hdescent : baseEnd_5010739 < baseStart_5010739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010756 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5010756 : Nat := 118140960795 + 5010756 * 2 ^ 59
def prefixEnd_5010756 : Nat := 4983230072969 + 3 ^ 40 * 5010756 * 2
def baseEnd_5010756 : Nat := 857642090133434209268653

theorem tailTrace_5010756 : CollatzResearch.WordTrace tailWord_5010756 prefixEnd_5010756 857642090133434209268653 := by
  unfold tailWord_5010756
  simp only [CollatzResearch.WordTrace]
  refine ⟨91378642717447127919330061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121838190289929503892440081 91378642717447127919330061)
  ·
    refine ⟨34266991019042672969748773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91378642717447127919330061 34266991019042672969748773)
    ·
      refine ⟨6425060816070501181827895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34266991019042672969748773 6425060816070501181827895)
      ·
        refine ⟨9637591224105751772741843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6425060816070501181827895 9637591224105751772741843)
        ·
          refine ⟨14456386836158627659112765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637591224105751772741843 14456386836158627659112765)
          ·
            refine ⟨5421145063559485372167287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14456386836158627659112765 5421145063559485372167287)
            ·
              refine ⟨8131717595339228058250931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421145063559485372167287 8131717595339228058250931)
              ·
                refine ⟨12197576393008842087376397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8131717595339228058250931 12197576393008842087376397)
                ·
                  refine ⟨4574091147378315782766149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12197576393008842087376397 4574091147378315782766149)
                  ·
                    refine ⟨857642090133434209268653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4574091147378315782766149 857642090133434209268653)
                    ·
                      rfl

theorem cell23_5010756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5010756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010756 prefixEnd_5010756 := by exact prefixLift 5010756
  have htrace : WordTrace (prefixWord ++ tailWord_5010756) baseStart_5010756 baseEnd_5010756 := by
    simpa [prefixWord, tailWord_5010756, baseEnd_5010756] using wordTrace_append hprefix tailTrace_5010756
  have hstable : (prefixWord ++ tailWord_5010756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010756).length < 2 ^ (prefixWord ++ tailWord_5010756).sum := by decide
  have hdescent : baseEnd_5010756 < baseStart_5010756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010789 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_5010789 : Nat := 118140960795 + 5010789 * 2 ^ 59
def prefixEnd_5010789 : Nat := 4983230072969 + 3 ^ 40 * 5010789 * 2
def baseEnd_5010789 : Nat := 2572943215261900998693307

theorem tailTrace_5010789 : CollatzResearch.WordTrace tailWord_5010789 prefixEnd_5010789 2572943215261900998693307 := by
  unfold tailWord_5010789
  simp only [CollatzResearch.WordTrace]
  refine ⟨182758489043774702474611421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121838992695849801649740947 182758489043774702474611421)
  ·
    refine ⟨68534433391415513427979283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182758489043774702474611421 68534433391415513427979283)
    ·
      refine ⟨102801650087123270141968925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68534433391415513427979283 102801650087123270141968925)
      ·
        refine ⟨38550618782671226303238347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102801650087123270141968925 38550618782671226303238347)
        ·
          refine ⟨57825928174006839454857521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38550618782671226303238347 57825928174006839454857521)
          ·
            refine ⟨43369446130505129591143141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57825928174006839454857521 43369446130505129591143141)
            ·
              refine ⟨8131771149469711798339339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43369446130505129591143141 8131771149469711798339339)
              ·
                refine ⟨12197656724204567697509009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8131771149469711798339339 12197656724204567697509009)
                ·
                  refine ⟨9148242543153425773131757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12197656724204567697509009 9148242543153425773131757)
                  ·
                    refine ⟨3430590953682534664924409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9148242543153425773131757 3430590953682534664924409)
                    ·
                      refine ⟨2572943215261900998693307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430590953682534664924409 2572943215261900998693307)
                      ·
                        rfl

theorem cell23_5010789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_5010789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010789 prefixEnd_5010789 := by exact prefixLift 5010789
  have htrace : WordTrace (prefixWord ++ tailWord_5010789) baseStart_5010789 baseEnd_5010789 := by
    simpa [prefixWord, tailWord_5010789, baseEnd_5010789] using wordTrace_append hprefix tailTrace_5010789
  have hstable : (prefixWord ++ tailWord_5010789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010789).length < 2 ^ (prefixWord ++ tailWord_5010789).sum := by decide
  have hdescent : baseEnd_5010789 < baseStart_5010789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010836 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5010836 : Nat := 118140960795 + 5010836 * 2 ^ 59
def prefixEnd_5010836 : Nat := 4983230072969 + 3 ^ 40 * 5010836 * 2
def baseEnd_5010836 : Nat := 2572967348852662314805591

theorem tailTrace_5010836 : CollatzResearch.WordTrace tailWord_5010836 prefixEnd_5010836 2572967348852662314805591 := by
  unfold tailWord_5010836
  simp only [CollatzResearch.WordTrace]
  refine ⟨91380101637302214750786181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121840135516402953001048241 91380101637302214750786181)
  ·
    refine ⟨17133769056994165265772409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91380101637302214750786181 17133769056994165265772409)
    ·
      refine ⟨12850326792745623949329307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17133769056994165265772409 12850326792745623949329307)
      ·
        refine ⟨19275490189118435923993961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12850326792745623949329307 19275490189118435923993961)
        ·
          refine ⟨14456617641838826942995471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19275490189118435923993961 14456617641838826942995471)
          ·
            refine ⟨21684926462758240414493207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14456617641838826942995471 21684926462758240414493207)
            ·
              refine ⟨32527389694137360621739811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21684926462758240414493207 32527389694137360621739811)
              ·
                refine ⟨48791084541206040932609717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32527389694137360621739811 48791084541206040932609717)
                ·
                  refine ⟨4574164175738066337432161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48791084541206040932609717 4574164175738066337432161)
                  ·
                    refine ⟨3430623131803549753074121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4574164175738066337432161 3430623131803549753074121)
                    ·
                      refine ⟨2572967348852662314805591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430623131803549753074121 2572967348852662314805591)
                      ·
                        rfl

theorem cell23_5010836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5010836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010836 prefixEnd_5010836 := by exact prefixLift 5010836
  have htrace : WordTrace (prefixWord ++ tailWord_5010836) baseStart_5010836 baseEnd_5010836 := by
    simpa [prefixWord, tailWord_5010836, baseEnd_5010836] using wordTrace_append hprefix tailTrace_5010836
  have hstable : (prefixWord ++ tailWord_5010836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010836).length < 2 ^ (prefixWord ++ tailWord_5010836).sum := by decide
  have hdescent : baseEnd_5010836 < baseStart_5010836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010842 : List Nat := [3, 1, 1, 4, 1, 1, 5, 7]
def baseStart_5010842 : Nat := 118140960795 + 5010842 * 2 ^ 59
def prefixEnd_5010842 : Nat := 4983230072969 + 3 ^ 40 * 5010842 * 2
def baseEnd_5010842 : Nat := 95295201101355158938169

theorem tailTrace_5010842 : CollatzResearch.WordTrace tailWord_5010842 prefixEnd_5010842 95295201101355158938169 := by
  unfold tailWord_5010842
  simp only [CollatzResearch.WordTrace]
  refine ⟨45690105528145673131572695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121840281408388461684193853 45690105528145673131572695)
  ·
    refine ⟨68535158292218509697359043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45690105528145673131572695 68535158292218509697359043)
    ·
      refine ⟨102802737438327764546038565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68535158292218509697359043 102802737438327764546038565)
      ·
        refine ⟨19275513269686455852382231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102802737438327764546038565 19275513269686455852382231)
        ·
          refine ⟨28913269904529683778573347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19275513269686455852382231 28913269904529683778573347)
          ·
            refine ⟨43369904856794525667860021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28913269904529683778573347 43369904856794525667860021)
            ·
              refine ⟨4065928580324486781361877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43369904856794525667860021 4065928580324486781361877)
              ·
                refine ⟨95295201101355158938169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4065928580324486781361877 95295201101355158938169)
                ·
                  rfl

theorem cell23_5010842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_5010842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010842 prefixEnd_5010842 := by exact prefixLift 5010842
  have htrace : WordTrace (prefixWord ++ tailWord_5010842) baseStart_5010842 baseEnd_5010842 := by
    simpa [prefixWord, tailWord_5010842, baseEnd_5010842] using wordTrace_append hprefix tailTrace_5010842
  have hstable : (prefixWord ++ tailWord_5010842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010842).length < 2 ^ (prefixWord ++ tailWord_5010842).sum := by decide
  have hdescent : baseEnd_5010842 < baseStart_5010842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010926 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_5010926 : Nat := 118140960795 + 5010926 * 2 ^ 59
def prefixEnd_5010926 : Nat := 4983230072969 + 3 ^ 40 * 5010926 * 2
def baseEnd_5010926 : Nat := 2573013562111566962680177

theorem tailTrace_5010926 : CollatzResearch.WordTrace tailWord_5010926 prefixEnd_5010926 2573013562111566962680177 := by
  unfold tailWord_5010926
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845435730534796859043579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121842323896185583248232421 22845435730534796859043579)
  ·
    refine ⟨34268153595802195288565369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22845435730534796859043579 34268153595802195288565369)
    ·
      refine ⟨25701115196851646466424027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34268153595802195288565369 25701115196851646466424027)
      ·
        refine ⟨38551672795277469699636041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25701115196851646466424027 38551672795277469699636041)
        ·
          refine ⟨28913754596458102274727031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38551672795277469699636041 28913754596458102274727031)
          ·
            refine ⟨43370631894687153412090547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28913754596458102274727031 43370631894687153412090547)
            ·
              refine ⟨65055947842030730118135821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43370631894687153412090547 65055947842030730118135821)
              ·
                refine ⟨24395980440761523794300933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65055947842030730118135821 24395980440761523794300933)
                ·
                  refine ⟨4574246332642785711431425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24395980440761523794300933 4574246332642785711431425)
                  ·
                    refine ⟨3430684749482089283573569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4574246332642785711431425 3430684749482089283573569)
                    ·
                      refine ⟨2573013562111566962680177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430684749482089283573569 2573013562111566962680177)
                      ·
                        rfl

theorem cell23_5010926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_5010926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010926 prefixEnd_5010926 := by exact prefixLift 5010926
  have htrace : WordTrace (prefixWord ++ tailWord_5010926) baseStart_5010926 baseEnd_5010926 := by
    simpa [prefixWord, tailWord_5010926, baseEnd_5010926] using wordTrace_append hprefix tailTrace_5010926
  have hstable : (prefixWord ++ tailWord_5010926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010926).length < 2 ^ (prefixWord ++ tailWord_5010926).sum := by decide
  have hdescent : baseEnd_5010926 < baseStart_5010926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010935 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_5010935 : Nat := 118140960795 + 5010935 * 2 ^ 59
def prefixEnd_5010935 : Nat := 4983230072969 + 3 ^ 40 * 5010935 * 2
def baseEnd_5010935 : Nat := 2573018183437457427467635

theorem tailTrace_5010935 : CollatzResearch.WordTrace tailWord_5010935 prefixEnd_5010935 2573018183437457427467635 := by
  unfold tailWord_5010935
  simp only [CollatzResearch.WordTrace]
  refine ⟨182763814101245769409426259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121842542734163846272950839 182763814101245769409426259)
  ·
    refine ⟨274145721151868654114139389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182763814101245769409426259 274145721151868654114139389)
    ·
      refine ⟨102804645431950745292802271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274145721151868654114139389 102804645431950745292802271)
      ·
        refine ⟨154206968147926117939203407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102804645431950745292802271 154206968147926117939203407)
        ·
          refine ⟨231310452221889176908805111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154206968147926117939203407 231310452221889176908805111)
          ·
            refine ⟨346965678332833765363207667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231310452221889176908805111 346965678332833765363207667)
            ·
              refine ⟨520448517499250648044811501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346965678332833765363207667 520448517499250648044811501)
              ·
                refine ⟨195168194062218993016804313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520448517499250648044811501 195168194062218993016804313)
                ·
                  refine ⟨146376145546664244762603235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195168194062218993016804313 146376145546664244762603235)
                  ·
                    refine ⟨219564218319996367143904853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146376145546664244762603235 219564218319996367143904853)
                    ·
                      refine ⟨2573018183437457427467635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219564218319996367143904853 2573018183437457427467635)
                      ·
                        rfl

theorem cell23_5010935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_5010935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010935 prefixEnd_5010935 := by exact prefixLift 5010935
  have htrace : WordTrace (prefixWord ++ tailWord_5010935) baseStart_5010935 baseEnd_5010935 := by
    simpa [prefixWord, tailWord_5010935, baseEnd_5010935] using wordTrace_append hprefix tailTrace_5010935
  have hstable : (prefixWord ++ tailWord_5010935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010935).length < 2 ^ (prefixWord ++ tailWord_5010935).sum := by decide
  have hdescent : baseEnd_5010935 < baseStart_5010935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010972 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5010972 : Nat := 118140960795 + 5010972 * 2 ^ 59
def prefixEnd_5010972 : Nat := 4983230072969 + 3 ^ 40 * 5010972 * 2
def baseEnd_5010972 : Nat := 2573037182221673782704965

theorem tailTrace_5010972 : CollatzResearch.WordTrace tailWord_5010972 prefixEnd_5010972 2573037182221673782704965 := by
  unfold tailWord_5010972
  simp only [CollatzResearch.WordTrace]
  refine ⟨91382581801055862364261585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121843442401407816485682113 91382581801055862364261585)
  ·
    refine ⟨68536936350791896773196189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91382581801055862364261585 68536936350791896773196189)
    ·
      refine ⟨25701351131546961289948571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68536936350791896773196189 25701351131546961289948571)
      ·
        refine ⟨38552026697320441934922857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25701351131546961289948571 38552026697320441934922857)
        ·
          refine ⟨28914020022990331451192143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38552026697320441934922857 28914020022990331451192143)
          ·
            refine ⟨43371030034485497176788215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28914020022990331451192143 43371030034485497176788215)
            ·
              refine ⟨65056545051728245765182323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43371030034485497176788215 65056545051728245765182323)
              ·
                refine ⟨97584817577592368647773485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65056545051728245765182323 97584817577592368647773485)
                ·
                  refine ⟨36594306591597138242915057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97584817577592368647773485 36594306591597138242915057)
                  ·
                    refine ⟨27445729943697853682186293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36594306591597138242915057 27445729943697853682186293)
                    ·
                      refine ⟨2573037182221673782704965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27445729943697853682186293 2573037182221673782704965)
                      ·
                        rfl

theorem cell23_5010972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5010972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010972 prefixEnd_5010972 := by exact prefixLift 5010972
  have htrace : WordTrace (prefixWord ++ tailWord_5010972) baseStart_5010972 baseEnd_5010972 := by
    simpa [prefixWord, tailWord_5010972, baseEnd_5010972] using wordTrace_append hprefix tailTrace_5010972
  have hstable : (prefixWord ++ tailWord_5010972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010972).length < 2 ^ (prefixWord ++ tailWord_5010972).sum := by decide
  have hdescent : baseEnd_5010972 < baseStart_5010972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5010999 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_5010999 : Nat := 118140960795 + 5010999 * 2 ^ 59
def prefixEnd_5010999 : Nat := 4983230072969 + 3 ^ 40 * 5010999 * 2
def baseEnd_5010999 : Nat := 2573051046199345177067341

theorem tailTrace_5010999 : CollatzResearch.WordTrace tailWord_5010999 prefixEnd_5010999 2573051046199345177067341 := by
  unfold tailWord_5010999
  simp only [CollatzResearch.WordTrace]
  refine ⟨182766148373013908339756051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121844098915342605559837367 182766148373013908339756051)
  ·
    refine ⟨274149222559520862509634077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182766148373013908339756051 274149222559520862509634077)
    ·
      refine ⟨102805958459820323441112779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274149222559520862509634077 102805958459820323441112779)
      ·
        refine ⟨154208937689730485161669169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102805958459820323441112779 154208937689730485161669169)
        ·
          refine ⟨115656703267297863871251877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154208937689730485161669169 115656703267297863871251877)
          ·
            refine ⟨21685631862618349475859727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115656703267297863871251877 21685631862618349475859727)
            ·
              refine ⟨32528447793927524213789591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21685631862618349475859727 32528447793927524213789591)
              ·
                refine ⟨48792671690891286320684387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32528447793927524213789591 48792671690891286320684387)
                ·
                  refine ⟨73189007536336929481026581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48792671690891286320684387 73189007536336929481026581)
                  ·
                    refine ⟨3430734728265793569423121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73189007536336929481026581 3430734728265793569423121)
                    ·
                      refine ⟨2573051046199345177067341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430734728265793569423121 2573051046199345177067341)
                      ·
                        rfl

theorem cell23_5010999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_5010999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5010999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5010999 prefixEnd_5010999 := by exact prefixLift 5010999
  have htrace : WordTrace (prefixWord ++ tailWord_5010999) baseStart_5010999 baseEnd_5010999 := by
    simpa [prefixWord, tailWord_5010999, baseEnd_5010999] using wordTrace_append hprefix tailTrace_5010999
  have hstable : (prefixWord ++ tailWord_5010999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5010999).length < 2 ^ (prefixWord ++ tailWord_5010999).sum := by decide
  have hdescent : baseEnd_5010999 < baseStart_5010999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5010999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011022 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_5011022 : Nat := 118140960795 + 5011022 * 2 ^ 59
def prefixEnd_5011022 : Nat := 4983230072969 + 3 ^ 40 * 5011022 * 2
def baseEnd_5011022 : Nat := 285895872917155398564415

theorem tailTrace_5011022 : CollatzResearch.WordTrace tailWord_5011022 prefixEnd_5011022 285895872917155398564415 := by
  unfold tailWord_5011022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845873406491322908480415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121844658167953722178562213 22845873406491322908480415)
  ·
    refine ⟨34268810109736984362720623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22845873406491322908480415 34268810109736984362720623)
    ·
      refine ⟨51403215164605476544080935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34268810109736984362720623 51403215164605476544080935)
      ·
        refine ⟨77104822746908214816121403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51403215164605476544080935 77104822746908214816121403)
        ·
          refine ⟨115657234120362322224182105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77104822746908214816121403 115657234120362322224182105)
          ·
            refine ⟨86742925590271741668136579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115657234120362322224182105 86742925590271741668136579)
            ·
              refine ⟨130114388385407612502204869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86742925590271741668136579 130114388385407612502204869)
              ·
                refine ⟨24396447822263927344163413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130114388385407612502204869 24396447822263927344163413)
                ·
                  refine ⟨285895872917155398564415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24396447822263927344163413 285895872917155398564415)
                  ·
                    rfl

theorem cell23_5011022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_5011022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011022 prefixEnd_5011022 := by exact prefixLift 5011022
  have htrace : WordTrace (prefixWord ++ tailWord_5011022) baseStart_5011022 baseEnd_5011022 := by
    simpa [prefixWord, tailWord_5011022, baseEnd_5011022] using wordTrace_append hprefix tailTrace_5011022
  have hstable : (prefixWord ++ tailWord_5011022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011022).length < 2 ^ (prefixWord ++ tailWord_5011022).sum := by decide
  have hdescent : baseEnd_5011022 < baseStart_5011022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011056 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 6]
def baseStart_5011056 : Nat := 118140960795 + 5011056 * 2 ^ 59
def prefixEnd_5011056 : Nat := 4983230072969 + 3 ^ 40 * 5011056 * 2
def baseEnd_5011056 : Nat := 285897812732961272672731

theorem tailTrace_5011056 : CollatzResearch.WordTrace tailWord_5011056 prefixEnd_5011056 285897812732961272672731 := by
  unfold tailWord_5011056
  simp only [CollatzResearch.WordTrace]
  refine ⟨91384113666903703537290511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121845484889204938049720681 91384113666903703537290511)
  ·
    refine ⟨137076170500355555305935767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91384113666903703537290511 137076170500355555305935767)
    ·
      refine ⟨205614255750533332958903651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137076170500355555305935767 205614255750533332958903651)
      ·
        refine ⟨308421383625799999438355477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205614255750533332958903651 308421383625799999438355477)
        ·
          refine ⟨14457252357459374973672913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 308421383625799999438355477 14457252357459374973672913)
          ·
            refine ⟨10842939268094531230254685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14457252357459374973672913 10842939268094531230254685)
            ·
              refine ⟨4066102225535449211345507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10842939268094531230254685 4066102225535449211345507)
              ·
                refine ⟨6099153338303173817018261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066102225535449211345507 6099153338303173817018261)
                ·
                  refine ⟨285897812732961272672731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6099153338303173817018261 285897812732961272672731)
                  ·
                    rfl

theorem cell23_5011056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 6].length) (baseStart_5011056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011056 prefixEnd_5011056 := by exact prefixLift 5011056
  have htrace : WordTrace (prefixWord ++ tailWord_5011056) baseStart_5011056 baseEnd_5011056 := by
    simpa [prefixWord, tailWord_5011056, baseEnd_5011056] using wordTrace_append hprefix tailTrace_5011056
  have hstable : (prefixWord ++ tailWord_5011056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011056).length < 2 ^ (prefixWord ++ tailWord_5011056).sum := by decide
  have hdescent : baseEnd_5011056 < baseStart_5011056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011086 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_5011086 : Nat := 118140960795 + 5011086 * 2 ^ 59
def prefixEnd_5011086 : Nat := 4983230072969 + 3 ^ 40 * 5011086 * 2
def baseEnd_5011086 : Nat := 857698573005428778893147

theorem tailTrace_5011086 : CollatzResearch.WordTrace tailWord_5011086 prefixEnd_5011086 857698573005428778893147 := by
  unfold tailWord_5011086
  simp only [CollatzResearch.WordTrace]
  refine ⟨22846165190462340274771639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121846214349132481465448741 22846165190462340274771639)
  ·
    refine ⟨34269247785693510412157459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22846165190462340274771639 34269247785693510412157459)
    ·
      refine ⟨51403871678540265618236189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34269247785693510412157459 51403871678540265618236189)
      ·
        refine ⟨19276451879452599606838571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51403871678540265618236189 19276451879452599606838571)
        ·
          refine ⟨28914677819178899410257857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19276451879452599606838571 28914677819178899410257857)
          ·
            refine ⟨21686008364384174557693393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28914677819178899410257857 21686008364384174557693393)
            ·
              refine ⟨16264506273288130918270045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21686008364384174557693393 16264506273288130918270045)
              ·
                refine ⟨6099189852483049094351267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16264506273288130918270045 6099189852483049094351267)
                ·
                  refine ⟨9148784778724573641526901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6099189852483049094351267 9148784778724573641526901)
                  ·
                    refine ⟨857698573005428778893147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9148784778724573641526901 857698573005428778893147)
                    ·
                      rfl

theorem cell23_5011086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_5011086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011086 prefixEnd_5011086 := by exact prefixLift 5011086
  have htrace : WordTrace (prefixWord ++ tailWord_5011086) baseStart_5011086 baseEnd_5011086 := by
    simpa [prefixWord, tailWord_5011086, baseEnd_5011086] using wordTrace_append hprefix tailTrace_5011086
  have hstable : (prefixWord ++ tailWord_5011086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011086).length < 2 ^ (prefixWord ++ tailWord_5011086).sum := by decide
  have hdescent : baseEnd_5011086 < baseStart_5011086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011100 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5011100 : Nat := 118140960795 + 5011100 * 2 ^ 59
def prefixEnd_5011100 : Nat := 4983230072969 + 3 ^ 40 * 5011100 * 2
def baseEnd_5011100 : Nat := 2573102907745449281904377

theorem tailTrace_5011100 : CollatzResearch.WordTrace tailWord_5011100 prefixEnd_5011100 2573102907745449281904377 := by
  unfold tailWord_5011100
  simp only [CollatzResearch.WordTrace]
  refine ⟨91384916072824001294591377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121846554763765335059455169 91384916072824001294591377)
  ·
    refine ⟨68538687054618000970943533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91384916072824001294591377 68538687054618000970943533)
    ·
      refine ⟨25702007645481750364103825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68538687054618000970943533 25702007645481750364103825)
      ·
        refine ⟨19276505734111312773077869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25702007645481750364103825 19276505734111312773077869)
        ·
          refine ⟨7228689650291742289904201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19276505734111312773077869 7228689650291742289904201)
          ·
            refine ⟨5421517237718806717428151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7228689650291742289904201 5421517237718806717428151)
            ·
              refine ⟨8132275856578210076142227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421517237718806717428151 8132275856578210076142227)
              ·
                refine ⟨12198413784867315114213341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132275856578210076142227 12198413784867315114213341)
                ·
                  refine ⟨4574405169325243167830003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12198413784867315114213341 4574405169325243167830003)
                  ·
                    refine ⟨6861607753987864751745005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574405169325243167830003 6861607753987864751745005)
                    ·
                      refine ⟨2573102907745449281904377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6861607753987864751745005 2573102907745449281904377)
                      ·
                        rfl

theorem cell23_5011100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5011100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011100 prefixEnd_5011100 := by exact prefixLift 5011100
  have htrace : WordTrace (prefixWord ++ tailWord_5011100) baseStart_5011100 baseEnd_5011100 := by
    simpa [prefixWord, tailWord_5011100, baseEnd_5011100] using wordTrace_append hprefix tailTrace_5011100
  have hstable : (prefixWord ++ tailWord_5011100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011100).length < 2 ^ (prefixWord ++ tailWord_5011100).sum := by decide
  have hdescent : baseEnd_5011100 < baseStart_5011100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011109 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_5011109 : Nat := 118140960795 + 5011109 * 2 ^ 59
def prefixEnd_5011109 : Nat := 4983230072969 + 3 ^ 40 * 5011109 * 2
def baseEnd_5011109 : Nat := 2573107529071339746691835

theorem tailTrace_5011109 : CollatzResearch.WordTrace tailWord_5011109 prefixEnd_5011109 2573107529071339746691835 := by
  unfold tailWord_5011109
  simp only [CollatzResearch.WordTrace]
  refine ⟨182770160402615397126260381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121846773601743598084173587 182770160402615397126260381)
  ·
    refine ⟨68538810150980773922347643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182770160402615397126260381 68538810150980773922347643)
    ·
      refine ⟨102808215226471160883521465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68538810150980773922347643 102808215226471160883521465)
      ·
        refine ⟨77106161419853370662641099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102808215226471160883521465 77106161419853370662641099)
        ·
          refine ⟨115659242129780055993961649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77106161419853370662641099 115659242129780055993961649)
          ·
            refine ⟨86744431597335041995471237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115659242129780055993961649 86744431597335041995471237)
            ·
              refine ⟨16264580924500320374150857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86744431597335041995471237 16264580924500320374150857)
              ·
                refine ⟨12198435693375240280613143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16264580924500320374150857 12198435693375240280613143)
                ·
                  refine ⟨18297653540062860420919715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12198435693375240280613143 18297653540062860420919715)
                  ·
                    refine ⟨27446480310094290631379573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18297653540062860420919715 27446480310094290631379573)
                    ·
                      refine ⟨2573107529071339746691835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27446480310094290631379573 2573107529071339746691835)
                      ·
                        rfl

theorem cell23_5011109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_5011109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011109 prefixEnd_5011109 := by exact prefixLift 5011109
  have htrace : WordTrace (prefixWord ++ tailWord_5011109) baseStart_5011109 baseEnd_5011109 := by
    simpa [prefixWord, tailWord_5011109, baseEnd_5011109] using wordTrace_append hprefix tailTrace_5011109
  have hstable : (prefixWord ++ tailWord_5011109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011109).length < 2 ^ (prefixWord ++ tailWord_5011109).sum := by decide
  have hdescent : baseEnd_5011109 < baseStart_5011109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011119 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_5011119 : Nat := 118140960795 + 5011119 * 2 ^ 59
def prefixEnd_5011119 : Nat := 4983230072969 + 3 ^ 40 * 5011119 * 2
def baseEnd_5011119 : Nat := 2573112663877884707566789

theorem tailTrace_5011119 : CollatzResearch.WordTrace tailWord_5011119 prefixEnd_5011119 2573112663877884707566789 := by
  unfold tailWord_5011119
  simp only [CollatzResearch.WordTrace]
  refine ⟨182770525132579168834124411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121847016755052779222749607 182770525132579168834124411)
  ·
    refine ⟨274155787698868753251186617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182770525132579168834124411 274155787698868753251186617)
    ·
      refine ⟨205616840774151564938389963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274155787698868753251186617 205616840774151564938389963)
      ·
        refine ⟨308425261161227347407584945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205616840774151564938389963 308425261161227347407584945)
        ·
          refine ⟨231318945870920510555688709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308425261161227347407584945 231318945870920510555688709)
          ·
            refine ⟨43372302350797595729191633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231318945870920510555688709 43372302350797595729191633)
            ·
              refine ⟨32529226763098196796893725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43372302350797595729191633 32529226763098196796893725)
              ·
                refine ⟨12198460036161823798835147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32529226763098196796893725 12198460036161823798835147)
                ·
                  refine ⟨18297690054242735698252721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12198460036161823798835147 18297690054242735698252721)
                  ·
                    refine ⟨13723267540682051773689541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18297690054242735698252721 13723267540682051773689541)
                    ·
                      refine ⟨2573112663877884707566789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13723267540682051773689541 2573112663877884707566789)
                      ·
                        rfl

theorem cell23_5011119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_5011119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011119 prefixEnd_5011119 := by exact prefixLift 5011119
  have htrace : WordTrace (prefixWord ++ tailWord_5011119) baseStart_5011119 baseEnd_5011119 := by
    simpa [prefixWord, tailWord_5011119, baseEnd_5011119] using wordTrace_append hprefix tailTrace_5011119
  have hstable : (prefixWord ++ tailWord_5011119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011119).length < 2 ^ (prefixWord ++ tailWord_5011119).sum := by decide
  have hdescent : baseEnd_5011119 < baseStart_5011119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011143 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_5011143 : Nat := 118140960795 + 5011143 * 2 ^ 59
def prefixEnd_5011143 : Nat := 4983230072969 + 3 ^ 40 * 5011143 * 2
def baseEnd_5011143 : Nat := 2573124987413592613666679

theorem tailTrace_5011143 : CollatzResearch.WordTrace tailWord_5011143 prefixEnd_5011143 2573124987413592613666679 := by
  unfold tailWord_5011143
  simp only [CollatzResearch.WordTrace]
  refine ⟨182771400484492220932998083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121847600322994813955332055 182771400484492220932998083)
  ·
    refine ⟨274157100726738331399497125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182771400484492220932998083 274157100726738331399497125)
    ·
      refine ⟨51404456386263437137405711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274157100726738331399497125 51404456386263437137405711)
      ·
        refine ⟨77106684579395155706108567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51404456386263437137405711 77106684579395155706108567)
        ·
          refine ⟨115660026869092733559162851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77106684579395155706108567 115660026869092733559162851)
          ·
            refine ⟨173490040303639100338744277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115660026869092733559162851 173490040303639100338744277)
            ·
              refine ⟨4066172819616541414189319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173490040303639100338744277 4066172819616541414189319)
              ·
                refine ⟨6099259229424812121283979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066172819616541414189319 6099259229424812121283979)
                ·
                  refine ⟨9148888844137218181925969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6099259229424812121283979 9148888844137218181925969)
                  ·
                    refine ⟨6861666633102913636444477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9148888844137218181925969 6861666633102913636444477)
                    ·
                      refine ⟨2573124987413592613666679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6861666633102913636444477 2573124987413592613666679)
                      ·
                        rfl

theorem cell23_5011143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_5011143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011143 prefixEnd_5011143 := by exact prefixLift 5011143
  have htrace : WordTrace (prefixWord ++ tailWord_5011143) baseStart_5011143 baseEnd_5011143 := by
    simpa [prefixWord, tailWord_5011143, baseEnd_5011143] using wordTrace_append hprefix tailTrace_5011143
  have hstable : (prefixWord ++ tailWord_5011143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011143).length < 2 ^ (prefixWord ++ tailWord_5011143).sum := by decide
  have hdescent : baseEnd_5011143 < baseStart_5011143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011173 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5011173 : Nat := 118140960795 + 5011173 * 2 ^ 59
def prefixEnd_5011173 : Nat := 4983230072969 + 3 ^ 40 * 5011173 * 2
def baseEnd_5011173 : Nat := 2573140391833227496291541

theorem tailTrace_5011173 : CollatzResearch.WordTrace tailWord_5011173 prefixEnd_5011173 2573140391833227496291541 := by
  unfold tailWord_5011173
  simp only [CollatzResearch.WordTrace]
  refine ⟨182772494674383536056590173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121848329782922357371060115 182772494674383536056590173)
  ·
    refine ⟨68539685502893826021221315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182772494674383536056590173 68539685502893826021221315)
    ·
      refine ⟨102809528254340739031831973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68539685502893826021221315 102809528254340739031831973)
      ·
        refine ⟨19276786547688888568468495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102809528254340739031831973 19276786547688888568468495)
        ·
          refine ⟨28915179821533332852702743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19276786547688888568468495 28915179821533332852702743)
          ·
            refine ⟨43372769732299999279054115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28915179821533332852702743 43372769732299999279054115)
            ·
              refine ⟨65059154598449998918581173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43372769732299999279054115 65059154598449998918581173)
              ·
                refine ⟨6099295743604687398616985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65059154598449998918581173 6099295743604687398616985)
                ·
                  refine ⟨4574471807703515548962739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099295743604687398616985 4574471807703515548962739)
                  ·
                    refine ⟨6861707711555273323444109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574471807703515548962739 6861707711555273323444109)
                    ·
                      refine ⟨2573140391833227496291541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6861707711555273323444109 2573140391833227496291541)
                      ·
                        rfl

theorem cell23_5011173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5011173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011173 prefixEnd_5011173 := by exact prefixLift 5011173
  have htrace : WordTrace (prefixWord ++ tailWord_5011173) baseStart_5011173 baseEnd_5011173 := by
    simpa [prefixWord, tailWord_5011173, baseEnd_5011173] using wordTrace_append hprefix tailTrace_5011173
  have hstable : (prefixWord ++ tailWord_5011173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011173).length < 2 ^ (prefixWord ++ tailWord_5011173).sum := by decide
  have hdescent : baseEnd_5011173 < baseStart_5011173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011183 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 1, 3, 2]
def baseStart_5011183 : Nat := 118140960795 + 5011183 * 2 ^ 59
def prefixEnd_5011183 : Nat := 4983230072969 + 3 ^ 40 * 5011183 * 2
def baseEnd_5011183 : Nat := 2573145526639772457166495

theorem tailTrace_5011183 : CollatzResearch.WordTrace tailWord_5011183 prefixEnd_5011183 2573145526639772457166495 := by
  unfold tailWord_5011183
  simp only [CollatzResearch.WordTrace]
  refine ⟨182772859404347307764454203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121848572936231538509636135 182772859404347307764454203)
  ·
    refine ⟨274159289106520961646681305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182772859404347307764454203 274159289106520961646681305)
    ·
      refine ⟨205619466829890721235010979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274159289106520961646681305 205619466829890721235010979)
      ·
        refine ⟨308429200244836081852516469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205619466829890721235010979 308429200244836081852516469)
        ·
          refine ⟨28915237522953382673673419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 308429200244836081852516469 28915237522953382673673419)
          ·
            refine ⟨43372856284430074010510129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28915237522953382673673419 43372856284430074010510129)
            ·
              refine ⟨32529642213322555507882597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43372856284430074010510129 32529642213322555507882597)
              ·
                refine ⟨6099307914997979157727987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32529642213322555507882597 6099307914997979157727987)
                ·
                  refine ⟨9148961872496968736591981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6099307914997979157727987 9148961872496968736591981)
                  ·
                    refine ⟨3430860702186363276221993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9148961872496968736591981 3430860702186363276221993)
                    ·
                      refine ⟨2573145526639772457166495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3430860702186363276221993 2573145526639772457166495)
                      ·
                        rfl

theorem cell23_5011183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3, 2].length) (baseStart_5011183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011183 prefixEnd_5011183 := by exact prefixLift 5011183
  have htrace : WordTrace (prefixWord ++ tailWord_5011183) baseStart_5011183 baseEnd_5011183 := by
    simpa [prefixWord, tailWord_5011183, baseEnd_5011183] using wordTrace_append hprefix tailTrace_5011183
  have hstable : (prefixWord ++ tailWord_5011183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011183).length < 2 ^ (prefixWord ++ tailWord_5011183).sum := by decide
  have hdescent : baseEnd_5011183 < baseStart_5011183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011199 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_5011199 : Nat := 118140960795 + 5011199 * 2 ^ 59
def prefixEnd_5011199 : Nat := 4983230072969 + 3 ^ 40 * 5011199 * 2
def baseEnd_5011199 : Nat := 2573153742330244394566421

theorem tailTrace_5011199 : CollatzResearch.WordTrace tailWord_5011199 prefixEnd_5011199 2573153742330244394566421 := by
  unfold tailWord_5011199
  simp only [CollatzResearch.WordTrace]
  refine ⟨182773442972289342497036651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121848961981526228331357767 182773442972289342497036651)
  ·
    refine ⟨274160164458434013745554977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182773442972289342497036651 274160164458434013745554977)
    ·
      refine ⟨205620123343825510309166233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274160164458434013745554977 205620123343825510309166233)
      ·
        refine ⟨154215092507869132731874675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205620123343825510309166233 154215092507869132731874675)
        ·
          refine ⟨231322638761803699097812013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154215092507869132731874675 231322638761803699097812013)
          ·
            refine ⟨86745989535676387161679505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231322638761803699097812013 86745989535676387161679505)
            ·
              refine ⟨65059492151757290371259629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86745989535676387161679505 65059492151757290371259629)
              ·
                refine ⟨24397309556908983889222361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65059492151757290371259629 24397309556908983889222361)
                ·
                  refine ⟨18297982167681737916916771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24397309556908983889222361 18297982167681737916916771)
                  ·
                    refine ⟨27446973251522606875375157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18297982167681737916916771 27446973251522606875375157)
                    ·
                      refine ⟨2573153742330244394566421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27446973251522606875375157 2573153742330244394566421)
                      ·
                        rfl

theorem cell23_5011199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_5011199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011199 prefixEnd_5011199 := by exact prefixLift 5011199
  have htrace : WordTrace (prefixWord ++ tailWord_5011199) baseStart_5011199 baseEnd_5011199 := by
    simpa [prefixWord, tailWord_5011199, baseEnd_5011199] using wordTrace_append hprefix tailTrace_5011199
  have hstable : (prefixWord ++ tailWord_5011199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011199).length < 2 ^ (prefixWord ++ tailWord_5011199).sum := by decide
  have hdescent : baseEnd_5011199 < baseStart_5011199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011207 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5011207 : Nat := 118140960795 + 5011207 * 2 ^ 59
def prefixEnd_5011207 : Nat := 4983230072969 + 3 ^ 40 * 5011207 * 2
def baseEnd_5011207 : Nat := 2573157850175480363266385

theorem tailTrace_5011207 : CollatzResearch.WordTrace tailWord_5011207 prefixEnd_5011207 2573157850175480363266385 := by
  unfold tailWord_5011207
  simp only [CollatzResearch.WordTrace]
  refine ⟨182773734756260359863327875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121849156504173573242218583 182773734756260359863327875)
  ·
    refine ⟨274160602134390539794991813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182773734756260359863327875 274160602134390539794991813)
    ·
      refine ⟨51405112900198226211560965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274160602134390539794991813 51405112900198226211560965)
      ·
        refine ⟨9638458668787167414667681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51405112900198226211560965 9638458668787167414667681)
        ·
          refine ⟨7228844001590375561000761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9638458668787167414667681 7228844001590375561000761)
          ·
            refine ⟨5421633001192781670750571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7228844001590375561000761 5421633001192781670750571)
            ·
              refine ⟨8132449501789172506125857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421633001192781670750571 8132449501789172506125857)
              ·
                refine ⟨6099337126341879379594393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8132449501789172506125857 6099337126341879379594393)
                ·
                  refine ⟨4574502844756409534695795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099337126341879379594393 4574502844756409534695795)
                  ·
                    refine ⟨6861754267134614302043693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574502844756409534695795 6861754267134614302043693)
                    ·
                      refine ⟨2573157850175480363266385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6861754267134614302043693 2573157850175480363266385)
                      ·
                        rfl

theorem cell23_5011207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5011207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011207 prefixEnd_5011207 := by exact prefixLift 5011207
  have htrace : WordTrace (prefixWord ++ tailWord_5011207) baseStart_5011207 baseEnd_5011207 := by
    simpa [prefixWord, tailWord_5011207, baseEnd_5011207] using wordTrace_append hprefix tailTrace_5011207
  have hstable : (prefixWord ++ tailWord_5011207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011207).length < 2 ^ (prefixWord ++ tailWord_5011207).sum := by decide
  have hdescent : baseEnd_5011207 < baseStart_5011207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011226 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_5011226 : Nat := 118140960795 + 5011226 * 2 ^ 59
def prefixEnd_5011226 : Nat := 4983230072969 + 3 ^ 40 * 5011226 * 2
def baseEnd_5011226 : Nat := 2573167606307915788928797

theorem tailTrace_5011226 : CollatzResearch.WordTrace tailWord_5011226 prefixEnd_5011226 2573167606307915788928797 := by
  unfold tailWord_5011226
  simp only [CollatzResearch.WordTrace]
  refine ⟨45693606935797881527067383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121849618495461017405513021 45693606935797881527067383)
  ·
    refine ⟨68540410403696822290601075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45693606935797881527067383 68540410403696822290601075)
    ·
      refine ⟨102810615605545233435901613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68540410403696822290601075 102810615605545233435901613)
      ·
        refine ⟨38553980852079462538463105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102810615605545233435901613 38553980852079462538463105)
        ·
          refine ⟨28915485639059596903847329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38553980852079462538463105 28915485639059596903847329)
          ·
            refine ⟨21686614229294697677885497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28915485639059596903847329 21686614229294697677885497)
            ·
              refine ⟨16264960671971023258414123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21686614229294697677885497 16264960671971023258414123)
              ·
                refine ⟨24397441007956534887621185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16264960671971023258414123 24397441007956534887621185)
                ·
                  refine ⟨18298080755967401165715889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24397441007956534887621185 18298080755967401165715889)
                  ·
                    refine ⟨13723560566975550874286917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18298080755967401165715889 13723560566975550874286917)
                    ·
                      refine ⟨2573167606307915788928797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13723560566975550874286917 2573167606307915788928797)
                      ·
                        rfl

theorem cell23_5011226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_5011226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011226 prefixEnd_5011226 := by exact prefixLift 5011226
  have htrace : WordTrace (prefixWord ++ tailWord_5011226) baseStart_5011226 baseEnd_5011226 := by
    simpa [prefixWord, tailWord_5011226, baseEnd_5011226] using wordTrace_append hprefix tailTrace_5011226
  have hstable : (prefixWord ++ tailWord_5011226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011226).length < 2 ^ (prefixWord ++ tailWord_5011226).sum := by decide
  have hdescent : baseEnd_5011226 < baseStart_5011226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011236 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 7]
def baseStart_5011236 : Nat := 118140960795 + 5011236 * 2 ^ 59
def prefixEnd_5011236 : Nat := 4983230072969 + 3 ^ 40 * 5011236 * 2
def baseEnd_5011236 : Nat := 285908082346051194422639

theorem tailTrace_5011236 : CollatzResearch.WordTrace tailWord_5011236 prefixEnd_5011236 285908082346051194422639 := by
  unfold tailWord_5011236
  simp only [CollatzResearch.WordTrace]
  refine ⟨91387396236577648908066781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121849861648770198544089041 91387396236577648908066781)
  ·
    refine ⟨34270273588716618340525043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91387396236577648908066781 34270273588716618340525043)
    ·
      refine ⟨51405410383074927510787565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34270273588716618340525043 51405410383074927510787565)
      ·
        refine ⟨19277028893653097816545337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51405410383074927510787565 19277028893653097816545337)
        ·
          refine ⟨14457771670239823362409003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19277028893653097816545337 14457771670239823362409003)
          ·
            refine ⟨21686657505359735043613505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14457771670239823362409003 21686657505359735043613505)
            ·
              refine ⟨16264993129019801282710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21686657505359735043613505 16264993129019801282710129)
              ·
                refine ⟨12198744846764850962032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16264993129019801282710129 12198744846764850962032597)
                ·
                  refine ⟨285908082346051194422639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12198744846764850962032597 285908082346051194422639)
                  ·
                    rfl

theorem cell23_5011236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_5011236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011236 prefixEnd_5011236 := by exact prefixLift 5011236
  have htrace : WordTrace (prefixWord ++ tailWord_5011236) baseStart_5011236 baseEnd_5011236 := by
    simpa [prefixWord, tailWord_5011236, baseEnd_5011236] using wordTrace_append hprefix tailTrace_5011236
  have hstable : (prefixWord ++ tailWord_5011236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011236).length < 2 ^ (prefixWord ++ tailWord_5011236).sum := by decide
  have hdescent : baseEnd_5011236 < baseStart_5011236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011270 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_5011270 : Nat := 118140960795 + 5011270 * 2 ^ 59
def prefixEnd_5011270 : Nat := 4983230072969 + 3 ^ 40 * 5011270 * 2
def baseEnd_5011270 : Nat := 285910022161857068530955

theorem tailTrace_5011270 : CollatzResearch.WordTrace tailWord_5011270 prefixEnd_5011270 285910022161857068530955 := by
  unfold tailWord_5011270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5711751017344753800714727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121850688370021414415247509 5711751017344753800714727)
  ·
    refine ⟨8567626526017130701072091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5711751017344753800714727 8567626526017130701072091)
    ·
      refine ⟨12851439789025696051608137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8567626526017130701072091 12851439789025696051608137)
      ·
        refine ⟨9638579841769272038706103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12851439789025696051608137 9638579841769272038706103)
        ·
          refine ⟨14457869762653908058059155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9638579841769272038706103 14457869762653908058059155)
          ·
            refine ⟨21686804643980862087088733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14457869762653908058059155 21686804643980862087088733)
            ·
              refine ⟨8132551741492823282658275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21686804643980862087088733 8132551741492823282658275)
              ·
                refine ⟨12198827612239234923987413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132551741492823282658275 12198827612239234923987413)
                ·
                  refine ⟨285910022161857068530955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12198827612239234923987413 285910022161857068530955)
                  ·
                    rfl

theorem cell23_5011270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_5011270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011270 prefixEnd_5011270 := by exact prefixLift 5011270
  have htrace : WordTrace (prefixWord ++ tailWord_5011270) baseStart_5011270 baseEnd_5011270 := by
    simpa [prefixWord, tailWord_5011270, baseEnd_5011270] using wordTrace_append hprefix tailTrace_5011270
  have hstable : (prefixWord ++ tailWord_5011270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011270).length < 2 ^ (prefixWord ++ tailWord_5011270).sum := by decide
  have hdescent : baseEnd_5011270 < baseStart_5011270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011303 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_5011303 : Nat := 118140960795 + 5011303 * 2 ^ 59
def prefixEnd_5011303 : Nat := 4983230072969 + 3 ^ 40 * 5011303 * 2
def baseEnd_5011303 : Nat := 2573207144318311987665943

theorem tailTrace_5011303 : CollatzResearch.WordTrace tailWord_5011303 prefixEnd_5011303 2573207144318311987665943 := by
  unfold tailWord_5011303
  simp only [CollatzResearch.WordTrace]
  refine ⟨182777236163912568258822563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121851490775941712172548375 182777236163912568258822563)
  ·
    refine ⟨274165854245868852388233845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182777236163912568258822563 274165854245868852388233845)
    ·
      refine ⟨25703048835550204911396923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274165854245868852388233845 25703048835550204911396923)
      ·
        refine ⟨38554573253325307367095385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25703048835550204911396923 38554573253325307367095385)
        ·
          refine ⟨28915929939993980525321539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38554573253325307367095385 28915929939993980525321539)
          ·
            refine ⟨43373894909990970787982309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28915929939993980525321539 43373894909990970787982309)
            ·
              refine ⟨8132605295623307022746683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43373894909990970787982309 8132605295623307022746683)
              ·
                refine ⟨12198907943434960534120025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132605295623307022746683 12198907943434960534120025)
                ·
                  refine ⟨9149180957576220400590019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12198907943434960534120025 9149180957576220400590019)
                  ·
                    refine ⟨13723771436364330600885029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9149180957576220400590019 13723771436364330600885029)
                    ·
                      refine ⟨2573207144318311987665943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13723771436364330600885029 2573207144318311987665943)
                      ·
                        rfl

theorem cell23_5011303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_5011303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011303 prefixEnd_5011303 := by exact prefixLift 5011303
  have htrace : WordTrace (prefixWord ++ tailWord_5011303) baseStart_5011303 baseEnd_5011303 := by
    simpa [prefixWord, tailWord_5011303, baseEnd_5011303] using wordTrace_append hprefix tailTrace_5011303
  have hstable : (prefixWord ++ tailWord_5011303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011303).length < 2 ^ (prefixWord ++ tailWord_5011303).sum := by decide
  have hdescent : baseEnd_5011303 < baseStart_5011303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011353 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 3]
def baseStart_5011353 : Nat := 118140960795 + 5011353 * 2 ^ 59
def prefixEnd_5011353 : Nat := 4983230072969 + 3 ^ 40 * 5011353 * 2
def baseEnd_5011353 : Nat := 2573232818351036792040713

theorem tailTrace_5011353 : CollatzResearch.WordTrace tailWord_5011353 prefixEnd_5011353 2573232818351036792040713 := by
  unfold tailWord_5011353
  simp only [CollatzResearch.WordTrace]
  refine ⟨182779059813731426798142713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121852706542487617865428475 182779059813731426798142713)
  ·
    refine ⟨137084294860298570098607035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182779059813731426798142713 137084294860298570098607035)
    ·
      refine ⟨205626442290447855147910553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137084294860298570098607035 205626442290447855147910553)
      ·
        refine ⟨154219831717835891360932915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205626442290447855147910553 154219831717835891360932915)
        ·
          refine ⟨231329747576753837041399373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154219831717835891360932915 231329747576753837041399373)
          ·
            refine ⟨86748655341282688890524765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231329747576753837041399373 86748655341282688890524765)
            ·
              refine ⟨32530745752981008333946787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86748655341282688890524765 32530745752981008333946787)
              ·
                refine ⟨48796118629471512500920181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32530745752981008333946787 48796118629471512500920181)
                ·
                  refine ⟨4574636121512954296961267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48796118629471512500920181 4574636121512954296961267)
                  ·
                    refine ⟨6861954182269431445441901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574636121512954296961267 6861954182269431445441901)
                    ·
                      refine ⟨2573232818351036792040713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6861954182269431445441901 2573232818351036792040713)
                      ·
                        rfl

theorem cell23_5011353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_5011353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011353 prefixEnd_5011353 := by exact prefixLift 5011353
  have htrace : WordTrace (prefixWord ++ tailWord_5011353) baseStart_5011353 baseEnd_5011353 := by
    simpa [prefixWord, tailWord_5011353, baseEnd_5011353] using wordTrace_append hprefix tailTrace_5011353
  have hstable : (prefixWord ++ tailWord_5011353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011353).length < 2 ^ (prefixWord ++ tailWord_5011353).sum := by decide
  have hdescent : baseEnd_5011353 < baseStart_5011353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011416 : List Nat := [2, 1, 2, 2, 2, 2, 3, 9]
def baseStart_5011416 : Nat := 118140960795 + 5011416 * 2 ^ 59
def prefixEnd_5011416 : Nat := 4983230072969 + 3 ^ 40 * 5011416 * 2
def baseEnd_5011416 : Nat := 95306117319713705390849

theorem tailTrace_5011416 : CollatzResearch.WordTrace tailWord_5011416 prefixEnd_5011416 95306117319713705390849 := by
  unfold tailWord_5011416
  simp only [CollatzResearch.WordTrace]
  refine ⟨91390678806251594278843051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121854238408335459038457401 91390678806251594278843051)
  ·
    refine ⟨137086018209377391418264577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91390678806251594278843051 137086018209377391418264577)
    ·
      refine ⟨102814513657033043563698433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137086018209377391418264577 102814513657033043563698433)
      ·
        refine ⟨77110885242774782672773825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102814513657033043563698433 77110885242774782672773825)
        ·
          refine ⟨57833163932081087004580369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77110885242774782672773825 57833163932081087004580369)
          ·
            refine ⟨43374872949060815253435277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57833163932081087004580369 43374872949060815253435277)
            ·
              refine ⟨16265577355897805720038229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43374872949060815253435277 16265577355897805720038229)
              ·
                refine ⟨95306117319713705390849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16265577355897805720038229 95306117319713705390849)
                ·
                  rfl

theorem cell23_5011416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 9].length) (baseStart_5011416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011416 prefixEnd_5011416 := by exact prefixLift 5011416
  have htrace : WordTrace (prefixWord ++ tailWord_5011416) baseStart_5011416 baseEnd_5011416 := by
    simpa [prefixWord, tailWord_5011416, baseEnd_5011416] using wordTrace_append hprefix tailTrace_5011416
  have hstable : (prefixWord ++ tailWord_5011416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011416).length < 2 ^ (prefixWord ++ tailWord_5011416).sum := by decide
  have hdescent : baseEnd_5011416 < baseStart_5011416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011421 : List Nat := [1, 4, 3, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_5011421 : Nat := 118140960795 + 5011421 * 2 ^ 59
def prefixEnd_5011421 : Nat := 4983230072969 + 3 ^ 40 * 5011421 * 2
def baseEnd_5011421 : Nat := 2573267735035542525990401

theorem tailTrace_5011421 : CollatzResearch.WordTrace tailWord_5011421 prefixEnd_5011421 2573267735035542525990401 := by
  unfold tailWord_5011421
  simp only [CollatzResearch.WordTrace]
  refine ⟨182781539977485074411618117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121854359984990049607745411 182781539977485074411618117)
  ·
    refine ⟨34271538745778451452178397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182781539977485074411618117 34271538745778451452178397)
    ·
      refine ⟨12851827029666919294566899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34271538745778451452178397 12851827029666919294566899)
      ·
        refine ⟨19277740544500378941850349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12851827029666919294566899 19277740544500378941850349)
        ·
          refine ⟨7229152704187642103193881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19277740544500378941850349 7229152704187642103193881)
          ·
            refine ⟨5421864528140731577395411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229152704187642103193881 5421864528140731577395411)
            ·
              refine ⟨8132796792211097366093117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5421864528140731577395411 8132796792211097366093117)
              ·
                refine ⟨3049798797079161512284919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8132796792211097366093117 3049798797079161512284919)
                ·
                  refine ⟨4574698195618742268427379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049798797079161512284919 4574698195618742268427379)
                  ·
                    refine ⟨6862047293428113402641069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574698195618742268427379 6862047293428113402641069)
                    ·
                      refine ⟨2573267735035542525990401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6862047293428113402641069 2573267735035542525990401)
                      ·
                        rfl

theorem cell23_5011421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_5011421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011421 prefixEnd_5011421 := by exact prefixLift 5011421
  have htrace : WordTrace (prefixWord ++ tailWord_5011421) baseStart_5011421 baseEnd_5011421 := by
    simpa [prefixWord, tailWord_5011421, baseEnd_5011421] using wordTrace_append hprefix tailTrace_5011421
  have hstable : (prefixWord ++ tailWord_5011421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011421).length < 2 ^ (prefixWord ++ tailWord_5011421).sum := by decide
  have hdescent : baseEnd_5011421 < baseStart_5011421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011454 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5011454 : Nat := 118140960795 + 5011454 * 2 ^ 59
def prefixEnd_5011454 : Nat := 4983230072969 + 3 ^ 40 * 5011454 * 2
def baseEnd_5011454 : Nat := 857761559965713632292583

theorem tailTrace_5011454 : CollatzResearch.WordTrace tailWord_5011454 prefixEnd_5011454 857761559965713632292583 := by
  unfold tailWord_5011454
  simp only [CollatzResearch.WordTrace]
  refine ⟨22847842948295690130946177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121855162390910347365046277 22847842948295690130946177)
  ·
    refine ⟨17135882211221767598209633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22847842948295690130946177 17135882211221767598209633)
    ·
      refine ⟨12851911658416325698657225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17135882211221767598209633 12851911658416325698657225)
      ·
        refine ⟨9638933743812244273992919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12851911658416325698657225 9638933743812244273992919)
        ·
          refine ⟨14458400615718366410989379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9638933743812244273992919 14458400615718366410989379)
          ·
            refine ⟨21687600923577549616484069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14458400615718366410989379 21687600923577549616484069)
            ·
              refine ⟨4066425173170790553090763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21687600923577549616484069 4066425173170790553090763)
              ·
                refine ⟨6099637759756185829636145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066425173170790553090763 6099637759756185829636145)
                ·
                  refine ⟨4574728319817139372227109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6099637759756185829636145 4574728319817139372227109)
                  ·
                    refine ⟨857761559965713632292583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4574728319817139372227109 857761559965713632292583)
                    ·
                      rfl

theorem cell23_5011454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5011454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011454 prefixEnd_5011454 := by exact prefixLift 5011454
  have htrace : WordTrace (prefixWord ++ tailWord_5011454) baseStart_5011454 baseEnd_5011454 := by
    simpa [prefixWord, tailWord_5011454, baseEnd_5011454] using wordTrace_append hprefix tailTrace_5011454
  have hstable : (prefixWord ++ tailWord_5011454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011454).length < 2 ^ (prefixWord ++ tailWord_5011454).sum := by decide
  have hdescent : baseEnd_5011454 < baseStart_5011454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011456 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_5011456 : Nat := 118140960795 + 5011456 * 2 ^ 59
def prefixEnd_5011456 : Nat := 4983230072969 + 3 ^ 40 * 5011456 * 2
def baseEnd_5011456 : Nat := 2573285706858449889052739

theorem tailTrace_5011456 : CollatzResearch.WordTrace tailWord_5011456 prefixEnd_5011456 2573285706858449889052739 := by
  unfold tailWord_5011456
  simp only [CollatzResearch.WordTrace]
  refine ⟨91391408266179137694571111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121855211021572183592761481 91391408266179137694571111)
  ·
    refine ⟨137087112399268706541856667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91391408266179137694571111 137087112399268706541856667)
    ·
      refine ⟨205630668598903059812785001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137087112399268706541856667 205630668598903059812785001)
      ·
        refine ⟨154223001449177294859588751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205630668598903059812785001 154223001449177294859588751)
        ·
          refine ⟨231334502173765942289383127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154223001449177294859588751 231334502173765942289383127)
          ·
            refine ⟨347001753260648913434074691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231334502173765942289383127 347001753260648913434074691)
            ·
              refine ⟨520502629890973370151112037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347001753260648913434074691 520502629890973370151112037)
              ·
                refine ⟨97594243104557506903333507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 520502629890973370151112037 97594243104557506903333507)
                ·
                  refine ⟨146391364656836260355000261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97594243104557506903333507 146391364656836260355000261)
                  ·
                    refine ⟨27448380873156798816562549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146391364656836260355000261 27448380873156798816562549)
                    ·
                      refine ⟨2573285706858449889052739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27448380873156798816562549 2573285706858449889052739)
                      ·
                        rfl

theorem cell23_5011456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_5011456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011456 prefixEnd_5011456 := by exact prefixLift 5011456
  have htrace : WordTrace (prefixWord ++ tailWord_5011456) baseStart_5011456 baseEnd_5011456 := by
    simpa [prefixWord, tailWord_5011456, baseEnd_5011456] using wordTrace_append hprefix tailTrace_5011456
  have hstable : (prefixWord ++ tailWord_5011456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011456).length < 2 ^ (prefixWord ++ tailWord_5011456).sum := by decide
  have hdescent : baseEnd_5011456 < baseStart_5011456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011495 : List Nat := [1, 1, 7, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5011495 : Nat := 118140960795 + 5011495 * 2 ^ 59
def prefixEnd_5011495 : Nat := 4983230072969 + 3 ^ 40 * 5011495 * 2
def baseEnd_5011495 : Nat := 2573305732603975236465061

theorem tailTrace_5011495 : CollatzResearch.WordTrace tailWord_5011495 prefixEnd_5011495 2573305732603975236465061 := by
  unfold tailWord_5011495
  simp only [CollatzResearch.WordTrace]
  refine ⟨182784238979216985049811939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121856159319477990033207959 182784238979216985049811939)
  ·
    refine ⟨274176358468825477574717909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182784238979216985049811939 274176358468825477574717909)
    ·
      refine ⟨6426008401613097130657451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 274176358468825477574717909 6426008401613097130657451)
      ·
        refine ⟨9639012602419645695986177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426008401613097130657451 9639012602419645695986177)
        ·
          refine ⟨7229259451814734271989633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9639012602419645695986177 7229259451814734271989633)
          ·
            refine ⟨5421944588861050703992225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229259451814734271989633 5421944588861050703992225)
            ·
              refine ⟨4066458441645788027994169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5421944588861050703992225 4066458441645788027994169)
              ·
                refine ⟨3049843831234341020995627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4066458441645788027994169 3049843831234341020995627)
                ·
                  refine ⟨4574765746851511531493441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049843831234341020995627 4574765746851511531493441)
                  ·
                    refine ⟨3431074310138633648620081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4574765746851511531493441 3431074310138633648620081)
                    ·
                      refine ⟨2573305732603975236465061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431074310138633648620081 2573305732603975236465061)
                      ·
                        rfl

theorem cell23_5011495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5011495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011495 prefixEnd_5011495 := by exact prefixLift 5011495
  have htrace : WordTrace (prefixWord ++ tailWord_5011495) baseStart_5011495 baseEnd_5011495 := by
    simpa [prefixWord, tailWord_5011495, baseEnd_5011495] using wordTrace_append hprefix tailTrace_5011495
  have hstable : (prefixWord ++ tailWord_5011495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011495).length < 2 ^ (prefixWord ++ tailWord_5011495).sum := by decide
  have hdescent : baseEnd_5011495 < baseStart_5011495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011510 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5011510 : Nat := 118140960795 + 5011510 * 2 ^ 59
def prefixEnd_5011510 : Nat := 4983230072969 + 3 ^ 40 * 5011510 * 2
def baseEnd_5011510 : Nat := 857771144937930892592497

theorem tailTrace_5011510 : CollatzResearch.WordTrace tailWord_5011510 prefixEnd_5011510 857771144937930892592497 := by
  unfold tailWord_5011510
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424049129635165163225499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121856524049441761741071989 11424049129635165163225499)
  ·
    refine ⟨17136073694452747744838249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11424049129635165163225499 17136073694452747744838249)
    ·
      refine ⟨12852055270839560808628687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17136073694452747744838249 12852055270839560808628687)
      ·
        refine ⟨19278082906259341212943031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12852055270839560808628687 19278082906259341212943031)
        ·
          refine ⟨28917124359389011819414547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19278082906259341212943031 28917124359389011819414547)
          ·
            refine ⟨43375686539083517729121821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28917124359389011819414547 43375686539083517729121821)
            ·
              refine ⟨16265882452156319148420683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43375686539083517729121821 16265882452156319148420683)
              ·
                refine ⟨24398823678234478722631025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16265882452156319148420683 24398823678234478722631025)
                ·
                  refine ⟨18299117758675859041973269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24398823678234478722631025 18299117758675859041973269)
                  ·
                    refine ⟨857771144937930892592497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18299117758675859041973269 857771144937930892592497)
                    ·
                      rfl

theorem cell23_5011510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5011510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011510 prefixEnd_5011510 := by exact prefixLift 5011510
  have htrace : WordTrace (prefixWord ++ tailWord_5011510) baseStart_5011510 baseEnd_5011510 := by
    simpa [prefixWord, tailWord_5011510, baseEnd_5011510] using wordTrace_append hprefix tailTrace_5011510
  have hstable : (prefixWord ++ tailWord_5011510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011510).length < 2 ^ (prefixWord ++ tailWord_5011510).sum := by decide
  have hdescent : baseEnd_5011510 < baseStart_5011510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011517 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5011517 : Nat := 118140960795 + 5011517 * 2 ^ 59
def prefixEnd_5011517 : Nat := 4983230072969 + 3 ^ 40 * 5011517 * 2
def baseEnd_5011517 : Nat := 2573317029178374150389959

theorem tailTrace_5011517 : CollatzResearch.WordTrace tailWord_5011517 prefixEnd_5011517 2573317029178374150389959 := by
  unfold tailWord_5011517
  simp only [CollatzResearch.WordTrace]
  refine ⟨182785041385137282807112805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121856694256758188538075203 182785041385137282807112805)
  ·
    refine ⟨34272195259713240526333651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182785041385137282807112805 34272195259713240526333651)
    ·
      refine ⟨51408292889569860789500477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34272195259713240526333651 51408292889569860789500477)
      ·
        refine ⟨19278109833588697796062679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51408292889569860789500477 19278109833588697796062679)
        ·
          refine ⟨28917164750383046694094019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19278109833588697796062679 28917164750383046694094019)
          ·
            refine ⟨43375747125574570041141029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28917164750383046694094019 43375747125574570041141029)
            ·
              refine ⟨8132952586045231882713943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43375747125574570041141029 8132952586045231882713943)
              ·
                refine ⟨12199428879067847824070915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132952586045231882713943 12199428879067847824070915)
                ·
                  refine ⟨18299143318601771736106373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12199428879067847824070915 18299143318601771736106373)
                  ·
                    refine ⟨3431089372237832200519945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18299143318601771736106373 3431089372237832200519945)
                    ·
                      refine ⟨2573317029178374150389959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431089372237832200519945 2573317029178374150389959)
                      ·
                        rfl

theorem cell23_5011517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5011517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011517 prefixEnd_5011517 := by exact prefixLift 5011517
  have htrace : WordTrace (prefixWord ++ tailWord_5011517) baseStart_5011517 baseEnd_5011517 := by
    simpa [prefixWord, tailWord_5011517, baseEnd_5011517] using wordTrace_append hprefix tailTrace_5011517
  have hstable : (prefixWord ++ tailWord_5011517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011517).length < 2 ^ (prefixWord ++ tailWord_5011517).sum := by decide
  have hdescent : baseEnd_5011517 < baseStart_5011517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011538 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_5011538 : Nat := 118140960795 + 5011538 * 2 ^ 59
def prefixEnd_5011538 : Nat := 4983230072969 + 3 ^ 40 * 5011538 * 2
def baseEnd_5011538 : Nat := 2573327812272118568227363

theorem tailTrace_5011538 : CollatzResearch.WordTrace tailWord_5011538 prefixEnd_5011538 2573327812272118568227363 := by
  unfold tailWord_5011538
  simp only [CollatzResearch.WordTrace]
  refine ⟨45696451829515300848406817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121857204878707468929084845 45696451829515300848406817)
  ·
    refine ⟨34272338872136475636305113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45696451829515300848406817 34272338872136475636305113)
    ·
      refine ⟨25704254154102356727228835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34272338872136475636305113 25704254154102356727228835)
      ·
        refine ⟨38556381231153535090843253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25704254154102356727228835 38556381231153535090843253)
        ·
          refine ⟨3614660740420643914766555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38556381231153535090843253 3614660740420643914766555)
          ·
            refine ⟨5421991110630965872149833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614660740420643914766555 5421991110630965872149833)
            ·
              refine ⟨4066493332973224404112375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5421991110630965872149833 4066493332973224404112375)
              ·
                refine ⟨6099739999459836606168563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066493332973224404112375 6099739999459836606168563)
                ·
                  refine ⟨9149609999189754909252845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6099739999459836606168563 9149609999189754909252845)
                  ·
                    refine ⟨3431103749696158090969817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9149609999189754909252845 3431103749696158090969817)
                    ·
                      refine ⟨2573327812272118568227363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431103749696158090969817 2573327812272118568227363)
                      ·
                        rfl

theorem cell23_5011538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_5011538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011538 prefixEnd_5011538 := by exact prefixLift 5011538
  have htrace : WordTrace (prefixWord ++ tailWord_5011538) baseStart_5011538 baseEnd_5011538 := by
    simpa [prefixWord, tailWord_5011538, baseEnd_5011538] using wordTrace_append hprefix tailTrace_5011538
  have hstable : (prefixWord ++ tailWord_5011538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011538).length < 2 ^ (prefixWord ++ tailWord_5011538).sum := by decide
  have hdescent : baseEnd_5011538 < baseStart_5011538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011553 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_5011553 : Nat := 118140960795 + 5011553 * 2 ^ 59
def prefixEnd_5011553 : Nat := 4983230072969 + 3 ^ 40 * 5011553 * 2
def baseEnd_5011553 : Nat := 857778504827312003179931

theorem tailTrace_5011553 : CollatzResearch.WordTrace tailWord_5011553 prefixEnd_5011553 857778504827312003179931 := by
  unfold tailWord_5011553
  simp only [CollatzResearch.WordTrace]
  refine ⟨182786354413006860955423313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121857569608671240636948875 182786354413006860955423313)
  ·
    refine ⟨137089765809755145716567485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182786354413006860955423313 137089765809755145716567485)
    ·
      refine ⟨51408662178658179643712807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137089765809755145716567485 51408662178658179643712807)
      ·
        refine ⟨77112993267987269465569211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51408662178658179643712807 77112993267987269465569211)
        ·
          refine ⟨115669489901980904198353817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77112993267987269465569211 115669489901980904198353817)
          ·
            refine ⟨86752117426485678148765363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115669489901980904198353817 86752117426485678148765363)
            ·
              refine ⟨130128176139728517223148045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86752117426485678148765363 130128176139728517223148045)
              ·
                refine ⟨48798066052398193958680517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130128176139728517223148045 48798066052398193958680517)
                ·
                  refine ⟨9149637384824661367252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48798066052398193958680517 9149637384824661367252597)
                  ·
                    refine ⟨857778504827312003179931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9149637384824661367252597 857778504827312003179931)
                    ·
                      rfl

theorem cell23_5011553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_5011553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011553 prefixEnd_5011553 := by exact prefixLift 5011553
  have htrace : WordTrace (prefixWord ++ tailWord_5011553) baseStart_5011553 baseEnd_5011553 := by
    simpa [prefixWord, tailWord_5011553, baseEnd_5011553] using wordTrace_append hprefix tailTrace_5011553
  have hstable : (prefixWord ++ tailWord_5011553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011553).length < 2 ^ (prefixWord ++ tailWord_5011553).sum := by decide
  have hdescent : baseEnd_5011553 < baseStart_5011553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011604 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_5011604 : Nat := 118140960795 + 5011604 * 2 ^ 59
def prefixEnd_5011604 : Nat := 4983230072969 + 3 ^ 40 * 5011604 * 2
def baseEnd_5011604 : Nat := 857787233998438436667353

theorem tailTrace_5011604 : CollatzResearch.WordTrace tailWord_5011604 prefixEnd_5011604 857787233998438436667353 := by
  unfold tailWord_5011604
  simp only [CollatzResearch.WordTrace]
  refine ⟨91394107267911048332764933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121858809690548064443686577 91394107267911048332764933)
  ·
    refine ⟨17136395112733321562393425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91394107267911048332764933 17136395112733321562393425)
    ·
      refine ⟨12852296334549991171795069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17136395112733321562393425 12852296334549991171795069)
      ·
        refine ⟨4819611125456246689423151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12852296334549991171795069 4819611125456246689423151)
        ·
          refine ⟨7229416688184370034134727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819611125456246689423151 7229416688184370034134727)
          ·
            refine ⟨10844125032276555051202091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7229416688184370034134727 10844125032276555051202091)
            ·
              refine ⟨16266187548414832576803137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10844125032276555051202091 16266187548414832576803137)
              ·
                refine ⟨12199640661311124432602353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16266187548414832576803137 12199640661311124432602353)
                ·
                  refine ⟨9149730495983343324451765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12199640661311124432602353 9149730495983343324451765)
                  ·
                    refine ⟨857787233998438436667353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9149730495983343324451765 857787233998438436667353)
                    ·
                      rfl

theorem cell23_5011604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_5011604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011604 prefixEnd_5011604 := by exact prefixLift 5011604
  have htrace : WordTrace (prefixWord ++ tailWord_5011604) baseStart_5011604 baseEnd_5011604 := by
    simpa [prefixWord, tailWord_5011604, baseEnd_5011604] using wordTrace_append hprefix tailTrace_5011604
  have hstable : (prefixWord ++ tailWord_5011604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011604).length < 2 ^ (prefixWord ++ tailWord_5011604).sum := by decide
  have hdescent : baseEnd_5011604 < baseStart_5011604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011607 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_5011607 : Nat := 118140960795 + 5011607 * 2 ^ 59
def prefixEnd_5011607 : Nat := 4983230072969 + 3 ^ 40 * 5011607 * 2
def baseEnd_5011607 : Nat := 2573363242437278798264545

theorem tailTrace_5011607 : CollatzResearch.WordTrace tailWord_5011607 prefixEnd_5011607 2573363242437278798264545 := by
  unfold tailWord_5011607
  simp only [CollatzResearch.WordTrace]
  refine ⟨182788323954811228177889075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121858882636540818785259383 182788323954811228177889075)
  ·
    refine ⟨274182485932216842266833613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182788323954811228177889075 274182485932216842266833613)
    ·
      refine ⟨102818432224581315850062605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274182485932216842266833613 102818432224581315850062605)
      ·
        refine ⟨38556912084217993443773477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102818432224581315850062605 38556912084217993443773477)
        ·
          refine ⟨7229421015790873770707527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38556912084217993443773477 7229421015790873770707527)
          ·
            refine ⟨10844131523686310656061291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7229421015790873770707527 10844131523686310656061291)
            ·
              refine ⟨16266197285529465984091937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10844131523686310656061291 16266197285529465984091937)
              ·
                refine ⟨12199647964147099488068953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16266197285529465984091937 12199647964147099488068953)
                ·
                  refine ⟨9149735973110324616051715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12199647964147099488068953 9149735973110324616051715)
                  ·
                    refine ⟨13724603959665486924077573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9149735973110324616051715 13724603959665486924077573)
                    ·
                      refine ⟨2573363242437278798264545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13724603959665486924077573 2573363242437278798264545)
                      ·
                        rfl

theorem cell23_5011607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_5011607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011607 prefixEnd_5011607 := by exact prefixLift 5011607
  have htrace : WordTrace (prefixWord ++ tailWord_5011607) baseStart_5011607 baseEnd_5011607 := by
    simpa [prefixWord, tailWord_5011607, baseEnd_5011607] using wordTrace_append hprefix tailTrace_5011607
  have hstable : (prefixWord ++ tailWord_5011607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011607).length < 2 ^ (prefixWord ++ tailWord_5011607).sum := by decide
  have hdescent : baseEnd_5011607 < baseStart_5011607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011617 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_5011617 : Nat := 118140960795 + 5011617 * 2 ^ 59
def prefixEnd_5011617 : Nat := 4983230072969 + 3 ^ 40 * 5011617 * 2
def baseEnd_5011617 : Nat := 857789459081274586379833

theorem tailTrace_5011617 : CollatzResearch.WordTrace tailWord_5011617 prefixEnd_5011617 857789459081274586379833 := by
  unfold tailWord_5011617
  simp only [CollatzResearch.WordTrace]
  refine ⟨182788688684774999885753105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121859125789849999923835403 182788688684774999885753105)
  ·
    refine ⟨137091516513581249914314829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182788688684774999885753105 137091516513581249914314829)
    ·
      refine ⟨51409318692592968717868061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137091516513581249914314829 51409318692592968717868061)
      ·
        refine ⟨19278494509722363269200523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51409318692592968717868061 19278494509722363269200523)
        ·
          refine ⟨28917741764583544903800785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19278494509722363269200523 28917741764583544903800785)
          ·
            refine ⟨21688306323437658677850589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28917741764583544903800785 21688306323437658677850589)
            ·
              refine ⟨8133114871289122004193971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21688306323437658677850589 8133114871289122004193971)
              ·
                refine ⟨12199672306933683006290957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133114871289122004193971 12199672306933683006290957)
                ·
                  refine ⟨4574877115100131127359109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12199672306933683006290957 4574877115100131127359109)
                  ·
                    refine ⟨857789459081274586379833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4574877115100131127359109 857789459081274586379833)
                    ·
                      rfl

theorem cell23_5011617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_5011617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011617 prefixEnd_5011617 := by exact prefixLift 5011617
  have htrace : WordTrace (prefixWord ++ tailWord_5011617) baseStart_5011617 baseEnd_5011617 := by
    simpa [prefixWord, tailWord_5011617, baseEnd_5011617] using wordTrace_append hprefix tailTrace_5011617
  have hstable : (prefixWord ++ tailWord_5011617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011617).length < 2 ^ (prefixWord ++ tailWord_5011617).sum := by decide
  have hdescent : baseEnd_5011617 < baseStart_5011617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011644 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_5011644 : Nat := 118140960795 + 5011644 * 2 ^ 59
def prefixEnd_5011644 : Nat := 4983230072969 + 3 ^ 40 * 5011644 * 2
def baseEnd_5011644 : Nat := 2573382241221495153501875

theorem tailTrace_5011644 : CollatzResearch.WordTrace tailWord_5011644 prefixEnd_5011644 2573382241221495153501875 := by
  unfold tailWord_5011644
  simp only [CollatzResearch.WordTrace]
  refine ⟨91394836727838591748492993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121859782303784788997990657 91394836727838591748492993)
  ·
    refine ⟨68546127545878943811369745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91394836727838591748492993 68546127545878943811369745)
    ·
      refine ⟨51409595659409207858527309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68546127545878943811369745 51409595659409207858527309)
      ·
        refine ⟨19278598372278452946947741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51409595659409207858527309 19278598372278452946947741)
        ·
          refine ⟨7229474389604419855105403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19278598372278452946947741 7229474389604419855105403)
          ·
            refine ⟨10844211584406629782658105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7229474389604419855105403 10844211584406629782658105)
            ·
              refine ⟨8133158688304972336993579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10844211584406629782658105 8133158688304972336993579)
              ·
                refine ⟨12199738032457458505490369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133158688304972336993579 12199738032457458505490369)
                ·
                  refine ⟨9149803524343093879117777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12199738032457458505490369 9149803524343093879117777)
                  ·
                    refine ⟨6862352643257320409338333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9149803524343093879117777 6862352643257320409338333)
                    ·
                      refine ⟨2573382241221495153501875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6862352643257320409338333 2573382241221495153501875)
                      ·
                        rfl

theorem cell23_5011644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_5011644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011644 prefixEnd_5011644 := by exact prefixLift 5011644
  have htrace : WordTrace (prefixWord ++ tailWord_5011644) baseStart_5011644 baseEnd_5011644 := by
    simpa [prefixWord, tailWord_5011644, baseEnd_5011644] using wordTrace_append hprefix tailTrace_5011644
  have hstable : (prefixWord ++ tailWord_5011644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011644).length < 2 ^ (prefixWord ++ tailWord_5011644).sum := by decide
  have hdescent : baseEnd_5011644 < baseStart_5011644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011677 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5011677 : Nat := 118140960795 + 5011677 * 2 ^ 59
def prefixEnd_5011677 : Nat := 4983230072969 + 3 ^ 40 * 5011677 * 2
def baseEnd_5011677 : Nat := 857799728694364508129741

theorem tailTrace_5011677 : CollatzResearch.WordTrace tailWord_5011677 prefixEnd_5011677 857799728694364508129741 := by
  unfold tailWord_5011677
  simp only [CollatzResearch.WordTrace]
  refine ⟨182790877064557630132937285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121860584709705086755291523 182790877064557630132937285)
  ·
    refine ⟨34273289449604555649925741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182790877064557630132937285 34273289449604555649925741)
    ·
      refine ⟨12852483543601708368722153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34273289449604555649925741 12852483543601708368722153)
      ·
        refine ⟨9639362657701281276541615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12852483543601708368722153 9639362657701281276541615)
        ·
          refine ⟨14459043986551921914812423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639362657701281276541615 14459043986551921914812423)
          ·
            refine ⟨21688565979827882872218635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14459043986551921914812423 21688565979827882872218635)
            ·
              refine ⟨32532848969741824308327953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21688565979827882872218635 32532848969741824308327953)
              ·
                refine ⟨24399636727306368231245965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32532848969741824308327953 24399636727306368231245965)
                ·
                  refine ⟨9149863772739888086717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24399636727306368231245965 9149863772739888086717237)
                  ·
                    refine ⟨857799728694364508129741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9149863772739888086717237 857799728694364508129741)
                    ·
                      rfl

theorem cell23_5011677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5011677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011677 prefixEnd_5011677 := by exact prefixLift 5011677
  have htrace : WordTrace (prefixWord ++ tailWord_5011677) baseStart_5011677 baseEnd_5011677 := by
    simpa [prefixWord, tailWord_5011677, baseEnd_5011677] using wordTrace_append hprefix tailTrace_5011677
  have hstable : (prefixWord ++ tailWord_5011677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011677).length < 2 ^ (prefixWord ++ tailWord_5011677).sum := by decide
  have hdescent : baseEnd_5011677 < baseStart_5011677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011680 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_5011680 : Nat := 118140960795 + 5011680 * 2 ^ 59
def prefixEnd_5011680 : Nat := 4983230072969 + 3 ^ 40 * 5011680 * 2
def baseEnd_5011680 : Nat := 2573400726525057012651709

theorem tailTrace_5011680 : CollatzResearch.WordTrace tailWord_5011680 prefixEnd_5011680 2573400726525057012651709 := by
  unfold tailWord_5011680
  simp only [CollatzResearch.WordTrace]
  refine ⟨91395493241773380822648247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121860657655697841096864329 91395493241773380822648247)
  ·
    refine ⟨137093239862660071233972371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91395493241773380822648247 137093239862660071233972371)
    ·
      refine ⟨205639859793990106850958557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137093239862660071233972371 205639859793990106850958557)
      ·
        refine ⟨77114947422746290069109459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205639859793990106850958557 77114947422746290069109459)
        ·
          refine ⟨115672421134119435103664189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77114947422746290069109459 115672421134119435103664189)
          ·
            refine ⟨43377157925294788163874071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115672421134119435103664189 43377157925294788163874071)
            ·
              refine ⟨65065736887942182245811107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43377157925294788163874071 65065736887942182245811107)
              ·
                refine ⟨97598605331913273368716661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65065736887942182245811107 97598605331913273368716661)
                ·
                  refine ⟨9149869249866869378317187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97598605331913273368716661 9149869249866869378317187)
                  ·
                    refine ⟨13724803874800304067475781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9149869249866869378317187 13724803874800304067475781)
                    ·
                      refine ⟨2573400726525057012651709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13724803874800304067475781 2573400726525057012651709)
                      ·
                        rfl

theorem cell23_5011680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_5011680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011680 prefixEnd_5011680 := by exact prefixLift 5011680
  have htrace : WordTrace (prefixWord ++ tailWord_5011680) baseStart_5011680 baseEnd_5011680 := by
    simpa [prefixWord, tailWord_5011680, baseEnd_5011680] using wordTrace_append hprefix tailTrace_5011680
  have hstable : (prefixWord ++ tailWord_5011680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011680).length < 2 ^ (prefixWord ++ tailWord_5011680).sum := by decide
  have hdescent : baseEnd_5011680 < baseStart_5011680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011720 : List Nat := [2, 1, 3, 2, 3, 2, 10]
def baseStart_5011720 : Nat := 118140960795 + 5011720 * 2 ^ 59
def prefixEnd_5011720 : Nat := 4983230072969 + 3 ^ 40 * 5011720 * 2
def baseEnd_5011720 : Nat := 31770632910509096989525

theorem tailTrace_5011720 : CollatzResearch.WordTrace tailWord_5011720 prefixEnd_5011720 31770632910509096989525 := by
  unfold tailWord_5011720
  simp only [CollatzResearch.WordTrace]
  refine ⟨91396222701700924238376307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121861630268934565651168409 91396222701700924238376307)
  ·
    refine ⟨137094334052551386357564461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91396222701700924238376307 137094334052551386357564461)
    ·
      refine ⟨51410375269706769884086673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137094334052551386357564461 51410375269706769884086673)
      ·
        refine ⟨38557781452280077413065005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51410375269706769884086673 38557781452280077413065005)
        ·
          refine ⟨14459168044605029029899377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38557781452280077413065005 14459168044605029029899377)
          ·
            refine ⟨10844376033453771772424533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14459168044605029029899377 10844376033453771772424533)
            ·
              refine ⟨31770632910509096989525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10844376033453771772424533 31770632910509096989525)
              ·
                rfl

theorem cell23_5011720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 10].length) (baseStart_5011720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011720 prefixEnd_5011720 := by exact prefixLift 5011720
  have htrace : WordTrace (prefixWord ++ tailWord_5011720) baseStart_5011720 baseEnd_5011720 := by
    simpa [prefixWord, tailWord_5011720, baseEnd_5011720] using wordTrace_append hprefix tailTrace_5011720
  have hstable : (prefixWord ++ tailWord_5011720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011720).length < 2 ^ (prefixWord ++ tailWord_5011720).sum := by decide
  have hdescent : baseEnd_5011720 < baseStart_5011720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011741 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_5011741 : Nat := 118140960795 + 5011741 * 2 ^ 59
def prefixEnd_5011741 : Nat := 4983230072969 + 3 ^ 40 * 5011741 * 2
def baseEnd_5011741 : Nat := 857810682948327091329643

theorem tailTrace_5011741 : CollatzResearch.WordTrace tailWord_5011741 prefixEnd_5011741 857810682948327091329643 := by
  unfold tailWord_5011741
  simp only [CollatzResearch.WordTrace]
  refine ⟨182793211336325769063267077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121862140890883846042178051 182793211336325769063267077)
  ·
    refine ⟨34273727125561081699362577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182793211336325769063267077 34273727125561081699362577)
    ·
      refine ⟨25705295344170811274521933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34273727125561081699362577 25705295344170811274521933)
      ·
        refine ⟨9639485754064054227945725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25705295344170811274521933 9639485754064054227945725)
        ·
          refine ⟨3614807157774020335479647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9639485754064054227945725 3614807157774020335479647)
          ·
            refine ⟨5422210736661030503219471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614807157774020335479647 5422210736661030503219471)
            ·
              refine ⟨8133316104991545754829207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422210736661030503219471 8133316104991545754829207)
              ·
                refine ⟨12199974157487318632243811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133316104991545754829207 12199974157487318632243811)
                ·
                  refine ⟨18299961236230977948365717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12199974157487318632243811 18299961236230977948365717)
                  ·
                    refine ⟨857810682948327091329643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18299961236230977948365717 857810682948327091329643)
                    ·
                      rfl

theorem cell23_5011741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_5011741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011741 prefixEnd_5011741 := by exact prefixLift 5011741
  have htrace : WordTrace (prefixWord ++ tailWord_5011741) baseStart_5011741 baseEnd_5011741 := by
    simpa [prefixWord, tailWord_5011741, baseEnd_5011741] using wordTrace_append hprefix tailTrace_5011741
  have hstable : (prefixWord ++ tailWord_5011741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011741).length < 2 ^ (prefixWord ++ tailWord_5011741).sum := by decide
  have hdescent : baseEnd_5011741 < baseStart_5011741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011744 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5011744 : Nat := 118140960795 + 5011744 * 2 ^ 59
def prefixEnd_5011744 : Nat := 4983230072969 + 3 ^ 40 * 5011744 * 2
def baseEnd_5011744 : Nat := 2573433589286944762251415

theorem tailTrace_5011744 : CollatzResearch.WordTrace tailWord_5011744 prefixEnd_5011744 2573433589286944762251415 := by
  unfold tailWord_5011744
  simp only [CollatzResearch.WordTrace]
  refine ⟨91396660377657450287813143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121862213836876600383750857 91396660377657450287813143)
  ·
    refine ⟨137094990566486175431719715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91396660377657450287813143 137094990566486175431719715)
    ·
      refine ⟨205642485849729263147579573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137094990566486175431719715 205642485849729263147579573)
      ·
        refine ⟨19278983048412118420085585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205642485849729263147579573 19278983048412118420085585)
        ·
          refine ⟨14459237286309088815064189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19278983048412118420085585 14459237286309088815064189)
          ·
            refine ⟨5422213982365908305649071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14459237286309088815064189 5422213982365908305649071)
            ·
              refine ⟨8133320973548862458473607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422213982365908305649071 8133320973548862458473607)
              ·
                refine ⟨12199981460323293687710411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133320973548862458473607 12199981460323293687710411)
                ·
                  refine ⟨18299972190484940531565617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12199981460323293687710411 18299972190484940531565617)
                  ·
                    refine ⟨13724979142863705398674213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18299972190484940531565617 13724979142863705398674213)
                    ·
                      refine ⟨2573433589286944762251415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13724979142863705398674213 2573433589286944762251415)
                      ·
                        rfl

theorem cell23_5011744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5011744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011744 prefixEnd_5011744 := by exact prefixLift 5011744
  have htrace : WordTrace (prefixWord ++ tailWord_5011744) baseStart_5011744 baseEnd_5011744 := by
    simpa [prefixWord, tailWord_5011744, baseEnd_5011744] using wordTrace_append hprefix tailTrace_5011744
  have hstable : (prefixWord ++ tailWord_5011744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011744).length < 2 ^ (prefixWord ++ tailWord_5011744).sum := by decide
  have hdescent : baseEnd_5011744 < baseStart_5011744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011787 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 5, 4, 2]
def baseStart_5011787 : Nat := 118140960795 + 5011787 * 2 ^ 59
def prefixEnd_5011787 : Nat := 4983230072969 + 3 ^ 40 * 5011787 * 2
def baseEnd_5011787 : Nat := 2573455668955088094013717

theorem tailTrace_5011787 : CollatzResearch.WordTrace tailWord_5011787 prefixEnd_5011787 2573455668955088094013717 := by
  unfold tailWord_5011787
  simp only [CollatzResearch.WordTrace]
  refine ⟨182794889094159118919441615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121863259396106079279627743 182794889094159118919441615)
  ·
    refine ⟨274192333641238678379162423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182794889094159118919441615 274192333641238678379162423)
    ·
      refine ⟨411288500461858017568743635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274192333641238678379162423 411288500461858017568743635)
      ·
        refine ⟨616932750692787026353115453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411288500461858017568743635 616932750692787026353115453)
        ·
          refine ⟨231349781509795134882418295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616932750692787026353115453 231349781509795134882418295)
          ·
            refine ⟨347024672264692702323627443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231349781509795134882418295 347024672264692702323627443)
            ·
              refine ⟨520537008397039053485441165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347024672264692702323627443 520537008397039053485441165)
              ·
                refine ⟨195201378148889645057040437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520537008397039053485441165 195201378148889645057040437)
                ·
                  refine ⟨18300129201458404224097541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195201378148889645057040437 18300129201458404224097541)
                  ·
                    refine ⟨3431274225273450792018289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18300129201458404224097541 3431274225273450792018289)
                    ·
                      refine ⟨2573455668955088094013717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431274225273450792018289 2573455668955088094013717)
                      ·
                        rfl

theorem cell23_5011787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4, 2].length) (baseStart_5011787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011787 prefixEnd_5011787 := by exact prefixLift 5011787
  have htrace : WordTrace (prefixWord ++ tailWord_5011787) baseStart_5011787 baseEnd_5011787 := by
    simpa [prefixWord, tailWord_5011787, baseEnd_5011787] using wordTrace_append hprefix tailTrace_5011787
  have hstable : (prefixWord ++ tailWord_5011787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011787).length < 2 ^ (prefixWord ++ tailWord_5011787).sum := by decide
  have hdescent : baseEnd_5011787 < baseStart_5011787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011808 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2]
def baseStart_5011808 : Nat := 118140960795 + 5011808 * 2 ^ 59
def prefixEnd_5011808 : Nat := 4983230072969 + 3 ^ 40 * 5011808 * 2
def baseEnd_5011808 : Nat := 2573466452048832511851121

theorem tailTrace_5011808 : CollatzResearch.WordTrace tailWord_5011808 prefixEnd_5011808 2573466452048832511851121 := by
  unfold tailWord_5011808
  simp only [CollatzResearch.WordTrace]
  refine ⟨91397827513541519752978039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121863770018055359670637385 91397827513541519752978039)
  ·
    refine ⟨137096741270312279629467059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91397827513541519752978039 137096741270312279629467059)
    ·
      refine ⟨205645111905468419444200589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137096741270312279629467059 205645111905468419444200589)
      ·
        refine ⟨77116916964550657291575221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205645111905468419444200589 77116916964550657291575221)
        ·
          refine ⟨7229710965426624121085177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77116916964550657291575221 7229710965426624121085177)
          ·
            refine ⟨5422283224069968090813883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7229710965426624121085177 5422283224069968090813883)
            ·
              refine ⟨8133424836104952136220825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422283224069968090813883 8133424836104952136220825)
              ·
                refine ⟨6100068627078714102165619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8133424836104952136220825 6100068627078714102165619)
                ·
                  refine ⟨9150102940618071153248429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100068627078714102165619 9150102940618071153248429)
                  ·
                    refine ⟨3431288602731776682468161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9150102940618071153248429 3431288602731776682468161)
                    ·
                      refine ⟨2573466452048832511851121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431288602731776682468161 2573466452048832511851121)
                      ·
                        rfl

theorem cell23_5011808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_5011808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011808 prefixEnd_5011808 := by exact prefixLift 5011808
  have htrace : WordTrace (prefixWord ++ tailWord_5011808) baseStart_5011808 baseEnd_5011808 := by
    simpa [prefixWord, tailWord_5011808, baseEnd_5011808] using wordTrace_append hprefix tailTrace_5011808
  have hstable : (prefixWord ++ tailWord_5011808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011808).length < 2 ^ (prefixWord ++ tailWord_5011808).sum := by decide
  have hdescent : baseEnd_5011808 < baseStart_5011808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011840 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_5011840 : Nat := 118140960795 + 5011840 * 2 ^ 59
def prefixEnd_5011840 : Nat := 4983230072969 + 3 ^ 40 * 5011840 * 2
def baseEnd_5011840 : Nat := 857827627809925462216991

theorem tailTrace_5011840 : CollatzResearch.WordTrace tailWord_5011840 prefixEnd_5011840 857827627809925462216991 := by
  unfold tailWord_5011840
  simp only [CollatzResearch.WordTrace]
  refine ⟨91398411081483554485560487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121864548108644739314080649 91398411081483554485560487)
  ·
    refine ⟨137097616622225331728340731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91398411081483554485560487 137097616622225331728340731)
    ·
      refine ⟨205646424933337997592511097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137097616622225331728340731 205646424933337997592511097)
      ·
        refine ⟨154234818700003498194383323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205646424933337997592511097 154234818700003498194383323)
        ·
          refine ⟨231352228050005247291574985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154234818700003498194383323 231352228050005247291574985)
          ·
            refine ⟨173514171037503935468681239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231352228050005247291574985 173514171037503935468681239)
            ·
              refine ⟨260271256556255903203021859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173514171037503935468681239 260271256556255903203021859)
              ·
                refine ⟨390406884834383854804532789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260271256556255903203021859 390406884834383854804532789)
                ·
                  refine ⟨36600645453223486387924949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390406884834383854804532789 36600645453223486387924949)
                  ·
                    refine ⟨857827627809925462216991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36600645453223486387924949 857827627809925462216991)
                    ·
                      rfl

theorem cell23_5011840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_5011840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011840 prefixEnd_5011840 := by exact prefixLift 5011840
  have htrace : WordTrace (prefixWord ++ tailWord_5011840) baseStart_5011840 baseEnd_5011840 := by
    simpa [prefixWord, tailWord_5011840, baseEnd_5011840] using wordTrace_append hprefix tailTrace_5011840
  have hstable : (prefixWord ++ tailWord_5011840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011840).length < 2 ^ (prefixWord ++ tailWord_5011840).sum := by decide
  have hdescent : baseEnd_5011840 < baseStart_5011840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011844 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 5]
def baseStart_5011844 : Nat := 118140960795 + 5011844 * 2 ^ 59
def prefixEnd_5011844 : Nat := 4983230072969 + 3 ^ 40 * 5011844 * 2
def baseEnd_5011844 : Nat := 285942770816932707888995

theorem tailTrace_5011844 : CollatzResearch.WordTrace tailWord_5011844 prefixEnd_5011844 285942770816932707888995 := by
  unfold tailWord_5011844
  simp only [CollatzResearch.WordTrace]
  refine ⟨91398484027476308827133293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121864645369968411769511057 91398484027476308827133293)
  ·
    refine ⟨34274431510303615810174985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91398484027476308827133293 34274431510303615810174985)
    ·
      refine ⟨25705823632727711857631239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34274431510303615810174985 25705823632727711857631239)
      ·
        refine ⟨38558735449091567786446859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25705823632727711857631239 38558735449091567786446859)
        ·
          refine ⟨57838103173637351679670289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38558735449091567786446859 57838103173637351679670289)
          ·
            refine ⟨43378577380228013759752717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57838103173637351679670289 43378577380228013759752717)
            ·
              refine ⟨16266966517585505159907269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43378577380228013759752717 16266966517585505159907269)
              ·
                refine ⟨3050056222047282217482613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16266966517585505159907269 3050056222047282217482613)
                ·
                  refine ⟨285942770816932707888995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3050056222047282217482613 285942770816932707888995)
                  ·
                    rfl

theorem cell23_5011844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_5011844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011844 prefixEnd_5011844 := by exact prefixLift 5011844
  have htrace : WordTrace (prefixWord ++ tailWord_5011844) baseStart_5011844 baseEnd_5011844 := by
    simpa [prefixWord, tailWord_5011844, baseEnd_5011844] using wordTrace_append hprefix tailTrace_5011844
  have hstable : (prefixWord ++ tailWord_5011844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011844).length < 2 ^ (prefixWord ++ tailWord_5011844).sum := by decide
  have hdescent : baseEnd_5011844 < baseStart_5011844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011854 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5011854 : Nat := 118140960795 + 5011854 * 2 ^ 59
def prefixEnd_5011854 : Nat := 4983230072969 + 3 ^ 40 * 5011854 * 2
def baseEnd_5011854 : Nat := 2573490072158939331875909

theorem tailTrace_5011854 : CollatzResearch.WordTrace tailWord_5011854 prefixEnd_5011854 2573490072158939331875909 := by
  unfold tailWord_5011854
  simp only [CollatzResearch.WordTrace]
  refine ⟨22849666598114548670266327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121864888523277592908087077 22849666598114548670266327)
  ·
    refine ⟨34274499897171823005399491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22849666598114548670266327 34274499897171823005399491)
    ·
      refine ⟨51411749845757734508099237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34274499897171823005399491 51411749845757734508099237)
      ·
        refine ⟨9639703096079575220268607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51411749845757734508099237 9639703096079575220268607)
        ·
          refine ⟨14459554644119362830402911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639703096079575220268607 14459554644119362830402911)
          ·
            refine ⟨21689331966179044245604367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14459554644119362830402911 21689331966179044245604367)
            ·
              refine ⟨32533997949268566368406551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21689331966179044245604367 32533997949268566368406551)
              ·
                refine ⟨48800996923902849552609827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32533997949268566368406551 48800996923902849552609827)
                ·
                  refine ⟨73201495385854274328914741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48800996923902849552609827 73201495385854274328914741)
                  ·
                    refine ⟨6862640192423838218335757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73201495385854274328914741 6862640192423838218335757)
                    ·
                      refine ⟨2573490072158939331875909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6862640192423838218335757 2573490072158939331875909)
                      ·
                        rfl

theorem cell23_5011854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5011854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011854 prefixEnd_5011854 := by exact prefixLift 5011854
  have htrace : WordTrace (prefixWord ++ tailWord_5011854) baseStart_5011854 baseEnd_5011854 := by
    simpa [prefixWord, tailWord_5011854, baseEnd_5011854] using wordTrace_append hprefix tailTrace_5011854
  have hstable : (prefixWord ++ tailWord_5011854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011854).length < 2 ^ (prefixWord ++ tailWord_5011854).sum := by decide
  have hdescent : baseEnd_5011854 < baseStart_5011854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011877 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_5011877 : Nat := 118140960795 + 5011877 * 2 ^ 59
def prefixEnd_5011877 : Nat := 4983230072969 + 3 ^ 40 * 5011877 * 2
def baseEnd_5011877 : Nat := 2573501882213992741888303

theorem tailTrace_5011877 : CollatzResearch.WordTrace tailWord_5011877 prefixEnd_5011877 2573501882213992741888303 := by
  unfold tailWord_5011877
  simp only [CollatzResearch.WordTrace]
  refine ⟨182798171663833064290217885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121865447775888709526811923 182798171663833064290217885)
  ·
    refine ⟨68549314373937399108831707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182798171663833064290217885 68549314373937399108831707)
    ·
      refine ⟨102823971560906098663247561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68549314373937399108831707 102823971560906098663247561)
      ·
        refine ⟨77117978670679573997435671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102823971560906098663247561 77117978670679573997435671)
        ·
          refine ⟨115676968006019360996153507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77117978670679573997435671 115676968006019360996153507)
          ·
            refine ⟨173515452009029041494230261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115676968006019360996153507 173515452009029041494230261)
            ·
              refine ⟨16267073625846472640084087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173515452009029041494230261 16267073625846472640084087)
              ·
                refine ⟨24400610438769708960126131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16267073625846472640084087 24400610438769708960126131)
                ·
                  refine ⟨36600915658154563440189197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24400610438769708960126131 36600915658154563440189197)
                  ·
                    refine ⟨13725343371807961290070949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36600915658154563440189197 13725343371807961290070949)
                    ·
                      refine ⟨2573501882213992741888303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13725343371807961290070949 2573501882213992741888303)
                      ·
                        rfl

theorem cell23_5011877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_5011877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011877 prefixEnd_5011877 := by exact prefixLift 5011877
  have htrace : WordTrace (prefixWord ++ tailWord_5011877) baseStart_5011877 baseEnd_5011877 := by
    simpa [prefixWord, tailWord_5011877, baseEnd_5011877] using wordTrace_append hprefix tailTrace_5011877
  have hstable : (prefixWord ++ tailWord_5011877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011877).length < 2 ^ (prefixWord ++ tailWord_5011877).sum := by decide
  have hdescent : baseEnd_5011877 < baseStart_5011877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011961 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 3]
def baseStart_5011961 : Nat := 118140960795 + 5011961 * 2 ^ 59
def prefixEnd_5011961 : Nat := 4983230072969 + 3 ^ 40 * 5011961 * 2
def baseEnd_5011961 : Nat := 2573545014588970413237917

theorem tailTrace_5011961 : CollatzResearch.WordTrace tailWord_5011961 prefixEnd_5011961 2573545014588970413237917 := by
  unfold tailWord_5011961
  simp only [CollatzResearch.WordTrace]
  refine ⟨182801235395528746636275737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121867490263685831090850491 182801235395528746636275737)
  ·
    refine ⟨137100926546646559977206803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182801235395528746636275737 137100926546646559977206803)
    ·
      refine ⟨205651389819969839965810205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137100926546646559977206803 205651389819969839965810205)
      ·
        refine ⟨77119271182488689987178827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205651389819969839965810205 77119271182488689987178827)
        ·
          refine ⟨115678906773733034980768241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77119271182488689987178827 115678906773733034980768241)
          ·
            refine ⟨86759180080299776235576181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115678906773733034980768241 86759180080299776235576181)
            ·
              refine ⟨8133673132528104022085267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86759180080299776235576181 8133673132528104022085267)
              ·
                refine ⟨12200509698792156033127901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133673132528104022085267 12200509698792156033127901)
                ·
                  refine ⟨4575191137047058512422963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12200509698792156033127901 4575191137047058512422963)
                  ·
                    refine ⟨6862786705570587768634445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575191137047058512422963 6862786705570587768634445)
                    ·
                      refine ⟨2573545014588970413237917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6862786705570587768634445 2573545014588970413237917)
                      ·
                        rfl

theorem cell23_5011961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_5011961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011961 prefixEnd_5011961 := by exact prefixLift 5011961
  have htrace : WordTrace (prefixWord ++ tailWord_5011961) baseStart_5011961 baseEnd_5011961 := by
    simpa [prefixWord, tailWord_5011961, baseEnd_5011961] using wordTrace_append hprefix tailTrace_5011961
  have hstable : (prefixWord ++ tailWord_5011961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011961).length < 2 ^ (prefixWord ++ tailWord_5011961).sum := by decide
  have hdescent : baseEnd_5011961 < baseStart_5011961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5011994 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_5011994 : Nat := 118140960795 + 5011994 * 2 ^ 59
def prefixEnd_5011994 : Nat := 4983230072969 + 3 ^ 40 * 5011994 * 2
def baseEnd_5011994 : Nat := 857853986483522928041755

theorem tailTrace_5011994 : CollatzResearch.WordTrace tailWord_5011994 prefixEnd_5011994 857853986483522928041755 := by
  unfold tailWord_5011994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45700609751102298318056759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121868292669606128848151357 45700609751102298318056759)
  ·
    refine ⟨68550914626653447477085139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45700609751102298318056759 68550914626653447477085139)
    ·
      refine ⟨102826371939980171215627709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68550914626653447477085139 102826371939980171215627709)
      ·
        refine ⟨38559889477492564205860391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102826371939980171215627709 38559889477492564205860391)
        ·
          refine ⟨57839834216238846308790587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38559889477492564205860391 57839834216238846308790587)
          ·
            refine ⟨86759751324358269463185881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57839834216238846308790587 86759751324358269463185881)
            ·
              refine ⟨65069813493268702097389411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86759751324358269463185881 65069813493268702097389411)
              ·
                refine ⟨97604720239903053146084117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65069813493268702097389411 97604720239903053146084117)
                ·
                  refine ⟨4575221261245455616222693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97604720239903053146084117 4575221261245455616222693)
                  ·
                    refine ⟨857853986483522928041755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575221261245455616222693 857853986483522928041755)
                    ·
                      rfl

theorem cell23_5011994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_5011994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5011994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5011994 prefixEnd_5011994 := by exact prefixLift 5011994
  have htrace : WordTrace (prefixWord ++ tailWord_5011994) baseStart_5011994 baseEnd_5011994 := by
    simpa [prefixWord, tailWord_5011994, baseEnd_5011994] using wordTrace_append hprefix tailTrace_5011994
  have hstable : (prefixWord ++ tailWord_5011994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5011994).length < 2 ^ (prefixWord ++ tailWord_5011994).sum := by decide
  have hdescent : baseEnd_5011994 < baseStart_5011994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5011994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012052 : List Nat := [2, 4, 1, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_5012052 : Nat := 118140960795 + 5012052 * 2 ^ 59
def prefixEnd_5012052 : Nat := 4983230072969 + 3 ^ 40 * 5012052 * 2
def baseEnd_5012052 : Nat := 2573591741328529557199999

theorem tailTrace_5012052 : CollatzResearch.WordTrace tailWord_5012052 prefixEnd_5012052 2573591741328529557199999 := by
  unfold tailWord_5012052
  simp only [CollatzResearch.WordTrace]
  refine ⟨91402277219099534588919205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121869702958799379451892273 91402277219099534588919205)
  ·
    refine ⟨17137926978581162735422351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91402277219099534588919205 17137926978581162735422351)
    ·
      refine ⟨25706890467871744103133527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17137926978581162735422351 25706890467871744103133527)
      ·
        refine ⟨38560335701807616154700291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25706890467871744103133527 38560335701807616154700291)
        ·
          refine ⟨57840503552711424232050437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38560335701807616154700291 57840503552711424232050437)
          ·
            refine ⟨10845094416133392043509457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57840503552711424232050437 10845094416133392043509457)
            ·
              refine ⟨8133820812100044032632093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10845094416133392043509457 8133820812100044032632093)
              ·
                refine ⟨3050182804537516512237035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8133820812100044032632093 3050182804537516512237035)
                ·
                  refine ⟨4575274206806274768355553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050182804537516512237035 4575274206806274768355553)
                  ·
                    refine ⟨3431455655104706076266665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4575274206806274768355553 3431455655104706076266665)
                    ·
                      refine ⟨2573591741328529557199999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431455655104706076266665 2573591741328529557199999)
                      ·
                        rfl

theorem cell23_5012052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_5012052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012052 prefixEnd_5012052 := by exact prefixLift 5012052
  have htrace : WordTrace (prefixWord ++ tailWord_5012052) baseStart_5012052 baseEnd_5012052 := by
    simpa [prefixWord, tailWord_5012052, baseEnd_5012052] using wordTrace_append hprefix tailTrace_5012052
  have hstable : (prefixWord ++ tailWord_5012052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012052).length < 2 ^ (prefixWord ++ tailWord_5012052).sum := by decide
  have hdescent : baseEnd_5012052 < baseStart_5012052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012062 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5012062 : Nat := 118140960795 + 5012062 * 2 ^ 59
def prefixEnd_5012062 : Nat := 4983230072969 + 3 ^ 40 * 5012062 * 2
def baseEnd_5012062 : Nat := 857865625378358172691651

theorem tailTrace_5012062 : CollatzResearch.WordTrace tailWord_5012062 prefixEnd_5012062 857865625378358172691651 := by
  unfold tailWord_5012062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850614896020355110712805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121869946112108560590468293 22850614896020355110712805)
  ·
    refine ⟨4284490293003816583258651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22850614896020355110712805 4284490293003816583258651)
    ·
      refine ⟨6426735439505724874887977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284490293003816583258651 6426735439505724874887977)
      ·
        refine ⟨4820051579629293656165983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6426735439505724874887977 4820051579629293656165983)
        ·
          refine ⟨7230077369443940484248975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820051579629293656165983 7230077369443940484248975)
          ·
            refine ⟨10845116054165910726373463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7230077369443940484248975 10845116054165910726373463)
            ·
              refine ⟨16267674081248866089560195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10845116054165910726373463 16267674081248866089560195)
              ·
                refine ⟨24401511121873299134340293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16267674081248866089560195 24401511121873299134340293)
                ·
                  refine ⟨4575283335351243587688805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24401511121873299134340293 4575283335351243587688805)
                  ·
                    refine ⟨857865625378358172691651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575283335351243587688805 857865625378358172691651)
                    ·
                      rfl

theorem cell23_5012062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5012062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012062 prefixEnd_5012062 := by exact prefixLift 5012062
  have htrace : WordTrace (prefixWord ++ tailWord_5012062) baseStart_5012062 baseEnd_5012062 := by
    simpa [prefixWord, tailWord_5012062, baseEnd_5012062] using wordTrace_append hprefix tailTrace_5012062
  have hstable : (prefixWord ++ tailWord_5012062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012062).length < 2 ^ (prefixWord ++ tailWord_5012062).sum := by decide
  have hdescent : baseEnd_5012062 < baseStart_5012062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012085 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5012085 : Nat := 118140960795 + 5012085 * 2 ^ 59
def prefixEnd_5012085 : Nat := 4983230072969 + 3 ^ 40 * 5012085 * 2
def baseEnd_5012085 : Nat := 2573608686190127928087347

theorem tailTrace_5012085 : CollatzResearch.WordTrace tailWord_5012085 prefixEnd_5012085 2573608686190127928087347 := by
  unfold tailWord_5012085
  simp only [CollatzResearch.WordTrace]
  refine ⟨182805758047079515813789709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121870505364719677209193139 182805758047079515813789709)
  ·
    refine ⟨68552159267654818430171141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182805758047079515813789709 68552159267654818430171141)
    ·
      refine ⟨12853529862685278455657089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68552159267654818430171141 12853529862685278455657089)
      ·
        refine ⟨9640147397013958841742817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12853529862685278455657089 9640147397013958841742817)
        ·
          refine ⟨7230110547760469131307113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640147397013958841742817 7230110547760469131307113)
          ·
            refine ⟨5422582910820351848480335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230110547760469131307113 5422582910820351848480335)
            ·
              refine ⟨8133874366230527772720503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422582910820351848480335 8133874366230527772720503)
              ·
                refine ⟨12200811549345791659080755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8133874366230527772720503 12200811549345791659080755)
                ·
                  refine ⟨18301217324018687488621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12200811549345791659080755 18301217324018687488621133)
                  ·
                    refine ⟨6862956496507007808232925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18301217324018687488621133 6862956496507007808232925)
                    ·
                      refine ⟨2573608686190127928087347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6862956496507007808232925 2573608686190127928087347)
                      ·
                        rfl

theorem cell23_5012085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5012085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012085 prefixEnd_5012085 := by exact prefixLift 5012085
  have htrace : WordTrace (prefixWord ++ tailWord_5012085) baseStart_5012085 baseEnd_5012085 := by
    simpa [prefixWord, tailWord_5012085, baseEnd_5012085] using wordTrace_append hprefix tailTrace_5012085
  have hstable : (prefixWord ++ tailWord_5012085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012085).length < 2 ^ (prefixWord ++ tailWord_5012085).sum := by decide
  have hdescent : baseEnd_5012085 < baseStart_5012085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012091 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 1, 4, 2]
def baseStart_5012091 : Nat := 118140960795 + 5012091 * 2 ^ 59
def prefixEnd_5012091 : Nat := 4983230072969 + 3 ^ 40 * 5012091 * 2
def baseEnd_5012091 : Nat := 2573611767074054904612319

theorem tailTrace_5012091 : CollatzResearch.WordTrace tailWord_5012091 prefixEnd_5012091 2573611767074054904612319 := by
  unfold tailWord_5012091
  simp only [CollatzResearch.WordTrace]
  refine ⟨182805976885057778838508127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121870651256705185892338751 182805976885057778838508127)
  ·
    refine ⟨274208965327586668257762191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182805976885057778838508127 274208965327586668257762191)
    ·
      refine ⟨411313447991380002386643287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274208965327586668257762191 411313447991380002386643287)
      ·
        refine ⟨616970171987070003579964931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411313447991380002386643287 616970171987070003579964931)
        ·
          refine ⟨925455257980605005369947397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616970171987070003579964931 925455257980605005369947397)
          ·
            refine ⟨173522860871363438506865137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 925455257980605005369947397 173522860871363438506865137)
            ·
              refine ⟨130142145653522578880148853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173522860871363438506865137 130142145653522578880148853)
              ·
                refine ⟨12200826155017741770013955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130142145653522578880148853 12200826155017741770013955)
                ·
                  refine ⟨18301239232526612655020933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12200826155017741770013955 18301239232526612655020933)
                  ·
                    refine ⟨3431482356098739872816425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18301239232526612655020933 3431482356098739872816425)
                    ·
                      refine ⟨2573611767074054904612319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431482356098739872816425 2573611767074054904612319)
                      ·
                        rfl

theorem cell23_5012091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4, 2].length) (baseStart_5012091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012091 prefixEnd_5012091 := by exact prefixLift 5012091
  have htrace : WordTrace (prefixWord ++ tailWord_5012091) baseStart_5012091 baseEnd_5012091 := by
    simpa [prefixWord, tailWord_5012091, baseEnd_5012091] using wordTrace_append hprefix tailTrace_5012091
  have hstable : (prefixWord ++ tailWord_5012091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012091).length < 2 ^ (prefixWord ++ tailWord_5012091).sum := by decide
  have hdescent : baseEnd_5012091 < baseStart_5012091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012144 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_5012144 : Nat := 118140960795 + 5012144 * 2 ^ 59
def prefixEnd_5012144 : Nat := 4983230072969 + 3 ^ 40 * 5012144 * 2
def baseEnd_5012144 : Nat := 857879660516247732416525

theorem tailTrace_5012144 : CollatzResearch.WordTrace tailWord_5012144 prefixEnd_5012144 857879660516247732416525 := by
  unfold tailWord_5012144
  simp only [CollatzResearch.WordTrace]
  refine ⟨91403954976932884445093743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121871939969243845926791657 91403954976932884445093743)
  ·
    refine ⟨137105932465399326667640615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91403954976932884445093743 137105932465399326667640615)
    ·
      refine ⟨205658898698098990001460923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137105932465399326667640615 205658898698098990001460923)
      ·
        refine ⟨308488348047148485002191385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205658898698098990001460923 308488348047148485002191385)
        ·
          refine ⟨231366261035361363751643539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308488348047148485002191385 231366261035361363751643539)
          ·
            refine ⟨347049391553042045627465309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231366261035361363751643539 347049391553042045627465309)
            ·
              refine ⟨130143521832390767110299491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347049391553042045627465309 130143521832390767110299491)
              ·
                refine ⟨195215282748586150665449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130143521832390767110299491 195215282748586150665449237)
                ·
                  refine ⟨9150716378839975812442933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195215282748586150665449237 9150716378839975812442933)
                  ·
                    refine ⟨857879660516247732416525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9150716378839975812442933 857879660516247732416525)
                    ·
                      rfl

theorem cell23_5012144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_5012144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012144 prefixEnd_5012144 := by exact prefixLift 5012144
  have htrace : WordTrace (prefixWord ++ tailWord_5012144) baseStart_5012144 baseEnd_5012144 := by
    simpa [prefixWord, tailWord_5012144, baseEnd_5012144] using wordTrace_append hprefix tailTrace_5012144
  have hstable : (prefixWord ++ tailWord_5012144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012144).length < 2 ^ (prefixWord ++ tailWord_5012144).sum := by decide
  have hdescent : baseEnd_5012144 < baseStart_5012144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012154 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_5012154 : Nat := 118140960795 + 5012154 * 2 ^ 59
def prefixEnd_5012154 : Nat := 4983230072969 + 3 ^ 40 * 5012154 * 2
def baseEnd_5012154 : Nat := 2573644116355288158124529

theorem tailTrace_5012154 : CollatzResearch.WordTrace tailWord_5012154 prefixEnd_5012154 2573644116355288158124529 := by
  unfold tailWord_5012154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45702068670957385149512879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121872183122553027065367677 45702068670957385149512879)
  ·
    refine ⟨68553103006436077724269319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45702068670957385149512879 68553103006436077724269319)
    ·
      refine ⟨102829654509654116586403979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68553103006436077724269319 102829654509654116586403979)
      ·
        refine ⟨154244481764481174879605969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102829654509654116586403979 154244481764481174879605969)
        ·
          refine ⟨115683361323360881159704477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154244481764481174879605969 115683361323360881159704477)
          ·
            refine ⟨43381260496260330434889179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115683361323360881159704477 43381260496260330434889179)
            ·
              refine ⟨65071890744390495652333769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43381260496260330434889179 65071890744390495652333769)
              ·
                refine ⟨48803918058292871739250327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65071890744390495652333769 48803918058292871739250327)
                ·
                  refine ⟨73205877087439307608875491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48803918058292871739250327 73205877087439307608875491)
                  ·
                    refine ⟨109808815631158961413313237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73205877087439307608875491 109808815631158961413313237)
                    ·
                      refine ⟨2573644116355288158124529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109808815631158961413313237 2573644116355288158124529)
                      ·
                        rfl

theorem cell23_5012154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_5012154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012154 prefixEnd_5012154 := by exact prefixLift 5012154
  have htrace : WordTrace (prefixWord ++ tailWord_5012154) baseStart_5012154 baseEnd_5012154 := by
    simpa [prefixWord, tailWord_5012154, baseEnd_5012154] using wordTrace_append hprefix tailTrace_5012154
  have hstable : (prefixWord ++ tailWord_5012154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012154).length < 2 ^ (prefixWord ++ tailWord_5012154).sum := by decide
  have hdescent : baseEnd_5012154 < baseStart_5012154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012188 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5012188 : Nat := 118140960795 + 5012188 * 2 ^ 59
def prefixEnd_5012188 : Nat := 4983230072969 + 3 ^ 40 * 5012188 * 2
def baseEnd_5012188 : Nat := 2573661574697541025099373

theorem tailTrace_5012188 : CollatzResearch.WordTrace tailWord_5012188 prefixEnd_5012188 2573661574697541025099373 := by
  unfold tailWord_5012188
  simp only [CollatzResearch.WordTrace]
  refine ⟨91404757382853182202394609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121873009843804242936526145 91404757382853182202394609)
  ·
    refine ⟨68553568037139886651795957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91404757382853182202394609 68553568037139886651795957)
    ·
      refine ⟨6426897003481864373605871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68553568037139886651795957 6426897003481864373605871)
      ·
        refine ⟨9640345505222796560408807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426897003481864373605871 9640345505222796560408807)
        ·
          refine ⟨14460518257834194840613211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640345505222796560408807 14460518257834194840613211)
          ·
            refine ⟨21690777386751292260919817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14460518257834194840613211 21690777386751292260919817)
            ·
              refine ⟨16268083040063469195689863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21690777386751292260919817 16268083040063469195689863)
              ·
                refine ⟨24402124560095203793534795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16268083040063469195689863 24402124560095203793534795)
                ·
                  refine ⟨36603186840142805690302193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24402124560095203793534795 36603186840142805690302193)
                  ·
                    refine ⟨27452390130107104267726645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36603186840142805690302193 27452390130107104267726645)
                    ·
                      refine ⟨2573661574697541025099373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27452390130107104267726645 2573661574697541025099373)
                      ·
                        rfl

theorem cell23_5012188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5012188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012188 prefixEnd_5012188 := by exact prefixLift 5012188
  have htrace : WordTrace (prefixWord ++ tailWord_5012188) baseStart_5012188 baseEnd_5012188 := by
    simpa [prefixWord, tailWord_5012188, baseEnd_5012188] using wordTrace_append hprefix tailTrace_5012188
  have hstable : (prefixWord ++ tailWord_5012188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012188).length < 2 ^ (prefixWord ++ tailWord_5012188).sum := by decide
  have hdescent : baseEnd_5012188 < baseStart_5012188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012201 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_5012201 : Nat := 118140960795 + 5012201 * 2 ^ 59
def prefixEnd_5012201 : Nat := 4983230072969 + 3 ^ 40 * 5012201 * 2
def baseEnd_5012201 : Nat := 2573668249946049474236813

theorem tailTrace_5012201 : CollatzResearch.WordTrace tailWord_5012201 prefixEnd_5012201 2573668249946049474236813 := by
  unfold tailWord_5012201
  simp only [CollatzResearch.WordTrace]
  refine ⟨182809988914659267625012457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121873325943106178416674971 182809988914659267625012457)
  ·
    refine ⟨137107491685994450718759343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182809988914659267625012457 137107491685994450718759343)
    ·
      refine ⟨205661237528991676078139015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137107491685994450718759343 205661237528991676078139015)
      ·
        refine ⟨308491856293487514117208523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205661237528991676078139015 308491856293487514117208523)
        ·
          refine ⟨462737784440231271175812785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308491856293487514117208523 462737784440231271175812785)
          ·
            refine ⟨347053338330173453381859589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462737784440231271175812785 347053338330173453381859589)
            ·
              refine ⟨65072500936907522509098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 347053338330173453381859589 65072500936907522509098673)
              ·
                refine ⟨48804375702680641881824005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65072500936907522509098673 48804375702680641881824005)
                ·
                  refine ⟨9150820444252620352842001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48804375702680641881824005 9150820444252620352842001)
                  ·
                    refine ⟨6863115333189465264631501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9150820444252620352842001 6863115333189465264631501)
                    ·
                      refine ⟨2573668249946049474236813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863115333189465264631501 2573668249946049474236813)
                      ·
                        rfl

theorem cell23_5012201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_5012201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012201 prefixEnd_5012201 := by exact prefixLift 5012201
  have htrace : WordTrace (prefixWord ++ tailWord_5012201) baseStart_5012201 baseEnd_5012201 := by
    simpa [prefixWord, tailWord_5012201, baseEnd_5012201] using wordTrace_append hprefix tailTrace_5012201
  have hstable : (prefixWord ++ tailWord_5012201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012201).length < 2 ^ (prefixWord ++ tailWord_5012201).sum := by decide
  have hdescent : baseEnd_5012201 < baseStart_5012201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012204 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 10]
def baseStart_5012204 : Nat := 118140960795 + 5012204 * 2 ^ 59
def prefixEnd_5012204 : Nat := 4983230072969 + 3 ^ 40 * 5012204 * 2
def baseEnd_5012204 : Nat := 285963310043112551388811

theorem tailTrace_5012204 : CollatzResearch.WordTrace tailWord_5012204 prefixEnd_5012204 285963310043112551388811 := by
  unfold tailWord_5012204
  simp only [CollatzResearch.WordTrace]
  refine ⟨91405049166824199568685833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121873398889098932758247777 91405049166824199568685833)
  ·
    refine ⟨68553786875118149676514375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91405049166824199568685833 68553786875118149676514375)
    ·
      refine ⟨102830680312677224514771563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68553786875118149676514375 102830680312677224514771563)
      ·
        refine ⟨154246020469015836772157345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102830680312677224514771563 154246020469015836772157345)
        ·
          refine ⟨115684515351761877579118009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154246020469015836772157345 115684515351761877579118009)
          ·
            refine ⟨86763386513821408184338507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115684515351761877579118009 86763386513821408184338507)
            ·
              refine ⟨130145079770732112276507761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86763386513821408184338507 130145079770732112276507761)
              ·
                refine ⟨97608809828049084207380821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130145079770732112276507761 97608809828049084207380821)
                ·
                  refine ⟨285963310043112551388811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97608809828049084207380821 285963310043112551388811)
                  ·
                    rfl

theorem cell23_5012204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_5012204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012204 prefixEnd_5012204 := by exact prefixLift 5012204
  have htrace : WordTrace (prefixWord ++ tailWord_5012204) baseStart_5012204 baseEnd_5012204 := by
    simpa [prefixWord, tailWord_5012204, baseEnd_5012204] using wordTrace_append hprefix tailTrace_5012204
  have hstable : (prefixWord ++ tailWord_5012204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012204).length < 2 ^ (prefixWord ++ tailWord_5012204).sum := by decide
  have hdescent : baseEnd_5012204 < baseStart_5012204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012218 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_5012218 : Nat := 118140960795 + 5012218 * 2 ^ 59
def prefixEnd_5012218 : Nat := 4983230072969 + 3 ^ 40 * 5012218 * 2
def baseEnd_5012218 : Nat := 2573676979117175907724235

theorem tailTrace_5012218 : CollatzResearch.WordTrace tailWord_5012218 prefixEnd_5012218 2573676979117175907724235 := by
  unfold tailWord_5012218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45702652238899419882095327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121873739303731786352254205 45702652238899419882095327)
  ·
    refine ⟨68553978358349129823142991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45702652238899419882095327 68553978358349129823142991)
    ·
      refine ⟨102830967537523694734714487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68553978358349129823142991 102830967537523694734714487)
      ·
        refine ⟨154246451306285542102071731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102830967537523694734714487 154246451306285542102071731)
        ·
          refine ⟨231369676959428313153107597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154246451306285542102071731 231369676959428313153107597)
          ·
            refine ⟨86763628859785617432415349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231369676959428313153107597 86763628859785617432415349)
            ·
              refine ⟨8134090205604901634288939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86763628859785617432415349 8134090205604901634288939)
              ·
                refine ⟨12201135308407352451433409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8134090205604901634288939 12201135308407352451433409)
                ·
                  refine ⟨9150851481305514338575057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12201135308407352451433409 9150851481305514338575057)
                  ·
                    refine ⟨6863138610979135753931293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9150851481305514338575057 6863138610979135753931293)
                    ·
                      refine ⟨2573676979117175907724235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863138610979135753931293 2573676979117175907724235)
                      ·
                        rfl

theorem cell23_5012218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_5012218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012218 prefixEnd_5012218 := by exact prefixLift 5012218
  have htrace : WordTrace (prefixWord ++ tailWord_5012218) baseStart_5012218 baseEnd_5012218 := by
    simpa [prefixWord, tailWord_5012218, baseEnd_5012218] using wordTrace_append hprefix tailTrace_5012218
  have hstable : (prefixWord ++ tailWord_5012218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012218).length < 2 ^ (prefixWord ++ tailWord_5012218).sum := by decide
  have hdescent : baseEnd_5012218 < baseStart_5012218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012224 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_5012224 : Nat := 118140960795 + 5012224 * 2 ^ 59
def prefixEnd_5012224 : Nat := 4983230072969 + 3 ^ 40 * 5012224 * 2
def baseEnd_5012224 : Nat := 2573680060001102884249207

theorem tailTrace_5012224 : CollatzResearch.WordTrace tailWord_5012224 prefixEnd_5012224 2573680060001102884249207 := by
  unfold tailWord_5012224
  simp only [CollatzResearch.WordTrace]
  refine ⟨91405413896787971276549863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121873885195717295035399817 91405413896787971276549863)
  ·
    refine ⟨137108120845181956914824795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91405413896787971276549863 137108120845181956914824795)
    ·
      refine ⟨205662181267772935372237193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137108120845181956914824795 205662181267772935372237193)
      ·
        refine ⟨154246635950829701529177895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205662181267772935372237193 154246635950829701529177895)
        ·
          refine ⟨231369953926244552293766843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154246635950829701529177895 231369953926244552293766843)
          ·
            refine ⟨347054930889366828440650265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231369953926244552293766843 347054930889366828440650265)
            ·
              refine ⟨260291198167025121330487699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347054930889366828440650265 260291198167025121330487699)
              ·
                refine ⟨390436797250537681995731549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260291198167025121330487699 390436797250537681995731549)
                ·
                  refine ⟨146413798968951630748399331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390436797250537681995731549 146413798968951630748399331)
                  ·
                    refine ⟨219620698453427446122598997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146413798968951630748399331 219620698453427446122598997)
                    ·
                      refine ⟨2573680060001102884249207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219620698453427446122598997 2573680060001102884249207)
                      ·
                        rfl

theorem cell23_5012224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_5012224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012224 prefixEnd_5012224 := by exact prefixLift 5012224
  have htrace : WordTrace (prefixWord ++ tailWord_5012224) baseStart_5012224 baseEnd_5012224 := by
    simpa [prefixWord, tailWord_5012224, baseEnd_5012224] using wordTrace_append hprefix tailTrace_5012224
  have hstable : (prefixWord ++ tailWord_5012224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012224).length < 2 ^ (prefixWord ++ tailWord_5012224).sum := by decide
  have hdescent : baseEnd_5012224 < baseStart_5012224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012242 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5012242 : Nat := 118140960795 + 5012242 * 2 ^ 59
def prefixEnd_5012242 : Nat := 4983230072969 + 3 ^ 40 * 5012242 * 2
def baseEnd_5012242 : Nat := 857896434217627937941375

theorem tailTrace_5012242 : CollatzResearch.WordTrace tailWord_5012242 prefixEnd_5012242 857896434217627937941375 := by
  unfold tailWord_5012242
  simp only [CollatzResearch.WordTrace]
  refine ⟨45702871076877682906813745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121874322871673821084836653 45702871076877682906813745)
  ·
    refine ⟨34277153307658262180110309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45702871076877682906813745 34277153307658262180110309)
    ·
      refine ⟨6426966245185924158770683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34277153307658262180110309 6426966245185924158770683)
      ·
        refine ⟨9640449367778886238156025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426966245185924158770683 9640449367778886238156025)
        ·
          refine ⟨7230337025834164678617019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640449367778886238156025 7230337025834164678617019)
          ·
            refine ⟨10845505538751247017925529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7230337025834164678617019 10845505538751247017925529)
            ·
              refine ⟨8134129154063435263444147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10845505538751247017925529 8134129154063435263444147)
              ·
                refine ⟨12201193731095152895166221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8134129154063435263444147 12201193731095152895166221)
                ·
                  refine ⟨4575447649160682335687333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12201193731095152895166221 4575447649160682335687333)
                  ·
                    refine ⟨857896434217627937941375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575447649160682335687333 857896434217627937941375)
                    ·
                      rfl

theorem cell23_5012242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5012242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012242 prefixEnd_5012242 := by exact prefixLift 5012242
  have htrace : WordTrace (prefixWord ++ tailWord_5012242) baseStart_5012242 baseEnd_5012242 := by
    simpa [prefixWord, tailWord_5012242, baseEnd_5012242] using wordTrace_append hprefix tailTrace_5012242
  have hstable : (prefixWord ++ tailWord_5012242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012242).length < 2 ^ (prefixWord ++ tailWord_5012242).sum := by decide
  have hdescent : baseEnd_5012242 < baseStart_5012242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012268 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_5012268 : Nat := 118140960795 + 5012268 * 2 ^ 59
def prefixEnd_5012268 : Nat := 4983230072969 + 3 ^ 40 * 5012268 * 2
def baseEnd_5012268 : Nat := 857900884383300237366335

theorem tailTrace_5012268 : CollatzResearch.WordTrace tailWord_5012268 prefixEnd_5012268 857900884383300237366335 := by
  unfold tailWord_5012268
  simp only [CollatzResearch.WordTrace]
  refine ⟨91406216302708269033850729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121874955070277692045134305 91406216302708269033850729)
  ·
    refine ⟨68554662227031201775388047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91406216302708269033850729 68554662227031201775388047)
    ·
      refine ⟨102831993340546802663082071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68554662227031201775388047 102831993340546802663082071)
      ·
        refine ⟨154247990010820203994623107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102831993340546802663082071 154247990010820203994623107)
        ·
          refine ⟨231371985016230305991934661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154247990010820203994623107 231371985016230305991934661)
          ·
            refine ⟨43382247190543182373487749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231371985016230305991934661 43382247190543182373487749)
            ·
              refine ⟨8134171348226846695028953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43382247190543182373487749 8134171348226846695028953)
              ·
                refine ⟨6100628511170135021271715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8134171348226846695028953 6100628511170135021271715)
                ·
                  refine ⟨9150942766755202531907573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100628511170135021271715 9150942766755202531907573)
                  ·
                    refine ⟨857900884383300237366335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9150942766755202531907573 857900884383300237366335)
                    ·
                      rfl

theorem cell23_5012268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_5012268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012268 prefixEnd_5012268 := by exact prefixLift 5012268
  have htrace : WordTrace (prefixWord ++ tailWord_5012268) baseStart_5012268 baseEnd_5012268 := by
    simpa [prefixWord, tailWord_5012268, baseEnd_5012268] using wordTrace_append hprefix tailTrace_5012268
  have hstable : (prefixWord ++ tailWord_5012268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012268).length < 2 ^ (prefixWord ++ tailWord_5012268).sum := by decide
  have hdescent : baseEnd_5012268 < baseStart_5012268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012276 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5012276 : Nat := 118140960795 + 5012276 * 2 ^ 59
def prefixEnd_5012276 : Nat := 4983230072969 + 3 ^ 40 * 5012276 * 2
def baseEnd_5012276 : Nat := 857902253665045560266323

theorem tailTrace_5012276 : CollatzResearch.WordTrace tailWord_5012276 prefixEnd_5012276 857902253665045560266323 := by
  unfold tailWord_5012276
  simp only [CollatzResearch.WordTrace]
  refine ⟨91406362194693777716996341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121875149592925036955995121 91406362194693777716996341)
  ·
    refine ⟨8569346455752541660968407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91406362194693777716996341 8569346455752541660968407)
    ·
      refine ⟨12854019683628812491452611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8569346455752541660968407 12854019683628812491452611)
      ·
        refine ⟨19281029525443218737178917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854019683628812491452611 19281029525443218737178917)
        ·
          refine ⟨3615193036020603513221047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19281029525443218737178917 3615193036020603513221047)
          ·
            refine ⟨5422789554030905269831571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615193036020603513221047 5422789554030905269831571)
            ·
              refine ⟨8134184331046357904747357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422789554030905269831571 8134184331046357904747357)
              ·
                refine ⟨3050319124142384214280259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8134184331046357904747357 3050319124142384214280259)
                ·
                  refine ⟨4575478686213576321420389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050319124142384214280259 4575478686213576321420389)
                  ·
                    refine ⟨857902253665045560266323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4575478686213576321420389 857902253665045560266323)
                    ·
                      rfl

theorem cell23_5012276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5012276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012276 prefixEnd_5012276 := by exact prefixLift 5012276
  have htrace : WordTrace (prefixWord ++ tailWord_5012276) baseStart_5012276 baseEnd_5012276 := by
    simpa [prefixWord, tailWord_5012276, baseEnd_5012276] using wordTrace_append hprefix tailTrace_5012276
  have hstable : (prefixWord ++ tailWord_5012276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012276).length < 2 ^ (prefixWord ++ tailWord_5012276).sum := by decide
  have hdescent : baseEnd_5012276 < baseStart_5012276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012311 : List Nat := [1, 1, 3, 2, 4, 1, 1, 10]
def baseStart_5012311 : Nat := 118140960795 + 5012311 * 2 ^ 59
def prefixEnd_5012311 : Nat := 4983230072969 + 3 ^ 40 * 5012311 * 2
def baseEnd_5012311 : Nat := 95323138252520149772641

theorem tailTrace_5012311 : CollatzResearch.WordTrace tailWord_5012311 prefixEnd_5012311 95323138252520149772641 := by
  unfold tailWord_5012311
  simp only [CollatzResearch.WordTrace]
  refine ⟨182814000944260756411516787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121876000629507170941011191 182814000944260756411516787)
  ·
    refine ⟨274221001416391134617275181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182814000944260756411516787 274221001416391134617275181)
    ·
      refine ⟨102832875531146675481478193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274221001416391134617275181 102832875531146675481478193)
      ·
        refine ⟨77124656648360006611108645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102832875531146675481478193 77124656648360006611108645)
        ·
          refine ⟨14460873121567501239582871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77124656648360006611108645 14460873121567501239582871)
          ·
            refine ⟨21691309682351251859374307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14460873121567501239582871 21691309682351251859374307)
            ·
              refine ⟨32536964523526877789061461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21691309682351251859374307 32536964523526877789061461)
              ·
                refine ⟨95323138252520149772641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32536964523526877789061461 95323138252520149772641)
                ·
                  rfl

theorem cell23_5012311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 10].length) (baseStart_5012311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012311 prefixEnd_5012311 := by exact prefixLift 5012311
  have htrace : WordTrace (prefixWord ++ tailWord_5012311) baseStart_5012311 baseEnd_5012311 := by
    simpa [prefixWord, tailWord_5012311, baseEnd_5012311] using wordTrace_append hprefix tailTrace_5012311
  have hstable : (prefixWord ++ tailWord_5012311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012311).length < 2 ^ (prefixWord ++ tailWord_5012311).sum := by decide
  have hdescent : baseEnd_5012311 < baseStart_5012311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012325 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_5012325 : Nat := 118140960795 + 5012325 * 2 ^ 59
def prefixEnd_5012325 : Nat := 4983230072969 + 3 ^ 40 * 5012325 * 2
def baseEnd_5012325 : Nat := 2573731921547206989086243

theorem tailTrace_5012325 : CollatzResearch.WordTrace tailWord_5012325 prefixEnd_5012325 2573731921547206989086243 := by
  unfold tailWord_5012325
  simp only [CollatzResearch.WordTrace]
  refine ⟨182814511566210036802526429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121876341044140024535017619 182814511566210036802526429)
  ·
    refine ⟨68555441837328763800947411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182814511566210036802526429 68555441837328763800947411)
    ·
      refine ⟨102833162755993145701421117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68555441837328763800947411 102833162755993145701421117)
      ·
        refine ⟨38562436033497429638032919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102833162755993145701421117 38562436033497429638032919)
        ·
          refine ⟨57843654050246144457049379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38562436033497429638032919 57843654050246144457049379)
          ·
            refine ⟨86765481075369216685574069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57843654050246144457049379 86765481075369216685574069)
            ·
              refine ⟨8134263850815864064272569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86765481075369216685574069 8134263850815864064272569)
              ·
                refine ⟨6100697888111898048204427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8134263850815864064272569 6100697888111898048204427)
                ·
                  refine ⟨9151046832167847072306641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100697888111898048204427 9151046832167847072306641)
                  ·
                    refine ⟨6863285124125885304229981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9151046832167847072306641 6863285124125885304229981)
                    ·
                      refine ⟨2573731921547206989086243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863285124125885304229981 2573731921547206989086243)
                      ·
                        rfl

theorem cell23_5012325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_5012325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012325 prefixEnd_5012325 := by exact prefixLift 5012325
  have htrace : WordTrace (prefixWord ++ tailWord_5012325) baseStart_5012325 baseEnd_5012325 := by
    simpa [prefixWord, tailWord_5012325, baseEnd_5012325] using wordTrace_append hprefix tailTrace_5012325
  have hstable : (prefixWord ++ tailWord_5012325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012325).length < 2 ^ (prefixWord ++ tailWord_5012325).sum := by decide
  have hdescent : baseEnd_5012325 < baseStart_5012325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012338 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5012338 : Nat := 118140960795 + 5012338 * 2 ^ 59
def prefixEnd_5012338 : Nat := 4983230072969 + 3 ^ 40 * 5012338 * 2
def baseEnd_5012338 : Nat := 2573738596795715438223683

theorem tailTrace_5012338 : CollatzResearch.WordTrace tailWord_5012338 prefixEnd_5012338 2573738596795715438223683 := by
  unfold tailWord_5012338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45703746428790735005687417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121876657143441960015166445 45703746428790735005687417)
  ·
    refine ⟨34277809821593051254265563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45703746428790735005687417 34277809821593051254265563)
    ·
      refine ⟨51416714732389576881398345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34277809821593051254265563 51416714732389576881398345)
      ·
        refine ⟨38562536049292182661048759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51416714732389576881398345 38562536049292182661048759)
        ·
          refine ⟨57843804073938273991573139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38562536049292182661048759 57843804073938273991573139)
          ·
            refine ⟨86765706110907410987359709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57843804073938273991573139 86765706110907410987359709)
            ·
              refine ⟨32537139791590279120259891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86765706110907410987359709 32537139791590279120259891)
              ·
                refine ⟨48805709687385418680389837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32537139791590279120259891 48805709687385418680389837)
                ·
                  refine ⟨18302141132769532005146189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48805709687385418680389837 18302141132769532005146189)
                  ·
                    refine ⟨6863302924788574501929821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18302141132769532005146189 6863302924788574501929821)
                    ·
                      refine ⟨2573738596795715438223683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863302924788574501929821 2573738596795715438223683)
                      ·
                        rfl

theorem cell23_5012338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5012338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012338 prefixEnd_5012338 := by exact prefixLift 5012338
  have htrace : WordTrace (prefixWord ++ tailWord_5012338) baseStart_5012338 baseEnd_5012338 := by
    simpa [prefixWord, tailWord_5012338, baseEnd_5012338] using wordTrace_append hprefix tailTrace_5012338
  have hstable : (prefixWord ++ tailWord_5012338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012338).length < 2 ^ (prefixWord ++ tailWord_5012338).sum := by decide
  have hdescent : baseEnd_5012338 < baseStart_5012338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012342 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5012342 : Nat := 118140960795 + 5012342 * 2 ^ 59
def prefixEnd_5012342 : Nat := 4983230072969 + 3 ^ 40 * 5012342 * 2
def baseEnd_5012342 : Nat := 2573740650718333422573665

theorem tailTrace_5012342 : CollatzResearch.WordTrace tailWord_5012342 prefixEnd_5012342 2573740650718333422573665 := by
  unfold tailWord_5012342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425945725446778044118455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121876754404765632470596853 11425945725446778044118455)
  ·
    refine ⟨17138918588170167066177683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11425945725446778044118455 17138918588170167066177683)
    ·
      refine ⟨25708377882255250599266525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17138918588170167066177683 25708377882255250599266525)
      ·
        refine ⟨9640641705845718974724947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25708377882255250599266525 9640641705845718974724947)
        ·
          refine ⟨14460962558768578462087421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640641705845718974724947 14460962558768578462087421)
          ·
            refine ⟨5422860959538216923282783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14460962558768578462087421 5422860959538216923282783)
            ·
              refine ⟨8134291439307325384924175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422860959538216923282783 8134291439307325384924175)
              ·
                refine ⟨12201437158960988077386263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8134291439307325384924175 12201437158960988077386263)
                ·
                  refine ⟨18302155738441482116079395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12201437158960988077386263 18302155738441482116079395)
                  ·
                    refine ⟨27453233607662223174119093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18302155738441482116079395 27453233607662223174119093)
                    ·
                      refine ⟨2573740650718333422573665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27453233607662223174119093 2573740650718333422573665)
                      ·
                        rfl

theorem cell23_5012342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5012342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012342 prefixEnd_5012342 := by exact prefixLift 5012342
  have htrace : WordTrace (prefixWord ++ tailWord_5012342) baseStart_5012342 baseEnd_5012342 := by
    simpa [prefixWord, tailWord_5012342, baseEnd_5012342] using wordTrace_append hprefix tailTrace_5012342
  have hstable : (prefixWord ++ tailWord_5012342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012342).length < 2 ^ (prefixWord ++ tailWord_5012342).sum := by decide
  have hdescent : baseEnd_5012342 < baseStart_5012342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012350 : List Nat := [4, 2, 3, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5012350 : Nat := 118140960795 + 5012350 * 2 ^ 59
def prefixEnd_5012350 : Nat := 4983230072969 + 3 ^ 40 * 5012350 * 2
def baseEnd_5012350 : Nat := 2573744758563569391273629

theorem tailTrace_5012350 : CollatzResearch.WordTrace tailWord_5012350 prefixEnd_5012350 2573744758563569391273629 := by
  unfold tailWord_5012350
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851927923889933259023313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121876948927412977381457669 22851927923889933259023313)
  ·
    refine ⟨17138945942917449944267485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22851927923889933259023313 17138945942917449944267485)
    ·
      refine ⟨6427104728594043729100307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17138945942917449944267485 6427104728594043729100307)
      ·
        refine ⟨9640657092891065593650461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6427104728594043729100307 9640657092891065593650461)
        ·
          refine ⟨3615246409834149597618923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9640657092891065593650461 3615246409834149597618923)
          ·
            refine ⟨5422869614751224396428385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615246409834149597618923 5422869614751224396428385)
            ·
              refine ⟨4067152211063418297321289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5422869614751224396428385 4067152211063418297321289)
              ·
                refine ⟨3050364158297563722990967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067152211063418297321289 3050364158297563722990967)
                ·
                  refine ⟨4575546237446345584486451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050364158297563722990967 4575546237446345584486451)
                  ·
                    refine ⟨6863319356169518376729677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575546237446345584486451 6863319356169518376729677)
                    ·
                      refine ⟨2573744758563569391273629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863319356169518376729677 2573744758563569391273629)
                      ·
                        rfl

theorem cell23_5012350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5012350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012350 prefixEnd_5012350 := by exact prefixLift 5012350
  have htrace : WordTrace (prefixWord ++ tailWord_5012350) baseStart_5012350 baseEnd_5012350 := by
    simpa [prefixWord, tailWord_5012350, baseEnd_5012350] using wordTrace_append hprefix tailTrace_5012350
  have hstable : (prefixWord ++ tailWord_5012350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012350).length < 2 ^ (prefixWord ++ tailWord_5012350).sum := by decide
  have hdescent : baseEnd_5012350 < baseStart_5012350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012351 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_5012351 : Nat := 118140960795 + 5012351 * 2 ^ 59
def prefixEnd_5012351 : Nat := 4983230072969 + 3 ^ 40 * 5012351 * 2
def baseEnd_5012351 : Nat := 2573745272044223887361123

theorem tailTrace_5012351 : CollatzResearch.WordTrace tailWord_5012351 prefixEnd_5012351 2573745272044223887361123 := by
  unfold tailWord_5012351
  simp only [CollatzResearch.WordTrace]
  refine ⟨182815459864115843242972907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121876973242743895495315271 182815459864115843242972907)
  ·
    refine ⟨274223189796173764864459361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182815459864115843242972907 274223189796173764864459361)
    ·
      refine ⟨205667392347130323648344521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274223189796173764864459361 205667392347130323648344521)
      ·
        refine ⟨154250544260347742736258391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205667392347130323648344521 154250544260347742736258391)
        ·
          refine ⟨231375816390521614104387587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154250544260347742736258391 231375816390521614104387587)
          ·
            refine ⟨347063724585782421156581381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231375816390521614104387587 347063724585782421156581381)
            ·
              refine ⟨65074448359834203966859009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 347063724585782421156581381 65074448359834203966859009)
              ·
                refine ⟨48805836269875652975144257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65074448359834203966859009 48805836269875652975144257)
                ·
                  refine ⟨36604377202406739731358193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48805836269875652975144257 36604377202406739731358193)
                  ·
                    refine ⟨27453282901805054798518645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36604377202406739731358193 27453282901805054798518645)
                    ·
                      refine ⟨2573745272044223887361123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27453282901805054798518645 2573745272044223887361123)
                      ·
                        rfl

theorem cell23_5012351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_5012351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012351 prefixEnd_5012351 := by exact prefixLift 5012351
  have htrace : WordTrace (prefixWord ++ tailWord_5012351) baseStart_5012351 baseEnd_5012351 := by
    simpa [prefixWord, tailWord_5012351, baseEnd_5012351] using wordTrace_append hprefix tailTrace_5012351
  have hstable : (prefixWord ++ tailWord_5012351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012351).length < 2 ^ (prefixWord ++ tailWord_5012351).sum := by decide
  have hdescent : baseEnd_5012351 < baseStart_5012351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012372 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5012372 : Nat := 118140960795 + 5012372 * 2 ^ 59
def prefixEnd_5012372 : Nat := 4983230072969 + 3 ^ 40 * 5012372 * 2
def baseEnd_5012372 : Nat := 2573756055137968305198527

theorem tailTrace_5012372 : CollatzResearch.WordTrace tailWord_5012372 prefixEnd_5012372 2573756055137968305198527 := by
  unfold tailWord_5012372
  simp only [CollatzResearch.WordTrace]
  refine ⟨91408112898519881914743685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121877483864693175886324913 91408112898519881914743685)
  ·
    refine ⟨17139021168472477859014441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91408112898519881914743685 17139021168472477859014441)
    ·
      refine ⟨12854265876354358394260831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17139021168472477859014441 12854265876354358394260831)
      ·
        refine ⟨19281398814531537591391247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854265876354358394260831 19281398814531537591391247)
        ·
          refine ⟨28922098221797306387086871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19281398814531537591391247 28922098221797306387086871)
          ·
            refine ⟨43383147332695959580630307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28922098221797306387086871 43383147332695959580630307)
            ·
              refine ⟨65074720999043939370945461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43383147332695959580630307 65074720999043939370945461)
              ·
                refine ⟨6100755093660369316026137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65074720999043939370945461 6100755093660369316026137)
                ·
                  refine ⟨4575566320245276987019603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6100755093660369316026137 4575566320245276987019603)
                  ·
                    refine ⟨6863349480367915480529405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575566320245276987019603 6863349480367915480529405)
                    ·
                      refine ⟨2573756055137968305198527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863349480367915480529405 2573756055137968305198527)
                      ·
                        rfl

theorem cell23_5012372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5012372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012372 prefixEnd_5012372 := by exact prefixLift 5012372
  have htrace : WordTrace (prefixWord ++ tailWord_5012372) baseStart_5012372 baseEnd_5012372 := by
    simpa [prefixWord, tailWord_5012372, baseEnd_5012372] using wordTrace_append hprefix tailTrace_5012372
  have hstable : (prefixWord ++ tailWord_5012372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012372).length < 2 ^ (prefixWord ++ tailWord_5012372).sum := by decide
  have hdescent : baseEnd_5012372 < baseStart_5012372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 6, 2, 2]
def baseStart_5012395 : Nat := 118140960795 + 5012395 * 2 ^ 59
def prefixEnd_5012395 : Nat := 4983230072969 + 3 ^ 40 * 5012395 * 2
def baseEnd_5012395 : Nat := 2573767865193021715210921

theorem tailTrace_5012395 : CollatzResearch.WordTrace tailWord_5012395 prefixEnd_5012395 2573767865193021715210921 := by
  unfold tailWord_5012395
  simp only [CollatzResearch.WordTrace]
  refine ⟨182817064675956438757574639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121878043117304292505049759 182817064675956438757574639)
  ·
    refine ⟨274225597013934658136361959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182817064675956438757574639 274225597013934658136361959)
    ·
      refine ⟨411338395520901987204542939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274225597013934658136361959 411338395520901987204542939)
      ·
        refine ⟨617007593281352980806814409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411338395520901987204542939 617007593281352980806814409)
        ·
          refine ⟨462755694961014735605110807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617007593281352980806814409 462755694961014735605110807)
          ·
            refine ⟨694133542441522103407666211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462755694961014735605110807 694133542441522103407666211)
            ·
              refine ⟨1041200313662283155111499317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694133542441522103407666211 1041200313662283155111499317)
              ·
                refine ⟨97612529405839045791703061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1041200313662283155111499317 97612529405839045791703061)
                ·
                  refine ⟨4575587315898705271486081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97612529405839045791703061 4575587315898705271486081)
                  ·
                    refine ⟨3431690486924028953614561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4575587315898705271486081 3431690486924028953614561)
                    ·
                      refine ⟨2573767865193021715210921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431690486924028953614561 2573767865193021715210921)
                      ·
                        rfl

theorem cell23_5012395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2, 2].length) (baseStart_5012395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012395 prefixEnd_5012395 := by exact prefixLift 5012395
  have htrace : WordTrace (prefixWord ++ tailWord_5012395) baseStart_5012395 baseEnd_5012395 := by
    simpa [prefixWord, tailWord_5012395, baseEnd_5012395] using wordTrace_append hprefix tailTrace_5012395
  have hstable : (prefixWord ++ tailWord_5012395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012395).length < 2 ^ (prefixWord ++ tailWord_5012395).sum := by decide
  have hdescent : baseEnd_5012395 < baseStart_5012395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012408 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_5012408 : Nat := 118140960795 + 5012408 * 2 ^ 59
def prefixEnd_5012408 : Nat := 4983230072969 + 3 ^ 40 * 5012408 * 2
def baseEnd_5012408 : Nat := 2573774540441530164348361

theorem tailTrace_5012408 : CollatzResearch.WordTrace tailWord_5012408 prefixEnd_5012408 2573774540441530164348361 := by
  unfold tailWord_5012408
  simp only [CollatzResearch.WordTrace]
  refine ⟨91408769412454670988898939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121878359216606227985198585 91408769412454670988898939)
  ·
    refine ⟨137113154118682006483348409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91408769412454670988898939 137113154118682006483348409)
    ·
      refine ⟨102834865589011504862511307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137113154118682006483348409 102834865589011504862511307)
      ·
        refine ⟨154252298383517257293766961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102834865589011504862511307 154252298383517257293766961)
        ·
          refine ⟨115689223787637942970325221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154252298383517257293766961 115689223787637942970325221)
          ·
            refine ⟨21691729460182114306935979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115689223787637942970325221 21691729460182114306935979)
            ·
              refine ⟨32537594190273171460403969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21691729460182114306935979 32537594190273171460403969)
              ·
                refine ⟨24403195642704878595302977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32537594190273171460403969 24403195642704878595302977)
                ·
                  refine ⟨18302396732028658946477233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24403195642704878595302977 18302396732028658946477233)
                  ·
                    refine ⟨13726797549021494209857925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18302396732028658946477233 13726797549021494209857925)
                    ·
                      refine ⟨2573774540441530164348361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13726797549021494209857925 2573774540441530164348361)
                      ·
                        rfl

theorem cell23_5012408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_5012408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012408 prefixEnd_5012408 := by exact prefixLift 5012408
  have htrace : WordTrace (prefixWord ++ tailWord_5012408) baseStart_5012408 baseEnd_5012408 := by
    simpa [prefixWord, tailWord_5012408, baseEnd_5012408] using wordTrace_append hprefix tailTrace_5012408
  have hstable : (prefixWord ++ tailWord_5012408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012408).length < 2 ^ (prefixWord ++ tailWord_5012408).sum := by decide
  have hdescent : baseEnd_5012408 < baseStart_5012408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012465 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_5012465 : Nat := 118140960795 + 5012465 * 2 ^ 59
def prefixEnd_5012465 : Nat := 4983230072969 + 3 ^ 40 * 5012465 * 2
def baseEnd_5012465 : Nat := 857934602946278813778533

theorem tailTrace_5012465 : CollatzResearch.WordTrace tailWord_5012465 prefixEnd_5012465 857934602946278813778533 := by
  unfold tailWord_5012465
  simp only [CollatzResearch.WordTrace]
  refine ⟨182819617785702840712622849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121879745190468560475081899 182819617785702840712622849)
  ·
    refine ⟨137114713339277130534467137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182819617785702840712622849 137114713339277130534467137)
    ·
      refine ⟨102836035004457847900850353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137114713339277130534467137 102836035004457847900850353)
      ·
        refine ⟨77127026253343385925637765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102836035004457847900850353 77127026253343385925637765)
        ·
          refine ⟨14461317422501884861057081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77127026253343385925637765 14461317422501884861057081)
          ·
            refine ⟨10845988066876413645792811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14461317422501884861057081 10845988066876413645792811)
            ·
              refine ⟨16268982100314620468689217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10845988066876413645792811 16268982100314620468689217)
              ·
                refine ⟨12201736575235965351516913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16268982100314620468689217 12201736575235965351516913)
                ·
                  refine ⟨9151302431426974013637685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12201736575235965351516913 9151302431426974013637685)
                  ·
                    refine ⟨857934602946278813778533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9151302431426974013637685 857934602946278813778533)
                    ·
                      rfl

theorem cell23_5012465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_5012465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012465 prefixEnd_5012465 := by exact prefixLift 5012465
  have htrace : WordTrace (prefixWord ++ tailWord_5012465) baseStart_5012465 baseEnd_5012465 := by
    simpa [prefixWord, tailWord_5012465, baseEnd_5012465] using wordTrace_append hprefix tailTrace_5012465
  have hstable : (prefixWord ++ tailWord_5012465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012465).length < 2 ^ (prefixWord ++ tailWord_5012465).sum := by decide
  have hdescent : baseEnd_5012465 < baseStart_5012465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012469 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 7]
def baseStart_5012469 : Nat := 118140960795 + 5012469 * 2 ^ 59
def prefixEnd_5012469 : Nat := 4983230072969 + 3 ^ 40 * 5012469 * 2
def baseEnd_5012469 : Nat := 285978429195717158409509

theorem tailTrace_5012469 : CollatzResearch.WordTrace tailWord_5012469 prefixEnd_5012469 285978429195717158409509 := by
  unfold tailWord_5012469
  simp only [CollatzResearch.WordTrace]
  refine ⟨182819763677688349395768461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121879842451792232930512307 182819763677688349395768461)
  ·
    refine ⟨68557411379133131023413173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182819763677688349395768461 68557411379133131023413173)
    ·
      refine ⟨6427257316793731033444985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68557411379133131023413173 6427257316793731033444985)
      ·
        refine ⟨4820442987595298275083739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6427257316793731033444985 4820442987595298275083739)
        ·
          refine ⟨7230664481392947412625609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820442987595298275083739 7230664481392947412625609)
          ·
            refine ⟨5422998361044710559469207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230664481392947412625609 5422998361044710559469207)
            ·
              refine ⟨8134497541567065839203811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422998361044710559469207 8134497541567065839203811)
              ·
                refine ⟨12201746312350598758805717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8134497541567065839203811 12201746312350598758805717)
                ·
                  refine ⟨285978429195717158409509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12201746312350598758805717 285978429195717158409509)
                  ·
                    rfl

theorem cell23_5012469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_5012469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012469 prefixEnd_5012469 := by exact prefixLift 5012469
  have htrace : WordTrace (prefixWord ++ tailWord_5012469) baseStart_5012469 baseEnd_5012469 := by
    simpa [prefixWord, tailWord_5012469, baseEnd_5012469] using wordTrace_append hprefix tailTrace_5012469
  have hstable : (prefixWord ++ tailWord_5012469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012469).length < 2 ^ (prefixWord ++ tailWord_5012469).sum := by decide
  have hdescent : baseEnd_5012469 < baseStart_5012469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012485 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_5012485 : Nat := 118140960795 + 5012485 * 2 ^ 59
def prefixEnd_5012485 : Nat := 4983230072969 + 3 ^ 40 * 5012485 * 2
def baseEnd_5012485 : Nat := 2573814078451926363085507

theorem tailTrace_5012485 : CollatzResearch.WordTrace tailWord_5012485 prefixEnd_5012485 2573814078451926363085507 := by
  unfold tailWord_5012485
  simp only [CollatzResearch.WordTrace]
  refine ⟨182820347245630384128350909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121880231497086922752233939 182820347245630384128350909)
  ·
    refine ⟨68557630217111394048131591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182820347245630384128350909 68557630217111394048131591)
    ·
      refine ⟨102836445325667091072197387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68557630217111394048131591 102836445325667091072197387)
      ·
        refine ⟨154254667988500636608296081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102836445325667091072197387 154254667988500636608296081)
        ·
          refine ⟨115691000991375477456222061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154254667988500636608296081 115691000991375477456222061)
          ·
            refine ⟨43384125371765804046083273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115691000991375477456222061 43384125371765804046083273)
            ·
              refine ⟨32538094028824353034562455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43384125371765804046083273 32538094028824353034562455)
              ·
                refine ⟨48807141043236529551843683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32538094028824353034562455 48807141043236529551843683)
                ·
                  refine ⟨73210711564854794327765525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48807141043236529551843683 73210711564854794327765525)
                  ·
                    refine ⟨3431752104602568484114009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73210711564854794327765525 3431752104602568484114009)
                    ·
                      refine ⟨2573814078451926363085507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3431752104602568484114009 2573814078451926363085507)
                      ·
                        rfl

theorem cell23_5012485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_5012485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012485 prefixEnd_5012485 := by exact prefixLift 5012485
  have htrace : WordTrace (prefixWord ++ tailWord_5012485) baseStart_5012485 baseEnd_5012485 := by
    simpa [prefixWord, tailWord_5012485, baseEnd_5012485] using wordTrace_append hprefix tailTrace_5012485
  have hstable : (prefixWord ++ tailWord_5012485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012485).length < 2 ^ (prefixWord ++ tailWord_5012485).sum := by decide
  have hdescent : baseEnd_5012485 < baseStart_5012485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012505 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_5012505 : Nat := 118140960795 + 5012505 * 2 ^ 59
def prefixEnd_5012505 : Nat := 4983230072969 + 3 ^ 40 * 5012505 * 2
def baseEnd_5012505 : Nat := 2573824348065016284835415

theorem tailTrace_5012505 : CollatzResearch.WordTrace tailWord_5012505 prefixEnd_5012505 2573824348065016284835415 := by
  unfold tailWord_5012505
  simp only [CollatzResearch.WordTrace]
  refine ⟨182821076705557927544078969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121880717803705285029385979 182821076705557927544078969)
  ·
    refine ⟨137115807529168445658059227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182821076705557927544078969 137115807529168445658059227)
    ·
      refine ⟨205673711293752668487088841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137115807529168445658059227 205673711293752668487088841)
      ·
        refine ⟨154255283470314501365316631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205673711293752668487088841 154255283470314501365316631)
        ·
          refine ⟨231382925205471752047974947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154255283470314501365316631 231382925205471752047974947)
          ·
            refine ⟨347074387808207628071962421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231382925205471752047974947 347074387808207628071962421)
            ·
              refine ⟨32538223857019465131746477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 347074387808207628071962421 32538223857019465131746477)
              ·
                refine ⟨12201833946382299424404929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32538223857019465131746477 12201833946382299424404929)
                ·
                  refine ⟨9151375459786724568303697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12201833946382299424404929 9151375459786724568303697)
                  ·
                    refine ⟨6863531594840043426227773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9151375459786724568303697 6863531594840043426227773)
                    ·
                      refine ⟨2573824348065016284835415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863531594840043426227773 2573824348065016284835415)
                      ·
                        rfl

theorem cell23_5012505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_5012505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012505 prefixEnd_5012505 := by exact prefixLift 5012505
  have htrace : WordTrace (prefixWord ++ tailWord_5012505) baseStart_5012505 baseEnd_5012505 := by
    simpa [prefixWord, tailWord_5012505, baseEnd_5012505] using wordTrace_append hprefix tailTrace_5012505
  have hstable : (prefixWord ++ tailWord_5012505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012505).length < 2 ^ (prefixWord ++ tailWord_5012505).sum := by decide
  have hdescent : baseEnd_5012505 < baseStart_5012505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012528 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_5012528 : Nat := 118140960795 + 5012528 * 2 ^ 59
def prefixEnd_5012528 : Nat := 4983230072969 + 3 ^ 40 * 5012528 * 2
def baseEnd_5012528 : Nat := 2573836158120069694847809

theorem tailTrace_5012528 : CollatzResearch.WordTrace tailWord_5012528 prefixEnd_5012528 2573836158120069694847809 := by
  unfold tailWord_5012528
  simp only [CollatzResearch.WordTrace]
  refine ⟨91410957792237301236083119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121881277056316401648110825 91410957792237301236083119)
  ·
    refine ⟨137116436688355951854124679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91410957792237301236083119 137116436688355951854124679)
    ·
      refine ⟨205674655032533927781187019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137116436688355951854124679 205674655032533927781187019)
      ·
        refine ⟨308511982548800891671780529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205674655032533927781187019 308511982548800891671780529)
        ·
          refine ⟨231383986911600668753835397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308511982548800891671780529 231383986911600668753835397)
          ·
            refine ⟨43384497545925125391344137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231383986911600668753835397 43384497545925125391344137)
            ·
              refine ⟨32538373159443844043508103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43384497545925125391344137 32538373159443844043508103)
              ·
                refine ⟨48807559739165766065262155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32538373159443844043508103 48807559739165766065262155)
                ·
                  refine ⟨73211339608748649097893233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48807559739165766065262155 73211339608748649097893233)
                  ·
                    refine ⟨54908504706561486823419925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73211339608748649097893233 54908504706561486823419925)
                    ·
                      refine ⟨2573836158120069694847809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54908504706561486823419925 2573836158120069694847809)
                      ·
                        rfl

theorem cell23_5012528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_5012528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012528 prefixEnd_5012528 := by exact prefixLift 5012528
  have htrace : WordTrace (prefixWord ++ tailWord_5012528) baseStart_5012528 baseEnd_5012528 := by
    simpa [prefixWord, tailWord_5012528, baseEnd_5012528] using wordTrace_append hprefix tailTrace_5012528
  have hstable : (prefixWord ++ tailWord_5012528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012528).length < 2 ^ (prefixWord ++ tailWord_5012528).sum := by decide
  have hdescent : baseEnd_5012528 < baseStart_5012528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012542 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_5012542 : Nat := 118140960795 + 5012542 * 2 ^ 59
def prefixEnd_5012542 : Nat := 4983230072969 + 3 ^ 40 * 5012542 * 2
def baseEnd_5012542 : Nat := 285982594094359182230305

theorem tailTrace_5012542 : CollatzResearch.WordTrace tailWord_5012542 prefixEnd_5012542 285982594094359182230305 := by
  unfold tailWord_5012542
  simp only [CollatzResearch.WordTrace]
  refine ⟨22852803275802985357896985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121881617470949255242117253 22852803275802985357896985)
  ·
    refine ⟨17139602456852239018422739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22852803275802985357896985 17139602456852239018422739)
    ·
      refine ⟨25709403685278358527634109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17139602456852239018422739 25709403685278358527634109)
      ·
        refine ⟨9641026381979384447862791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25709403685278358527634109 9641026381979384447862791)
        ·
          refine ⟨14461539572969076671794187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9641026381979384447862791 14461539572969076671794187)
          ·
            refine ⟨21692309359453615007691281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14461539572969076671794187 21692309359453615007691281)
            ·
              refine ⟨16269232019590211255768461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21692309359453615007691281 16269232019590211255768461)
              ·
                refine ⟨6100962007346329220913173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16269232019590211255768461 6100962007346329220913173)
                ·
                  refine ⟨285982594094359182230305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6100962007346329220913173 285982594094359182230305)
                  ·
                    rfl

theorem cell23_5012542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_5012542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012542 prefixEnd_5012542 := by exact prefixLift 5012542
  have htrace : WordTrace (prefixWord ++ tailWord_5012542) baseStart_5012542 baseEnd_5012542 := by
    simpa [prefixWord, tailWord_5012542, baseEnd_5012542] using wordTrace_append hprefix tailTrace_5012542
  have hstable : (prefixWord ++ tailWord_5012542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012542).length < 2 ^ (prefixWord ++ tailWord_5012542).sum := by decide
  have hdescent : baseEnd_5012542 < baseStart_5012542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012552 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_5012552 : Nat := 118140960795 + 5012552 * 2 ^ 59
def prefixEnd_5012552 : Nat := 4983230072969 + 3 ^ 40 * 5012552 * 2
def baseEnd_5012552 : Nat := 2573848481655777600947699

theorem tailTrace_5012552 : CollatzResearch.WordTrace tailWord_5012552 prefixEnd_5012552 2573848481655777600947699 := by
  unfold tailWord_5012552
  simp only [CollatzResearch.WordTrace]
  refine ⟨91411395468193827285519955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121881860624258436380693273 91411395468193827285519955)
  ·
    refine ⟨137117093202290740928279933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91411395468193827285519955 137117093202290740928279933)
    ·
      refine ⟨51418909950859027848104975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137117093202290740928279933 51418909950859027848104975)
      ·
        refine ⟨77128364926288541772157463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51418909950859027848104975 77128364926288541772157463)
        ·
          refine ⟨115692547389432812658236195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77128364926288541772157463 115692547389432812658236195)
          ·
            refine ⟨173538821084149218987354293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115692547389432812658236195 173538821084149218987354293)
            ·
              refine ⟨16269264476638989280064465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173538821084149218987354293 16269264476638989280064465)
              ·
                refine ⟨12201948357479241960048349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16269264476638989280064465 12201948357479241960048349)
                ·
                  refine ⟨4575730634054715735018131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12201948357479241960048349 4575730634054715735018131)
                  ·
                    refine ⟨6863595951082073602527197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575730634054715735018131 6863595951082073602527197)
                    ·
                      refine ⟨2573848481655777600947699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6863595951082073602527197 2573848481655777600947699)
                      ·
                        rfl

theorem cell23_5012552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_5012552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012552 prefixEnd_5012552 := by exact prefixLift 5012552
  have htrace : WordTrace (prefixWord ++ tailWord_5012552) baseStart_5012552 baseEnd_5012552 := by
    simpa [prefixWord, tailWord_5012552, baseEnd_5012552] using wordTrace_append hprefix tailTrace_5012552
  have hstable : (prefixWord ++ tailWord_5012552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012552).length < 2 ^ (prefixWord ++ tailWord_5012552).sum := by decide
  have hdescent : baseEnd_5012552 < baseStart_5012552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5012572 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_5012572 : Nat := 118140960795 + 5012572 * 2 ^ 59
def prefixEnd_5012572 : Nat := 4983230072969 + 3 ^ 40 * 5012572 * 2
def baseEnd_5012572 : Nat := 857952917089622507565869

theorem tailTrace_5012572 : CollatzResearch.WordTrace tailWord_5012572 prefixEnd_5012572 857952917089622507565869 := by
  unfold tailWord_5012572
  simp only [CollatzResearch.WordTrace]
  refine ⟨91411760198157598993383985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121882346930876798657845313 91411760198157598993383985)
  ·
    refine ⟨68558820148618199245037989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91411760198157598993383985 68558820148618199245037989)
    ·
      refine ⟨12854778777865912358444623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68558820148618199245037989 12854778777865912358444623)
      ·
        refine ⟨19282168166798868537666935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854778777865912358444623 19282168166798868537666935)
        ·
          refine ⟨28923252250198302806500403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19282168166798868537666935 28923252250198302806500403)
          ·
            refine ⟨43384878375297454209750605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28923252250198302806500403 43384878375297454209750605)
            ·
              refine ⟨16269329390736545328656477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43384878375297454209750605 16269329390736545328656477)
              ·
                refine ⟨6100998521526204498246179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16269329390736545328656477 6100998521526204498246179)
                ·
                  refine ⟨9151497782289306747369269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100998521526204498246179 9151497782289306747369269)
                  ·
                    refine ⟨857952917089622507565869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9151497782289306747369269 857952917089622507565869)
                    ·
                      rfl

theorem cell23_5012572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_5012572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5012572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5012572 prefixEnd_5012572 := by exact prefixLift 5012572
  have htrace : WordTrace (prefixWord ++ tailWord_5012572) baseStart_5012572 baseEnd_5012572 := by
    simpa [prefixWord, tailWord_5012572, baseEnd_5012572] using wordTrace_append hprefix tailTrace_5012572
  have hstable : (prefixWord ++ tailWord_5012572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5012572).length < 2 ^ (prefixWord ++ tailWord_5012572).sum := by decide
  have hdescent : baseEnd_5012572 < baseStart_5012572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5012572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
