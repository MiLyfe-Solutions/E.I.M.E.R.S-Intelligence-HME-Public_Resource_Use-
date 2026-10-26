import V185TrunkScan23Chunk0095

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_569557 : List Nat := [1, 3, 2, 4, 2, 2, 9]
def baseStart_569557 : Nat := 118140960795 + 569557 * 2 ^ 59
def prefixEnd_569557 : Nat := 4983230072969 + 3 ^ 40 * 569557 * 2
def baseEnd_569557 : Nat := 3610574088060905423681

theorem tailTrace_569557 : CollatzResearch.WordTrace tailWord_569557 prefixEnd_569557 3610574088060905423681 := by
  unfold tailWord_569557
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773450397599736436442925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13848966931733157624295283 20773450397599736436442925)
  ·
    refine ⟨7790043899099901163666097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20773450397599736436442925 7790043899099901163666097)
    ·
      refine ⟨5842532924324925872749573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7790043899099901163666097 5842532924324925872749573)
      ·
        refine ⟨1095474923310923601140545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5842532924324925872749573 1095474923310923601140545)
        ·
          refine ⟨821606192483192700855409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095474923310923601140545 821606192483192700855409)
          ·
            refine ⟨616204644362394525641557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821606192483192700855409 616204644362394525641557)
            ·
              refine ⟨3610574088060905423681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 616204644362394525641557 3610574088060905423681)
              ·
                rfl

theorem cell23_569557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 9].length) (baseStart_569557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569557 prefixEnd_569557 := by exact prefixLift 569557
  have htrace : WordTrace (prefixWord ++ tailWord_569557) baseStart_569557 baseEnd_569557 := by
    simpa [prefixWord, tailWord_569557, baseEnd_569557] using wordTrace_append hprefix tailTrace_569557
  have hstable : (prefixWord ++ tailWord_569557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569557).length < 2 ^ (prefixWord ++ tailWord_569557).sum := by decide
  have hdescent : baseEnd_569557 < baseStart_569557 := by decide
  rcases family_descends (prefixWord ++ tailWord_569557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569568 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 1, 2, 2]
def baseStart_569568 : Nat := 118140960795 + 569568 * 2 ^ 59
def prefixEnd_569568 : Nat := 4983230072969 + 3 ^ 40 * 569568 * 2
def baseEnd_569568 : Nat := 292462149420132796280611

theorem tailTrace_569568 : CollatzResearch.WordTrace tailWord_569568 prefixEnd_569568 292462149420132796280611 := by
  unfold tailWord_569568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386925800279942657546679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13849234400373256876728905 10386925800279942657546679)
  ·
    refine ⟨15580388700419913986320019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10386925800279942657546679 15580388700419913986320019)
    ·
      refine ⟨23370583050629870979480029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580388700419913986320019 23370583050629870979480029)
      ·
        refine ⟨8763968643986201617305011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23370583050629870979480029 8763968643986201617305011)
        ·
          refine ⟨13145952965979302425957517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8763968643986201617305011 13145952965979302425957517)
          ·
            refine ⟨4929732362242238409734069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13145952965979302425957517 4929732362242238409734069)
            ·
              refine ⟨462162408960209850912569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4929732362242238409734069 462162408960209850912569)
              ·
                refine ⟨346621806720157388184427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462162408960209850912569 346621806720157388184427)
                ·
                  refine ⟨519932710080236082276641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346621806720157388184427 519932710080236082276641)
                  ·
                    refine ⟨389949532560177061707481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 519932710080236082276641 389949532560177061707481)
                    ·
                      refine ⟨292462149420132796280611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389949532560177061707481 292462149420132796280611)
                      ·
                        rfl

theorem cell23_569568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_569568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569568 prefixEnd_569568 := by exact prefixLift 569568
  have htrace : WordTrace (prefixWord ++ tailWord_569568) baseStart_569568 baseEnd_569568 := by
    simpa [prefixWord, tailWord_569568, baseEnd_569568] using wordTrace_append hprefix tailTrace_569568
  have hstable : (prefixWord ++ tailWord_569568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569568).length < 2 ^ (prefixWord ++ tailWord_569568).sum := by decide
  have hdescent : baseEnd_569568 < baseStart_569568 := by decide
  rcases family_descends (prefixWord ++ tailWord_569568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569577 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 5, 3, 2]
def baseStart_569577 : Nat := 118140960795 + 569577 * 2 ^ 59
def prefixEnd_569577 : Nat := 4983230072969 + 3 ^ 40 * 569577 * 2
def baseEnd_569577 : Nat := 292466770746023261068069

theorem tailTrace_569577 : CollatzResearch.WordTrace tailWord_569577 prefixEnd_569577 292466770746023261068069 := by
  unfold tailWord_569577
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774179857527279852170985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13849453238351519901447323 20774179857527279852170985)
  ·
    refine ⟨15580634893145459889128239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20774179857527279852170985 15580634893145459889128239)
    ·
      refine ⟨23370952339718189833692359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580634893145459889128239 23370952339718189833692359)
      ·
        refine ⟨35056428509577284750538539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23370952339718189833692359 35056428509577284750538539)
        ·
          refine ⟨52584642764365927125807809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35056428509577284750538539 52584642764365927125807809)
          ·
            refine ⟨39438482073274445344355857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52584642764365927125807809 39438482073274445344355857)
            ·
              refine ⟨29578861554955834008266893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39438482073274445344355857 29578861554955834008266893)
              ·
                refine ⟨11092073083108437753100085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29578861554955834008266893 11092073083108437753100085)
                ·
                  refine ⟨1039881851541416039353133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11092073083108437753100085 1039881851541416039353133)
                  ·
                    refine ⟨389955694328031014757425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039881851541416039353133 389955694328031014757425)
                    ·
                      refine ⟨292466770746023261068069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389955694328031014757425 292466770746023261068069)
                      ·
                        rfl

theorem cell23_569577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 3, 2].length) (baseStart_569577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569577 prefixEnd_569577 := by exact prefixLift 569577
  have htrace : WordTrace (prefixWord ++ tailWord_569577) baseStart_569577 baseEnd_569577 := by
    simpa [prefixWord, tailWord_569577, baseEnd_569577] using wordTrace_append hprefix tailTrace_569577
  have hstable : (prefixWord ++ tailWord_569577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569577).length < 2 ^ (prefixWord ++ tailWord_569577).sum := by decide
  have hdescent : baseEnd_569577 < baseStart_569577 := by decide
  rcases family_descends (prefixWord ++ tailWord_569577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569594 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2]
def baseStart_569594 : Nat := 118140960795 + 569594 * 2 ^ 59
def prefixEnd_569594 : Nat := 4983230072969 + 3 ^ 40 * 569594 * 2
def baseEnd_569594 : Nat := 292475499917149694555491

theorem tailTrace_569594 : CollatzResearch.WordTrace tailWord_569594 prefixEnd_569594 292475499917149694555491 := by
  unfold tailWord_569594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193699974616422938884959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13849866598977127837026557 5193699974616422938884959)
  ·
    refine ⟨7790549961924634408327439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5193699974616422938884959 7790549961924634408327439)
    ·
      refine ⟨11685824942886951612491159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790549961924634408327439 11685824942886951612491159)
      ·
        refine ⟨17528737414330427418736739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685824942886951612491159 17528737414330427418736739)
        ·
          refine ⟨26293106121495641128105109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17528737414330427418736739 26293106121495641128105109)
          ·
            refine ⟨1232489349445108177879927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26293106121495641128105109 1232489349445108177879927)
            ·
              refine ⟨1848734024167662266819891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232489349445108177879927 1848734024167662266819891)
              ·
                refine ⟨2773101036251493400229837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848734024167662266819891 2773101036251493400229837)
                ·
                  refine ⟨1039912888594310025086189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2773101036251493400229837 1039912888594310025086189)
                  ·
                    refine ⟨389967333222866259407321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039912888594310025086189 389967333222866259407321)
                    ·
                      refine ⟨292475499917149694555491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389967333222866259407321 292475499917149694555491)
                      ·
                        rfl

theorem cell23_569594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_569594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569594 prefixEnd_569594 := by exact prefixLift 569594
  have htrace : WordTrace (prefixWord ++ tailWord_569594) baseStart_569594 baseEnd_569594 := by
    simpa [prefixWord, tailWord_569594, baseEnd_569594] using wordTrace_append hprefix tailTrace_569594
  have hstable : (prefixWord ++ tailWord_569594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569594).length < 2 ^ (prefixWord ++ tailWord_569594).sum := by decide
  have hdescent : baseEnd_569594 < baseStart_569594 := by decide
  rcases family_descends (prefixWord ++ tailWord_569594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569611 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 1, 3, 2]
def baseStart_569611 : Nat := 118140960795 + 569611 * 2 ^ 59
def prefixEnd_569611 : Nat := 4983230072969 + 3 ^ 40 * 569611 * 2
def baseEnd_569611 : Nat := 292484229088276128042913

theorem tailTrace_569611 : CollatzResearch.WordTrace tailWord_569611 prefixEnd_569611 292484229088276128042913 := by
  unfold tailWord_569611
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775419939404103658908687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13850279959602735772605791 20775419939404103658908687)
  ·
    refine ⟨31163129909106155488363031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20775419939404103658908687 31163129909106155488363031)
    ·
      refine ⟨46744694863659233232544547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31163129909106155488363031 46744694863659233232544547)
      ·
        refine ⟨70117042295488849848816821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46744694863659233232544547 70117042295488849848816821)
        ·
          refine ⟨6573472715202079673326577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70117042295488849848816821 6573472715202079673326577)
          ·
            refine ⟨4930104536401559754994933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6573472715202079673326577 4930104536401559754994933)
            ·
              refine ⟨462197300287646227030775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4930104536401559754994933 462197300287646227030775)
              ·
                refine ⟨693295950431469340546163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462197300287646227030775 693295950431469340546163)
                ·
                  refine ⟨1039943925647204010819245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693295950431469340546163 1039943925647204010819245)
                  ·
                    refine ⟨389978972117701504057217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039943925647204010819245 389978972117701504057217)
                    ·
                      refine ⟨292484229088276128042913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389978972117701504057217 292484229088276128042913)
                      ·
                        rfl

theorem cell23_569611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 3, 2].length) (baseStart_569611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569611 prefixEnd_569611 := by exact prefixLift 569611
  have htrace : WordTrace (prefixWord ++ tailWord_569611) baseStart_569611 baseEnd_569611 := by
    simpa [prefixWord, tailWord_569611, baseEnd_569611] using wordTrace_append hprefix tailTrace_569611
  have hstable : (prefixWord ++ tailWord_569611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569611).length < 2 ^ (prefixWord ++ tailWord_569611).sum := by decide
  have hdescent : baseEnd_569611 < baseStart_569611 := by decide
  rcases family_descends (prefixWord ++ tailWord_569611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569692 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_569692 : Nat := 118140960795 + 569692 * 2 ^ 59
def prefixEnd_569692 : Nat := 4983230072969 + 3 ^ 40 * 569692 * 2
def baseEnd_569692 : Nat := 292525821021290311130041

theorem tailTrace_569692 : CollatzResearch.WordTrace tailWord_569692 prefixEnd_569692 292525821021290311130041 := by
  unfold tailWord_569692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10389187126055327246303665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13852249501407102995071553 10389187126055327246303665)
  ·
    refine ⟨7791890344541495434727749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10389187126055327246303665 7791890344541495434727749)
    ·
      refine ⟨1460979439601530394011453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7791890344541495434727749 1460979439601530394011453)
      ·
        refine ⟨547867289850573897754295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1460979439601530394011453 547867289850573897754295)
        ·
          refine ⟨821800934775860846631443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547867289850573897754295 821800934775860846631443)
          ·
            refine ⟨1232701402163791269947165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821800934775860846631443 1232701402163791269947165)
            ·
              refine ⟨462263025811421726230187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1232701402163791269947165 462263025811421726230187)
              ·
                refine ⟨693394538717132589345281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462263025811421726230187 693394538717132589345281)
                ·
                  refine ⟨520045904037849442008961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 693394538717132589345281 520045904037849442008961)
                  ·
                    refine ⟨390034428028387081506721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 520045904037849442008961 390034428028387081506721)
                    ·
                      refine ⟨292525821021290311130041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390034428028387081506721 292525821021290311130041)
                      ·
                        rfl

theorem cell23_569692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_569692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569692 prefixEnd_569692 := by exact prefixLift 569692
  have htrace : WordTrace (prefixWord ++ tailWord_569692) baseStart_569692 baseEnd_569692 := by
    simpa [prefixWord, tailWord_569692, baseEnd_569692] using wordTrace_append hprefix tailTrace_569692
  have hstable : (prefixWord ++ tailWord_569692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569692).length < 2 ^ (prefixWord ++ tailWord_569692).sum := by decide
  have hdescent : baseEnd_569692 < baseStart_569692 := by decide
  rcases family_descends (prefixWord ++ tailWord_569692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569737 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 8]
def baseStart_569737 : Nat := 118140960795 + 569737 * 2 ^ 59
def prefixEnd_569737 : Nat := 4983230072969 + 3 ^ 40 * 569737 * 2
def baseEnd_569737 : Nat := 32505436405638070563037

theorem tailTrace_569737 : CollatzResearch.WordTrace tailWord_569737 prefixEnd_569737 32505436405638070563037 := by
  unfold tailWord_569737
  simp only [CollatzResearch.WordTrace]
  refine ⟨20780015536947627177995465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13853343691298418118663643 20780015536947627177995465)
  ·
    refine ⟨15585011652710720383496599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20780015536947627177995465 15585011652710720383496599)
    ·
      refine ⟨23377517479066080575244899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15585011652710720383496599 23377517479066080575244899)
      ·
        refine ⟨35066276218599120862867349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23377517479066080575244899 35066276218599120862867349)
        ·
          refine ⟨1643731697746833790446907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35066276218599120862867349 1643731697746833790446907)
          ·
            refine ⟨2465597546620250685670361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643731697746833790446907 2465597546620250685670361)
            ·
              refine ⟨1849198159965188014252771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465597546620250685670361 1849198159965188014252771)
              ·
                refine ⟨2773797239947782021379157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849198159965188014252771 2773797239947782021379157)
                ·
                  refine ⟨32505436405638070563037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2773797239947782021379157 32505436405638070563037)
                  ·
                    rfl

theorem cell23_569737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_569737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569737 prefixEnd_569737 := by exact prefixLift 569737
  have htrace : WordTrace (prefixWord ++ tailWord_569737) baseStart_569737 baseEnd_569737 := by
    simpa [prefixWord, tailWord_569737, baseEnd_569737] using wordTrace_append hprefix tailTrace_569737
  have hstable : (prefixWord ++ tailWord_569737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569737).length < 2 ^ (prefixWord ++ tailWord_569737).sum := by decide
  have hdescent : baseEnd_569737 < baseStart_569737 := by decide
  rcases family_descends (prefixWord ++ tailWord_569737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569754 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_569754 : Nat := 118140960795 + 569754 * 2 ^ 59
def prefixEnd_569754 : Nat := 4983230072969 + 3 ^ 40 * 569754 * 2
def baseEnd_569754 : Nat := 32506406313541007617195

theorem tailTrace_569754 : CollatzResearch.WordTrace tailWord_569754 prefixEnd_569754 32506406313541007617195 := by
  unfold tailWord_569754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5195158894471509770341079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13853757051924026054242877 5195158894471509770341079)
  ·
    refine ⟨7792738341707264655511619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5195158894471509770341079 7792738341707264655511619)
    ·
      refine ⟨11689107512560896983267429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792738341707264655511619 11689107512560896983267429)
      ·
        refine ⟨2191707658605168184362643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11689107512560896983267429 2191707658605168184362643)
        ·
          refine ⟨3287561487907752276543965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191707658605168184362643 3287561487907752276543965)
          ·
            refine ⟨1232835557965407103703987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3287561487907752276543965 1232835557965407103703987)
            ·
              refine ⟨1849253336948110655555981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232835557965407103703987 1849253336948110655555981)
              ·
                refine ⟨693470001355541495833493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849253336948110655555981 693470001355541495833493)
                ·
                  refine ⟨32506406313541007617195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 693470001355541495833493 32506406313541007617195)
                  ·
                    rfl

theorem cell23_569754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_569754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569754 prefixEnd_569754 := by exact prefixLift 569754
  have htrace : WordTrace (prefixWord ++ tailWord_569754) baseStart_569754 baseEnd_569754 := by
    simpa [prefixWord, tailWord_569754, baseEnd_569754] using wordTrace_append hprefix tailTrace_569754
  have hstable : (prefixWord ++ tailWord_569754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569754).length < 2 ^ (prefixWord ++ tailWord_569754).sum := by decide
  have hdescent : baseEnd_569754 < baseStart_569754 := by decide
  rcases family_descends (prefixWord ++ tailWord_569754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569768 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_569768 : Nat := 118140960795 + 569768 * 2 ^ 59
def prefixEnd_569768 : Nat := 4983230072969 + 3 ^ 40 * 569768 * 2
def baseEnd_569768 : Nat := 292564845551032013779691

theorem tailTrace_569768 : CollatzResearch.WordTrace tailWord_569768 prefixEnd_569768 292564845551032013779691 := by
  unfold tailWord_569768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390573099917659736186979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13854097466556879648249305 10390573099917659736186979)
  ·
    refine ⟨15585859649876489604280469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10390573099917659736186979 15585859649876489604280469)
    ·
      refine ⟨730587171087960450200647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15585859649876489604280469 730587171087960450200647)
      ·
        refine ⟨1095880756631940675300971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730587171087960450200647 1095880756631940675300971)
        ·
          refine ⟨1643821134947911012951457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095880756631940675300971 1643821134947911012951457)
          ·
            refine ⟨1232865851210933259713593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643821134947911012951457 1232865851210933259713593)
            ·
              refine ⟨924649388408199944785195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232865851210933259713593 924649388408199944785195)
              ·
                refine ⟨1386974082612299917177793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924649388408199944785195 1386974082612299917177793)
                ·
                  refine ⟨1040230561959224937883345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386974082612299917177793 1040230561959224937883345)
                  ·
                    refine ⟨780172921469418703412509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1040230561959224937883345 780172921469418703412509)
                    ·
                      refine ⟨292564845551032013779691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 780172921469418703412509 292564845551032013779691)
                      ·
                        rfl

theorem cell23_569768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_569768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569768 prefixEnd_569768 := by exact prefixLift 569768
  have htrace : WordTrace (prefixWord ++ tailWord_569768) baseStart_569768 baseEnd_569768 := by
    simpa [prefixWord, tailWord_569768, baseEnd_569768] using wordTrace_append hprefix tailTrace_569768
  have hstable : (prefixWord ++ tailWord_569768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569768).length < 2 ^ (prefixWord ++ tailWord_569768).sum := by decide
  have hdescent : baseEnd_569768 < baseStart_569768 := by decide
  rcases family_descends (prefixWord ++ tailWord_569768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569807 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_569807 : Nat := 118140960795 + 569807 * 2 ^ 59
def prefixEnd_569807 : Nat := 4983230072969 + 3 ^ 40 * 569807 * 2
def baseEnd_569807 : Nat := 292584871296557361192011

theorem tailTrace_569807 : CollatzResearch.WordTrace tailWord_569807 prefixEnd_569807 292584871296557361192011 := by
  unfold tailWord_569807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20782568646694029133043675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13855045764462686088695783 20782568646694029133043675)
  ·
    refine ⟨31173852970041043699565513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20782568646694029133043675 31173852970041043699565513)
    ·
      refine ⟨23380389727530782774674135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31173852970041043699565513 23380389727530782774674135)
      ·
        refine ⟨35070584591296174162011203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23380389727530782774674135 35070584591296174162011203)
        ·
          refine ⟨52605876886944261243016805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35070584591296174162011203 52605876886944261243016805)
          ·
            refine ⟨9863601916302048983065651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52605876886944261243016805 9863601916302048983065651)
            ·
              refine ⟨14795402874453073474598477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9863601916302048983065651 14795402874453073474598477)
              ·
                refine ⟨5548276077919902552974429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14795402874453073474598477 5548276077919902552974429)
                ·
                  refine ⟨2080603529219963457365411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5548276077919902552974429 2080603529219963457365411)
                  ·
                    refine ⟨3120905293829945186048117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2080603529219963457365411 3120905293829945186048117)
                    ·
                      refine ⟨292584871296557361192011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3120905293829945186048117 292584871296557361192011)
                      ·
                        rfl

theorem cell23_569807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_569807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569807 prefixEnd_569807 := by exact prefixLift 569807
  have htrace : WordTrace (prefixWord ++ tailWord_569807) baseStart_569807 baseEnd_569807 := by
    simpa [prefixWord, tailWord_569807, baseEnd_569807] using wordTrace_append hprefix tailTrace_569807
  have hstable : (prefixWord ++ tailWord_569807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569807).length < 2 ^ (prefixWord ++ tailWord_569807).sum := by decide
  have hdescent : baseEnd_569807 < baseStart_569807 := by decide
  rcases family_descends (prefixWord ++ tailWord_569807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569821 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_569821 : Nat := 118140960795 + 569821 * 2 ^ 59
def prefixEnd_569821 : Nat := 4983230072969 + 3 ^ 40 * 569821 * 2
def baseEnd_569821 : Nat := 292592060025720306416947

theorem tailTrace_569821 : CollatzResearch.WordTrace tailWord_569821 prefixEnd_569821 292592060025720306416947 := by
  unfold tailWord_569821
  simp only [CollatzResearch.WordTrace]
  refine ⟨20783079268643309524053317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13855386179095539682702211 20783079268643309524053317)
  ·
    refine ⟨3896827362870620535759997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20783079268643309524053317 3896827362870620535759997)
    ·
      refine ⟨1461310261076482700909999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3896827362870620535759997 1461310261076482700909999)
      ·
        refine ⟨2191965391614724051364999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461310261076482700909999 2191965391614724051364999)
        ·
          refine ⟨3287948087422086077047499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191965391614724051364999 3287948087422086077047499)
          ·
            refine ⟨4931922131133129115571249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287948087422086077047499 4931922131133129115571249)
            ·
              refine ⟨3698941598349846836678437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931922131133129115571249 3698941598349846836678437)
              ·
                refine ⟨693551549690596281877207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3698941598349846836678437 693551549690596281877207)
                ·
                  refine ⟨1040327324535894422815811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693551549690596281877207 1040327324535894422815811)
                  ·
                    refine ⟨1560490986803841634223717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040327324535894422815811 1560490986803841634223717)
                    ·
                      refine ⟨292592060025720306416947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1560490986803841634223717 292592060025720306416947)
                      ·
                        rfl

theorem cell23_569821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_569821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569821 prefixEnd_569821 := by exact prefixLift 569821
  have htrace : WordTrace (prefixWord ++ tailWord_569821) baseStart_569821 baseEnd_569821 := by
    simpa [prefixWord, tailWord_569821, baseEnd_569821] using wordTrace_append hprefix tailTrace_569821
  have hstable : (prefixWord ++ tailWord_569821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569821).length < 2 ^ (prefixWord ++ tailWord_569821).sum := by decide
  have hdescent : baseEnd_569821 < baseStart_569821 := by decide
  rcases family_descends (prefixWord ++ tailWord_569821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569824 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_569824 : Nat := 118140960795 + 569824 * 2 ^ 59
def prefixEnd_569824 : Nat := 4983230072969 + 3 ^ 40 * 569824 * 2
def baseEnd_569824 : Nat := 292593600467683794679433

theorem tailTrace_569824 : CollatzResearch.WordTrace tailWord_569824 prefixEnd_569824 292593600467683794679433 := by
  unfold tailWord_569824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391594343816220518206263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13855459125088294024275017 10391594343816220518206263)
  ·
    refine ⟨15587391515724330777309395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10391594343816220518206263 15587391515724330777309395)
    ·
      refine ⟨23381087273586496165964093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15587391515724330777309395 23381087273586496165964093)
      ·
        refine ⟨8767907727594936062236535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23381087273586496165964093 8767907727594936062236535)
        ·
          refine ⟨13151861591392404093354803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8767907727594936062236535 13151861591392404093354803)
          ·
            refine ⟨19727792387088606140032205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13151861591392404093354803 19727792387088606140032205)
            ·
              refine ⟨7397922145158227302512077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19727792387088606140032205 7397922145158227302512077)
              ·
                refine ⟨2774220804434335238442029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7397922145158227302512077 2774220804434335238442029)
                ·
                  refine ⟨1040332801662875714415761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2774220804434335238442029 1040332801662875714415761)
                  ·
                    refine ⟨780249601247156785811821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1040332801662875714415761 780249601247156785811821)
                    ·
                      refine ⟨292593600467683794679433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 780249601247156785811821 292593600467683794679433)
                      ·
                        rfl

theorem cell23_569824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_569824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569824 prefixEnd_569824 := by exact prefixLift 569824
  have htrace : WordTrace (prefixWord ++ tailWord_569824) baseStart_569824 baseEnd_569824 := by
    simpa [prefixWord, tailWord_569824, baseEnd_569824] using wordTrace_append hprefix tailTrace_569824
  have hstable : (prefixWord ++ tailWord_569824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569824).length < 2 ^ (prefixWord ++ tailWord_569824).sum := by decide
  have hdescent : baseEnd_569824 < baseStart_569824 := by decide
  rcases family_descends (prefixWord ++ tailWord_569824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569838 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_569838 : Nat := 118140960795 + 569838 * 2 ^ 59
def prefixEnd_569838 : Nat := 4983230072969 + 3 ^ 40 * 569838 * 2
def baseEnd_569838 : Nat := 292600789196846739904369

theorem tailTrace_569838 : CollatzResearch.WordTrace tailWord_569838 prefixEnd_569838 292600789196846739904369 := by
  unfold tailWord_569838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597962413697715178427771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13855799539721147618281445 2597962413697715178427771)
  ·
    refine ⟨3896943620546572767641657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597962413697715178427771 3896943620546572767641657)
    ·
      refine ⟨2922707715409929575731243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3896943620546572767641657 2922707715409929575731243)
      ·
        refine ⟨4384061573114894363596865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922707715409929575731243 4384061573114894363596865)
        ·
          refine ⟨3288046179836170772697649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384061573114894363596865 3288046179836170772697649)
          ·
            refine ⟨2466034634877128079523237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288046179836170772697649 2466034634877128079523237)
            ·
              refine ⟨462381494039461514910607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2466034634877128079523237 462381494039461514910607)
              ·
                refine ⟨693572241059192272365911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462381494039461514910607 693572241059192272365911)
                ·
                  refine ⟨1040358361588788408548867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693572241059192272365911 1040358361588788408548867)
                  ·
                    refine ⟨1560537542383182612823301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040358361588788408548867 1560537542383182612823301)
                    ·
                      refine ⟨292600789196846739904369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1560537542383182612823301 292600789196846739904369)
                      ·
                        rfl

theorem cell23_569838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_569838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569838 prefixEnd_569838 := by exact prefixLift 569838
  have htrace : WordTrace (prefixWord ++ tailWord_569838) baseStart_569838 baseEnd_569838 := by
    simpa [prefixWord, tailWord_569838, baseEnd_569838] using wordTrace_append hprefix tailTrace_569838
  have hstable : (prefixWord ++ tailWord_569838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569838).length < 2 ^ (prefixWord ++ tailWord_569838).sum := by decide
  have hdescent : baseEnd_569838 < baseStart_569838 := by decide
  rcases family_descends (prefixWord ++ tailWord_569838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569841 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 3]
def baseStart_569841 : Nat := 118140960795 + 569841 * 2 ^ 59
def prefixEnd_569841 : Nat := 4983230072969 + 3 ^ 40 * 569841 * 2
def baseEnd_569841 : Nat := 292602329638810228166855

theorem tailTrace_569841 : CollatzResearch.WordTrace tailWord_569841 prefixEnd_569841 292602329638810228166855 := by
  unfold tailWord_569841
  simp only [CollatzResearch.WordTrace]
  refine ⟨20783808728570852939781377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13855872485713901959854251 20783808728570852939781377)
  ·
    refine ⟨15587856546428139704836033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20783808728570852939781377 15587856546428139704836033)
    ·
      refine ⟨11690892409821104778627025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15587856546428139704836033 11690892409821104778627025)
      ·
        refine ⟨8768169307365828583970269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11690892409821104778627025 8768169307365828583970269)
        ·
          refine ⟨3288063490262185718988851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8768169307365828583970269 3288063490262185718988851)
          ·
            refine ⟨4932095235393278578483277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288063490262185718988851 4932095235393278578483277)
            ·
              refine ⟨1849535713272479466931229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4932095235393278578483277 1849535713272479466931229)
              ·
                refine ⟨693575892477179800099211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849535713272479466931229 693575892477179800099211)
                ·
                  refine ⟨1040363838715769700148817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693575892477179800099211 1040363838715769700148817)
                  ·
                    refine ⟨780272879036827275111613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1040363838715769700148817 780272879036827275111613)
                    ·
                      refine ⟨292602329638810228166855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 780272879036827275111613 292602329638810228166855)
                      ·
                        rfl

theorem cell23_569841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_569841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569841 prefixEnd_569841 := by exact prefixLift 569841
  have htrace : WordTrace (prefixWord ++ tailWord_569841) baseStart_569841 baseEnd_569841 := by
    simpa [prefixWord, tailWord_569841, baseEnd_569841] using wordTrace_append hprefix tailTrace_569841
  have hstable : (prefixWord ++ tailWord_569841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569841).length < 2 ^ (prefixWord ++ tailWord_569841).sum := by decide
  have hdescent : baseEnd_569841 < baseStart_569841 := by decide
  rcases family_descends (prefixWord ++ tailWord_569841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569858 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_569858 : Nat := 118140960795 + 569858 * 2 ^ 59
def prefixEnd_569858 : Nat := 4983230072969 + 3 ^ 40 * 569858 * 2
def baseEnd_569858 : Nat := 292611058809936661654277

theorem tailTrace_569858 : CollatzResearch.WordTrace tailWord_569858 prefixEnd_569858 292611058809936661654277 := by
  unfold tailWord_569858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196107192377316210787557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13856285846339509895433485 5196107192377316210787557)
  ·
    refine ⟨974270098570746789522667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5196107192377316210787557 974270098570746789522667)
    ·
      refine ⟨1461405147856120184284001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 974270098570746789522667 1461405147856120184284001)
      ·
        refine ⟨1096053860892090138213001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1461405147856120184284001 1096053860892090138213001)
        ·
          refine ⟨822040395669067603659751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1096053860892090138213001 822040395669067603659751)
          ·
            refine ⟨1233060593503601405489627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822040395669067603659751 1233060593503601405489627)
            ·
              refine ⟨1849590890255402108234441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233060593503601405489627 1849590890255402108234441)
              ·
                refine ⟨1387193167691551581175831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849590890255402108234441 1387193167691551581175831)
                ·
                  refine ⟨2080789751537327371763747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387193167691551581175831 2080789751537327371763747)
                  ·
                    refine ⟨3121184627305991057645621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2080789751537327371763747 3121184627305991057645621)
                    ·
                      refine ⟨292611058809936661654277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3121184627305991057645621 292611058809936661654277)
                      ·
                        rfl

theorem cell23_569858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_569858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569858 prefixEnd_569858 := by exact prefixLift 569858
  have htrace : WordTrace (prefixWord ++ tailWord_569858) baseStart_569858 baseEnd_569858 := by
    simpa [prefixWord, tailWord_569858, baseEnd_569858] using wordTrace_append hprefix tailTrace_569858
  have hstable : (prefixWord ++ tailWord_569858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569858).length < 2 ^ (prefixWord ++ tailWord_569858).sum := by decide
  have hdescent : baseEnd_569858 < baseStart_569858 := by decide
  rcases family_descends (prefixWord ++ tailWord_569858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569884 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_569884 : Nat := 118140960795 + 569884 * 2 ^ 59
def prefixEnd_569884 : Nat := 4983230072969 + 3 ^ 40 * 569884 * 2
def baseEnd_569884 : Nat := 292624409306953559929157

theorem tailTrace_569884 : CollatzResearch.WordTrace tailWord_569884 prefixEnd_569884 292624409306953559929157 := by
  unfold tailWord_569884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392688533707535641798353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13856918044943380855731137 10392688533707535641798353)
  ·
    refine ⟨7794516400280651731348765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10392688533707535641798353 7794516400280651731348765)
    ·
      refine ⟨2922943650105244399255787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7794516400280651731348765 2922943650105244399255787)
      ·
        refine ⟨4384415475157866598883681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922943650105244399255787 4384415475157866598883681)
        ·
          refine ⟨3288311606368399949162761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384415475157866598883681 3288311606368399949162761)
          ·
            refine ⟨2466233704776299961872071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288311606368399949162761 2466233704776299961872071)
            ·
              refine ⟨3699350557164449942808107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466233704776299961872071 3699350557164449942808107)
              ·
                refine ⟨5549025835746674914212161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699350557164449942808107 5549025835746674914212161)
                ·
                  refine ⟨4161769376810006185659121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5549025835746674914212161 4161769376810006185659121)
                  ·
                    refine ⟨3121327032607504639244341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4161769376810006185659121 3121327032607504639244341)
                    ·
                      refine ⟨292624409306953559929157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3121327032607504639244341 292624409306953559929157)
                      ·
                        rfl

theorem cell23_569884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_569884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569884 prefixEnd_569884 := by exact prefixLift 569884
  have htrace : WordTrace (prefixWord ++ tailWord_569884) baseStart_569884 baseEnd_569884 := by
    simpa [prefixWord, tailWord_569884, baseEnd_569884] using wordTrace_append hprefix tailTrace_569884
  have hstable : (prefixWord ++ tailWord_569884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569884).length < 2 ^ (prefixWord ++ tailWord_569884).sum := by decide
  have hdescent : baseEnd_569884 < baseStart_569884 := by decide
  rcases family_descends (prefixWord ++ tailWord_569884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569934 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_569934 : Nat := 118140960795 + 569934 * 2 ^ 59
def prefixEnd_569934 : Nat := 4983230072969 + 3 ^ 40 * 569934 * 2
def baseEnd_569934 : Nat := 32516675926630929367103

theorem tailTrace_569934 : CollatzResearch.WordTrace tailWord_569934 prefixEnd_569934 32516675926630929367103 := by
  unfold tailWord_569934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598400089654241227864607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13858133811489286548611237 2598400089654241227864607)
  ·
    refine ⟨3897600134481361841796911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2598400089654241227864607 3897600134481361841796911)
    ·
      refine ⟨5846400201722042762695367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3897600134481361841796911 5846400201722042762695367)
      ·
        refine ⟨8769600302583064144043051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5846400201722042762695367 8769600302583064144043051)
        ·
          refine ⟨13154400453874596216064577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8769600302583064144043051 13154400453874596216064577)
          ·
            refine ⟨9865800340405947162048433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13154400453874596216064577 9865800340405947162048433)
            ·
              refine ⟨7399350255304460371536325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9865800340405947162048433 7399350255304460371536325)
              ·
                refine ⟨1387378172869586319663061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7399350255304460371536325 1387378172869586319663061)
                ·
                  refine ⟨32516675926630929367103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1387378172869586319663061 32516675926630929367103)
                  ·
                    rfl

theorem cell23_569934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_569934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569934 prefixEnd_569934 := by exact prefixLift 569934
  have htrace : WordTrace (prefixWord ++ tailWord_569934) baseStart_569934 baseEnd_569934 := by
    simpa [prefixWord, tailWord_569934, baseEnd_569934] using wordTrace_append hprefix tailTrace_569934
  have hstable : (prefixWord ++ tailWord_569934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569934).length < 2 ^ (prefixWord ++ tailWord_569934).sum := by decide
  have hdescent : baseEnd_569934 < baseStart_569934 := by decide
  rcases family_descends (prefixWord ++ tailWord_569934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569968 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 5]
def baseStart_569968 : Nat := 118140960795 + 569968 * 2 ^ 59
def prefixEnd_569968 : Nat := 4983230072969 + 3 ^ 40 * 569968 * 2
def baseEnd_569968 : Nat := 32518615742436803475419

theorem tailTrace_569968 : CollatzResearch.WordTrace tailWord_569968 prefixEnd_569968 32518615742436803475419 := by
  unfold tailWord_569968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394220399555376814827279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13858960532740502419769705 10394220399555376814827279)
  ·
    refine ⟨15591330599333065222240919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394220399555376814827279 15591330599333065222240919)
    ·
      refine ⟨23386995898999597833361379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591330599333065222240919 23386995898999597833361379)
      ·
        refine ⟨35080493848499396750042069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23386995898999597833361379 35080493848499396750042069)
        ·
          refine ⟨822199074574204611329111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35080493848499396750042069 822199074574204611329111)
          ·
            refine ⟨1233298611861306916993667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822199074574204611329111 1233298611861306916993667)
            ·
              refine ⟨1849947917791960375490501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233298611861306916993667 1849947917791960375490501)
              ·
                refine ⟨346865234585992570404469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1849947917791960375490501 346865234585992570404469)
                ·
                  refine ⟨32518615742436803475419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 346865234585992570404469 32518615742436803475419)
                  ·
                    rfl

theorem cell23_569968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 5].length) (baseStart_569968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569968 prefixEnd_569968 := by exact prefixLift 569968
  have htrace : WordTrace (prefixWord ++ tailWord_569968) baseStart_569968 baseEnd_569968 := by
    simpa [prefixWord, tailWord_569968, baseEnd_569968] using wordTrace_append hprefix tailTrace_569968
  have hstable : (prefixWord ++ tailWord_569968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569968).length < 2 ^ (prefixWord ++ tailWord_569968).sum := by decide
  have hdescent : baseEnd_569968 < baseStart_569968 := by decide
  rcases family_descends (prefixWord ++ tailWord_569968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570021 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_570021 : Nat := 118140960795 + 570021 * 2 ^ 59
def prefixEnd_570021 : Nat := 4983230072969 + 3 ^ 40 * 570021 * 2
def baseEnd_570021 : Nat := 292694756156619523916027

theorem tailTrace_570021 : CollatzResearch.WordTrace tailWord_570021 prefixEnd_570021 292694756156619523916027 := by
  unfold tailWord_570021
  simp only [CollatzResearch.WordTrace]
  refine ⟨20790373867918743681333917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13860249245279162454222611 20790373867918743681333917)
  ·
    refine ⟨7796390200469528880500219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20790373867918743681333917 7796390200469528880500219)
    ·
      refine ⟨11694585300704293320750329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7796390200469528880500219 11694585300704293320750329)
      ·
        refine ⟨8770938975528219990562747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11694585300704293320750329 8770938975528219990562747)
        ·
          refine ⟨13156408463292329985844121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8770938975528219990562747 13156408463292329985844121)
          ·
            refine ⟨9867306347469247489383091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13156408463292329985844121 9867306347469247489383091)
            ·
              refine ⟨14800959521203871234074637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9867306347469247489383091 14800959521203871234074637)
              ·
                refine ⟨5550359820451451712777989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14800959521203871234074637 5550359820451451712777989)
                ·
                  refine ⟨1040692466334647196145873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5550359820451451712777989 1040692466334647196145873)
                  ·
                    refine ⟨780519349750985397109405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1040692466334647196145873 780519349750985397109405)
                    ·
                      refine ⟨292694756156619523916027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 780519349750985397109405 292694756156619523916027)
                      ·
                        rfl

theorem cell23_570021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_570021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570021 prefixEnd_570021 := by exact prefixLift 570021
  have htrace : WordTrace (prefixWord ++ tailWord_570021) baseStart_570021 baseEnd_570021 := by
    simpa [prefixWord, tailWord_570021, baseEnd_570021] using wordTrace_append hprefix tailTrace_570021
  have hstable : (prefixWord ++ tailWord_570021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570021).length < 2 ^ (prefixWord ++ tailWord_570021).sum := by decide
  have hdescent : baseEnd_570021 < baseStart_570021 := by decide
  rcases family_descends (prefixWord ++ tailWord_570021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570062 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_570062 : Nat := 118140960795 + 570062 * 2 ^ 59
def prefixEnd_570062 : Nat := 4983230072969 + 3 ^ 40 * 570062 * 2
def baseEnd_570062 : Nat := 97571936287817954501113

theorem tailTrace_570062 : CollatzResearch.WordTrace tailWord_570062 prefixEnd_570062 97571936287817954501113 := by
  unfold tailWord_570062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598983657596275960447055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13861246173846805122384293 2598983657596275960447055)
  ·
    refine ⟨3898475486394413940670583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2598983657596275960447055 3898475486394413940670583)
    ·
      refine ⟨5847713229591620911005875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3898475486394413940670583 5847713229591620911005875)
      ·
        refine ⟨8771569844387431366508813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5847713229591620911005875 8771569844387431366508813)
        ·
          refine ⟨3289338691645286762440805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8771569844387431366508813 3289338691645286762440805)
          ·
            refine ⟨616751004683491267957651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3289338691645286762440805 616751004683491267957651)
            ·
              refine ⟨925126507025236901936477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616751004683491267957651 925126507025236901936477)
              ·
                refine ⟨346922440134463838226179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925126507025236901936477 346922440134463838226179)
                ·
                  refine ⟨520383660201695757339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346922440134463838226179 520383660201695757339269)
                  ·
                    refine ⟨97571936287817954501113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520383660201695757339269 97571936287817954501113)
                    ·
                      rfl

theorem cell23_570062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_570062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570062 prefixEnd_570062 := by exact prefixLift 570062
  have htrace : WordTrace (prefixWord ++ tailWord_570062) baseStart_570062 baseEnd_570062 := by
    simpa [prefixWord, tailWord_570062, baseEnd_570062] using wordTrace_append hprefix tailTrace_570062
  have hstable : (prefixWord ++ tailWord_570062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570062).length < 2 ^ (prefixWord ++ tailWord_570062).sum := by decide
  have hdescent : baseEnd_570062 < baseStart_570062 := by decide
  rcases family_descends (prefixWord ++ tailWord_570062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570064 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_570064 : Nat := 118140960795 + 570064 * 2 ^ 59
def prefixEnd_570064 : Nat := 4983230072969 + 3 ^ 40 * 570064 * 2
def baseEnd_570064 : Nat := 292716835824762855678329

theorem tailTrace_570064 : CollatzResearch.WordTrace tailWord_570064 prefixEnd_570064 292716835824762855678329 := by
  unfold tailWord_570064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10395971103381481012574623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13861294804508641350099497 10395971103381481012574623)
  ·
    refine ⟨15593956655072221518861935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10395971103381481012574623 15593956655072221518861935)
    ·
      refine ⟨23390934982608332278292903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15593956655072221518861935 23390934982608332278292903)
      ·
        refine ⟨35086402473912498417439355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23390934982608332278292903 35086402473912498417439355)
        ·
          refine ⟨52629603710868747626159033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35086402473912498417439355 52629603710868747626159033)
          ·
            refine ⟨39472202783151560719619275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52629603710868747626159033 39472202783151560719619275)
            ·
              refine ⟨59208304174727341079428913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39472202783151560719619275 59208304174727341079428913)
              ·
                refine ⟨44406228131045505809571685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59208304174727341079428913 44406228131045505809571685)
                ·
                  refine ⟨8326167774571032339294691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44406228131045505809571685 8326167774571032339294691)
                  ·
                    refine ⟨12489251661856548508942037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8326167774571032339294691 12489251661856548508942037)
                    ·
                      refine ⟨292716835824762855678329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12489251661856548508942037 292716835824762855678329)
                      ·
                        rfl

theorem cell23_570064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_570064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570064 prefixEnd_570064 := by exact prefixLift 570064
  have htrace : WordTrace (prefixWord ++ tailWord_570064) baseStart_570064 baseEnd_570064 := by
    simpa [prefixWord, tailWord_570064, baseEnd_570064] using wordTrace_append hprefix tailTrace_570064
  have hstable : (prefixWord ++ tailWord_570064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570064).length < 2 ^ (prefixWord ++ tailWord_570064).sum := by decide
  have hdescent : baseEnd_570064 < baseStart_570064 := by decide
  rcases family_descends (prefixWord ++ tailWord_570064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570085 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_570085 : Nat := 118140960795 + 570085 * 2 ^ 59
def prefixEnd_570085 : Nat := 4983230072969 + 3 ^ 40 * 570085 * 2
def baseEnd_570085 : Nat := 292727618918507273515733

theorem tailTrace_570085 : CollatzResearch.WordTrace tailWord_570085 prefixEnd_570085 292727618918507273515733 := by
  unfold tailWord_570085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20792708139686882611663709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13861805426457921741109139 20792708139686882611663709)
  ·
    refine ⟨7797265552382580979373891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20792708139686882611663709 7797265552382580979373891)
    ·
      refine ⟨11695898328573871469060837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7797265552382580979373891 11695898328573871469060837)
      ·
        refine ⟨2192980936607600900448907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11695898328573871469060837 2192980936607600900448907)
        ·
          refine ⟨3289471404911401350673361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192980936607600900448907 3289471404911401350673361)
          ·
            refine ⟨2467103553683551013005021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3289471404911401350673361 2467103553683551013005021)
            ·
              refine ⟨925163832631331629876883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2467103553683551013005021 925163832631331629876883)
              ·
                refine ⟨1387745748946997444815325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925163832631331629876883 1387745748946997444815325)
                ·
                  refine ⟨520404655855124041805747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1387745748946997444815325 520404655855124041805747)
                  ·
                    refine ⟨780606983782686062708621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 520404655855124041805747 780606983782686062708621)
                    ·
                      refine ⟨292727618918507273515733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 780606983782686062708621 292727618918507273515733)
                      ·
                        rfl

theorem cell23_570085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_570085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570085 prefixEnd_570085 := by exact prefixLift 570085
  have htrace : WordTrace (prefixWord ++ tailWord_570085) baseStart_570085 baseEnd_570085 := by
    simpa [prefixWord, tailWord_570085, baseEnd_570085] using wordTrace_append hprefix tailTrace_570085
  have hstable : (prefixWord ++ tailWord_570085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570085).length < 2 ^ (prefixWord ++ tailWord_570085).sum := by decide
  have hdescent : baseEnd_570085 < baseStart_570085 := by decide
  rcases family_descends (prefixWord ++ tailWord_570085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570091 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4]
def baseStart_570091 : Nat := 118140960795 + 570091 * 2 ^ 59
def prefixEnd_570091 : Nat := 4983230072969 + 3 ^ 40 * 570091 * 2
def baseEnd_570091 : Nat := 292730699802434250040705

theorem tailTrace_570091 : CollatzResearch.WordTrace tailWord_570091 prefixEnd_570091 292730699802434250040705 := by
  unfold tailWord_570091
  simp only [CollatzResearch.WordTrace]
  refine ⟨20792926977665145636382127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13861951318443430424254751 20792926977665145636382127)
  ·
    refine ⟨31189390466497718454573191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20792926977665145636382127 31189390466497718454573191)
    ·
      refine ⟨46784085699746577681859787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31189390466497718454573191 46784085699746577681859787)
      ·
        refine ⟨70176128549619866522789681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46784085699746577681859787 70176128549619866522789681)
        ·
          refine ⟨52632096412214899892092261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70176128549619866522789681 52632096412214899892092261)
          ·
            refine ⟨9868518077290293729767299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52632096412214899892092261 9868518077290293729767299)
            ·
              refine ⟨14802777115935440594650949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9868518077290293729767299 14802777115935440594650949)
              ·
                refine ⟨2775520709237895111497053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14802777115935440594650949 2775520709237895111497053)
                ·
                  refine ⟨1040820265964210666811395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2775520709237895111497053 1040820265964210666811395)
                  ·
                    refine ⟨1561230398946316000217093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040820265964210666811395 1561230398946316000217093)
                    ·
                      refine ⟨292730699802434250040705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1561230398946316000217093 292730699802434250040705)
                      ·
                        rfl

theorem cell23_570091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 4].length) (baseStart_570091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570091 prefixEnd_570091 := by exact prefixLift 570091
  have htrace : WordTrace (prefixWord ++ tailWord_570091) baseStart_570091 baseEnd_570091 := by
    simpa [prefixWord, tailWord_570091, baseEnd_570091] using wordTrace_append hprefix tailTrace_570091
  have hstable : (prefixWord ++ tailWord_570091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570091).length < 2 ^ (prefixWord ++ tailWord_570091).sum := by decide
  have hdescent : baseEnd_570091 < baseStart_570091 := by decide
  rcases family_descends (prefixWord ++ tailWord_570091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570108 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_570108 : Nat := 118140960795 + 570108 * 2 ^ 59
def prefixEnd_570108 : Nat := 4983230072969 + 3 ^ 40 * 570108 * 2
def baseEnd_570108 : Nat := 292739428973560683528127

theorem tailTrace_570108 : CollatzResearch.WordTrace tailWord_570108 prefixEnd_570108 292739428973560683528127 := by
  unfold tailWord_570108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10396773509301778769875489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13862364679069038359833985 10396773509301778769875489)
  ·
    refine ⟨7797580131976334077406617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10396773509301778769875489 7797580131976334077406617)
    ·
      refine ⟨5848185098982250558054963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7797580131976334077406617 5848185098982250558054963)
      ·
        refine ⟨8772277648473375837082445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5848185098982250558054963 8772277648473375837082445)
        ·
          refine ⟨3289604118177515938905917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8772277648473375837082445 3289604118177515938905917)
          ·
            refine ⟨1233601544316568477089719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3289604118177515938905917 1233601544316568477089719)
            ·
              refine ⟨1850402316474852715634579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233601544316568477089719 1850402316474852715634579)
              ·
                refine ⟨2775603474712279073451869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850402316474852715634579 2775603474712279073451869)
                ·
                  refine ⟨1040851303017104652544451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2775603474712279073451869 1040851303017104652544451)
                  ·
                    refine ⟨1561276954525656978816677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040851303017104652544451 1561276954525656978816677)
                    ·
                      refine ⟨292739428973560683528127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1561276954525656978816677 292739428973560683528127)
                      ·
                        rfl

theorem cell23_570108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_570108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570108 prefixEnd_570108 := by exact prefixLift 570108
  have htrace : WordTrace (prefixWord ++ tailWord_570108) baseStart_570108 baseEnd_570108 := by
    simpa [prefixWord, tailWord_570108, baseEnd_570108] using wordTrace_append hprefix tailTrace_570108
  have hstable : (prefixWord ++ tailWord_570108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570108).length < 2 ^ (prefixWord ++ tailWord_570108).sum := by decide
  have hdescent : baseEnd_570108 < baseStart_570108 := by decide
  rcases family_descends (prefixWord ++ tailWord_570108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570121 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_570121 : Nat := 118140960795 + 570121 * 2 ^ 59
def prefixEnd_570121 : Nat := 4983230072969 + 3 ^ 40 * 570121 * 2
def baseEnd_570121 : Nat := 292746104222069132665567

theorem tailTrace_570121 : CollatzResearch.WordTrace tailWord_570121 prefixEnd_570121 292746104222069132665567 := by
  unfold tailWord_570121
  simp only [CollatzResearch.WordTrace]
  refine ⟨20794021167556460759974217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13862680778370973839982811 20794021167556460759974217)
  ·
    refine ⟨15595515875667345569980663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20794021167556460759974217 15595515875667345569980663)
    ·
      refine ⟨23393273813501018354970995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15595515875667345569980663 23393273813501018354970995)
      ·
        refine ⟨35089910720251527532456493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23393273813501018354970995 35089910720251527532456493)
        ·
          refine ⟨13158716520094322824671185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35089910720251527532456493 13158716520094322824671185)
          ·
            refine ⟨9869037390070742118503389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13158716520094322824671185 9869037390070742118503389)
            ·
              refine ⟨3700889021276528294438771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9869037390070742118503389 3700889021276528294438771)
              ·
                refine ⟨5551333531914792441658157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700889021276528294438771 5551333531914792441658157)
                ·
                  refine ⟨2081750074468047165621809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5551333531914792441658157 2081750074468047165621809)
                  ·
                    refine ⟨1561312555851035374216357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081750074468047165621809 1561312555851035374216357)
                    ·
                      refine ⟨292746104222069132665567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1561312555851035374216357 292746104222069132665567)
                      ·
                        rfl

theorem cell23_570121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_570121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570121 prefixEnd_570121 := by exact prefixLift 570121
  have htrace : WordTrace (prefixWord ++ tailWord_570121) baseStart_570121 baseEnd_570121 := by
    simpa [prefixWord, tailWord_570121, baseEnd_570121] using wordTrace_append hprefix tailTrace_570121
  have hstable : (prefixWord ++ tailWord_570121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570121).length < 2 ^ (prefixWord ++ tailWord_570121).sum := by decide
  have hdescent : baseEnd_570121 < baseStart_570121 := by decide
  rcases family_descends (prefixWord ++ tailWord_570121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570161 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_570161 : Nat := 118140960795 + 570161 * 2 ^ 59
def prefixEnd_570161 : Nat := 4983230072969 + 3 ^ 40 * 570161 * 2
def baseEnd_570161 : Nat := 97588881149416325388461

theorem tailTrace_570161 : CollatzResearch.WordTrace tailWord_570161 prefixEnd_570161 97588881149416325388461 := by
  unfold tailWord_570161
  simp only [CollatzResearch.WordTrace]
  refine ⟨20795480087411547591430337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13863653391607698394286891 20795480087411547591430337)
  ·
    refine ⟨15596610065558660693572753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20795480087411547591430337 15596610065558660693572753)
    ·
      refine ⟨11697457549168995520179565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15596610065558660693572753 11697457549168995520179565)
      ·
        refine ⟨4386546580938373320067337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11697457549168995520179565 4386546580938373320067337)
        ·
          refine ⟨3289909935703779990050503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4386546580938373320067337 3289909935703779990050503)
          ·
            refine ⟨4934864903555669985075755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289909935703779990050503 4934864903555669985075755)
            ·
              refine ⟨7402297355333504977613633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4934864903555669985075755 7402297355333504977613633)
              ·
                refine ⟨5551723016500128733210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7402297355333504977613633 5551723016500128733210225)
                ·
                  refine ⟨4163792262375096549907669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5551723016500128733210225 4163792262375096549907669)
                  ·
                    refine ⟨97588881149416325388461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4163792262375096549907669 97588881149416325388461)
                    ·
                      rfl

theorem cell23_570161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_570161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570161 prefixEnd_570161 := by exact prefixLift 570161
  have htrace : WordTrace (prefixWord ++ tailWord_570161) baseStart_570161 baseEnd_570161 := by
    simpa [prefixWord, tailWord_570161, baseEnd_570161] using wordTrace_append hprefix tailTrace_570161
  have hstable : (prefixWord ++ tailWord_570161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570161).length < 2 ^ (prefixWord ++ tailWord_570161).sum := by decide
  have hdescent : baseEnd_570161 < baseStart_570161 := by decide
  rcases family_descends (prefixWord ++ tailWord_570161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570181 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_570181 : Nat := 118140960795 + 570181 * 2 ^ 59
def prefixEnd_570181 : Nat := 4983230072969 + 3 ^ 40 * 570181 * 2
def baseEnd_570181 : Nat := 292776913061338897915291

theorem tailTrace_570181 : CollatzResearch.WordTrace tailWord_570181 prefixEnd_570181 292776913061338897915291 := by
  unfold tailWord_570181
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796209547339091007158397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13864139698226060671438931 20796209547339091007158397)
  ·
    refine ⟨7798578580252159127684399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20796209547339091007158397 7798578580252159127684399)
    ·
      refine ⟨11697867870378238691526599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798578580252159127684399 11697867870378238691526599)
      ·
        refine ⟨17546801805567358037289899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11697867870378238691526599 17546801805567358037289899)
        ·
          refine ⟨26320202708351037055934849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17546801805567358037289899 26320202708351037055934849)
          ·
            refine ⟨19740152031263277791951137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26320202708351037055934849 19740152031263277791951137)
            ·
              refine ⟨14805114023447458343963353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19740152031263277791951137 14805114023447458343963353)
              ·
                refine ⟨11103835517585593757972515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14805114023447458343963353 11103835517585593757972515)
                ·
                  refine ⟨16655753276378390636958773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11103835517585593757972515 16655753276378390636958773)
                  ·
                    refine ⟨1561476869660474122214885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16655753276378390636958773 1561476869660474122214885)
                    ·
                      refine ⟨292776913061338897915291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1561476869660474122214885 292776913061338897915291)
                      ·
                        rfl

theorem cell23_570181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_570181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570181 prefixEnd_570181 := by exact prefixLift 570181
  have htrace : WordTrace (prefixWord ++ tailWord_570181) baseStart_570181 baseEnd_570181 := by
    simpa [prefixWord, tailWord_570181, baseEnd_570181] using wordTrace_append hprefix tailTrace_570181
  have hstable : (prefixWord ++ tailWord_570181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570181).length < 2 ^ (prefixWord ++ tailWord_570181).sum := by decide
  have hdescent : baseEnd_570181 < baseStart_570181 := by decide
  rcases family_descends (prefixWord ++ tailWord_570181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570322 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_570322 : Nat := 118140960795 + 570322 * 2 ^ 59
def prefixEnd_570322 : Nat := 4983230072969 + 3 ^ 40 * 570322 * 2
def baseEnd_570322 : Nat := 292849313833622846252143

theorem tailTrace_570322 : CollatzResearch.WordTrace tailWord_570322 prefixEnd_570322 292849313833622846252143 := by
  unfold tailWord_570322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200338059957068022010305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13867568159885514725360813 5200338059957068022010305)
  ·
    refine ⟨3900253544967801016507729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5200338059957068022010305 3900253544967801016507729)
    ·
      refine ⟨2925190158725850762380797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3900253544967801016507729 2925190158725850762380797)
      ·
        refine ⟨1096946309522194035892799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2925190158725850762380797 1096946309522194035892799)
        ·
          refine ⟨1645419464283291053839199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096946309522194035892799 1645419464283291053839199)
          ·
            refine ⟨2468129196424936580758799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645419464283291053839199 2468129196424936580758799)
            ·
              refine ⟨3702193794637404871138199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468129196424936580758799 3702193794637404871138199)
              ·
                refine ⟨5553290691956107306707299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702193794637404871138199 5553290691956107306707299)
                ·
                  refine ⟨8329936037934160960060949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5553290691956107306707299 8329936037934160960060949)
                  ·
                    refine ⟨390465751778163795002857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8329936037934160960060949 390465751778163795002857)
                    ·
                      refine ⟨292849313833622846252143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390465751778163795002857 292849313833622846252143)
                      ·
                        rfl

theorem cell23_570322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_570322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570322 prefixEnd_570322 := by exact prefixLift 570322
  have htrace : WordTrace (prefixWord ++ tailWord_570322) baseStart_570322 baseEnd_570322 := by
    simpa [prefixWord, tailWord_570322, baseEnd_570322] using wordTrace_append hprefix tailTrace_570322
  have hstable : (prefixWord ++ tailWord_570322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570322).length < 2 ^ (prefixWord ++ tailWord_570322).sum := by decide
  have hdescent : baseEnd_570322 < baseStart_570322 := by decide
  rcases family_descends (prefixWord ++ tailWord_570322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570382 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_570382 : Nat := 118140960795 + 570382 * 2 ^ 59
def prefixEnd_570382 : Nat := 4983230072969 + 3 ^ 40 * 570382 * 2
def baseEnd_570382 : Nat := 292880122672892611501867

theorem tailTrace_570382 : CollatzResearch.WordTrace tailWord_570382 prefixEnd_570382 292880122672892611501867 := by
  unfold tailWord_570382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600442577451362791903175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13869027079740601556816933 2600442577451362791903175)
  ·
    refine ⟨3900663866177044187854763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600442577451362791903175 3900663866177044187854763)
    ·
      refine ⟨5850995799265566281782145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3900663866177044187854763 5850995799265566281782145)
      ·
        refine ⟨4388246849449174711336609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850995799265566281782145 4388246849449174711336609)
        ·
          refine ⟨3291185137086881033502457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4388246849449174711336609 3291185137086881033502457)
          ·
            refine ⟨2468388852815160775126843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291185137086881033502457 2468388852815160775126843)
            ·
              refine ⟨3702583279222741162690265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468388852815160775126843 3702583279222741162690265)
              ·
                refine ⟨2776937459417055872017699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702583279222741162690265 2776937459417055872017699)
                ·
                  refine ⟨4165406189125583808026549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776937459417055872017699 4165406189125583808026549)
                  ·
                    refine ⟨390506830230523482002489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4165406189125583808026549 390506830230523482002489)
                    ·
                      refine ⟨292880122672892611501867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390506830230523482002489 292880122672892611501867)
                      ·
                        rfl

theorem cell23_570382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_570382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570382 prefixEnd_570382 := by exact prefixLift 570382
  have htrace : WordTrace (prefixWord ++ tailWord_570382) baseStart_570382 baseEnd_570382 := by
    simpa [prefixWord, tailWord_570382, baseEnd_570382] using wordTrace_append hprefix tailTrace_570382
  have hstable : (prefixWord ++ tailWord_570382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570382).length < 2 ^ (prefixWord ++ tailWord_570382).sum := by decide
  have hdescent : baseEnd_570382 < baseStart_570382 := by decide
  rcases family_descends (prefixWord ++ tailWord_570382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570392 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_570392 : Nat := 118140960795 + 570392 * 2 ^ 59
def prefixEnd_570392 : Nat := 4983230072969 + 3 ^ 40 * 570392 * 2
def baseEnd_570392 : Nat := 97628419159812524125607

theorem tailTrace_570392 : CollatzResearch.WordTrace tailWord_570392 prefixEnd_570392 97628419159812524125607 := by
  unfold tailWord_570392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401952674787337021544715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13869270233049782695392953 10401952674787337021544715)
  ·
    refine ⟨15602929012181005532317073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10401952674787337021544715 15602929012181005532317073)
    ·
      refine ⟨11702196759135754149237805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15602929012181005532317073 11702196759135754149237805)
      ·
        refine ⟨4388323784675907805964177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11702196759135754149237805 4388323784675907805964177)
        ·
          refine ⟨3291242838506930854473133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4388323784675907805964177 3291242838506930854473133)
          ·
            refine ⟨1234216064440099070427425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3291242838506930854473133 1234216064440099070427425)
            ·
              refine ⟨925662048330074302820569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234216064440099070427425 925662048330074302820569)
              ·
                refine ⟨694246536247555727115427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925662048330074302820569 694246536247555727115427)
                ·
                  refine ⟨1041369804371333590673141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694246536247555727115427 1041369804371333590673141)
                  ·
                    refine ⟨97628419159812524125607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1041369804371333590673141 97628419159812524125607)
                    ·
                      rfl

theorem cell23_570392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_570392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570392 prefixEnd_570392 := by exact prefixLift 570392
  have htrace : WordTrace (prefixWord ++ tailWord_570392) baseStart_570392 baseEnd_570392 := by
    simpa [prefixWord, tailWord_570392, baseEnd_570392] using wordTrace_append hprefix tailTrace_570392
  have hstable : (prefixWord ++ tailWord_570392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570392).length < 2 ^ (prefixWord ++ tailWord_570392).sum := by decide
  have hdescent : baseEnd_570392 < baseStart_570392 := by decide
  rcases family_descends (prefixWord ++ tailWord_570392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570405 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_570405 : Nat := 118140960795 + 570405 * 2 ^ 59
def prefixEnd_570405 : Nat := 4983230072969 + 3 ^ 40 * 570405 * 2
def baseEnd_570405 : Nat := 97630644242648673838087

theorem tailTrace_570405 : CollatzResearch.WordTrace tailWord_570405 prefixEnd_570405 97630644242648673838087 := by
  unfold tailWord_570405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20804379498527577263312669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13869586332351718175541779 20804379498527577263312669)
  ·
    refine ⟨7801642311947841473742251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20804379498527577263312669 7801642311947841473742251)
    ·
      refine ⟨11702463467921762210613377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7801642311947841473742251 11702463467921762210613377)
      ·
        refine ⟨8776847600941321657960033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11702463467921762210613377 8776847600941321657960033)
        ·
          refine ⟨6582635700705991243470025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8776847600941321657960033 6582635700705991243470025)
          ·
            refine ⟨4936976775529493432602519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6582635700705991243470025 4936976775529493432602519)
            ·
              refine ⟨7405465163294240148903779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4936976775529493432602519 7405465163294240148903779)
              ·
                refine ⟨11108197744941360223355669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7405465163294240148903779 11108197744941360223355669)
                ·
                  refine ⟨520696769294126260469797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11108197744941360223355669 520696769294126260469797)
                  ·
                    refine ⟨97630644242648673838087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520696769294126260469797 97630644242648673838087)
                    ·
                      rfl

theorem cell23_570405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_570405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570405 prefixEnd_570405 := by exact prefixLift 570405
  have htrace : WordTrace (prefixWord ++ tailWord_570405) baseStart_570405 baseEnd_570405 := by
    simpa [prefixWord, tailWord_570405, baseEnd_570405] using wordTrace_append hprefix tailTrace_570405
  have hstable : (prefixWord ++ tailWord_570405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570405).length < 2 ^ (prefixWord ++ tailWord_570405).sum := by decide
  have hdescent : baseEnd_570405 < baseStart_570405 := by decide
  rcases family_descends (prefixWord ++ tailWord_570405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570425 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_570425 : Nat := 118140960795 + 570425 * 2 ^ 59
def prefixEnd_570425 : Nat := 4983230072969 + 3 ^ 40 * 570425 * 2
def baseEnd_570425 : Nat := 292902202341035943264169

theorem tailTrace_570425 : CollatzResearch.WordTrace tailWord_570425 prefixEnd_570425 292902202341035943264169 := by
  unfold tailWord_570425
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805108958455120679040729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13870072638970080452693819 20805108958455120679040729)
  ·
    refine ⟨15603831718841340509280547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20805108958455120679040729 15603831718841340509280547)
    ·
      refine ⟨23405747578262010763920821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15603831718841340509280547 23405747578262010763920821)
      ·
        refine ⟨2194288835462063509117577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23405747578262010763920821 2194288835462063509117577)
        ·
          refine ⟨1645716626596547631838183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2194288835462063509117577 1645716626596547631838183)
          ·
            refine ⟨2468574939894821447757275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645716626596547631838183 2468574939894821447757275)
            ·
              refine ⟨3702862409842232171635913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468574939894821447757275 3702862409842232171635913)
              ·
                refine ⟨2777146807381674128726935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702862409842232171635913 2777146807381674128726935)
                ·
                  refine ⟨4165720211072511193090403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777146807381674128726935 4165720211072511193090403)
                  ·
                    refine ⟨6248580316608766789635605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165720211072511193090403 6248580316608766789635605)
                    ·
                      refine ⟨292902202341035943264169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6248580316608766789635605 292902202341035943264169)
                      ·
                        rfl

theorem cell23_570425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_570425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570425 prefixEnd_570425 := by exact prefixLift 570425
  have htrace : WordTrace (prefixWord ++ tailWord_570425) baseStart_570425 baseEnd_570425 := by
    simpa [prefixWord, tailWord_570425, baseEnd_570425] using wordTrace_append hprefix tailTrace_570425
  have hstable : (prefixWord ++ tailWord_570425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570425).length < 2 ^ (prefixWord ++ tailWord_570425).sum := by decide
  have hdescent : baseEnd_570425 < baseStart_570425 := by decide
  rcases family_descends (prefixWord ++ tailWord_570425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570439 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 2, 4]
def baseStart_570439 : Nat := 118140960795 + 570439 * 2 ^ 59
def prefixEnd_570439 : Nat := 4983230072969 + 3 ^ 40 * 570439 * 2
def baseEnd_570439 : Nat := 97636463690066296163035

theorem tailTrace_570439 : CollatzResearch.WordTrace tailWord_570439 prefixEnd_570439 97636463690066296163035 := by
  unfold tailWord_570439
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805619580404401070050371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13870413053602934046700247 20805619580404401070050371)
  ·
    refine ⟨31208429370606601605075557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20805619580404401070050371 31208429370606601605075557)
    ·
      refine ⟨5851580506988737800951667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31208429370606601605075557 5851580506988737800951667)
      ·
        refine ⟨8777370760483106701427501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5851580506988737800951667 8777370760483106701427501)
        ·
          refine ⟨3291514035181165013035313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8777370760483106701427501 3291514035181165013035313)
          ·
            refine ⟨2468635526385873759776485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291514035181165013035313 2468635526385873759776485)
            ·
              refine ⟨462869161197351329958091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2468635526385873759776485 462869161197351329958091)
              ·
                refine ⟨694303741796026994937137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462869161197351329958091 694303741796026994937137)
                ·
                  refine ⟨520727806347020246202853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694303741796026994937137 520727806347020246202853)
                  ·
                    refine ⟨97636463690066296163035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520727806347020246202853 97636463690066296163035)
                    ·
                      rfl

theorem cell23_570439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_570439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570439 prefixEnd_570439 := by exact prefixLift 570439
  have htrace : WordTrace (prefixWord ++ tailWord_570439) baseStart_570439 baseEnd_570439 := by
    simpa [prefixWord, tailWord_570439, baseEnd_570439] using wordTrace_append hprefix tailTrace_570439
  have hstable : (prefixWord ++ tailWord_570439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570439).length < 2 ^ (prefixWord ++ tailWord_570439).sum := by decide
  have hdescent : baseEnd_570439 < baseStart_570439 := by decide
  rcases family_descends (prefixWord ++ tailWord_570439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570479 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 3]
def baseStart_570479 : Nat := 118140960795 + 570479 * 2 ^ 59
def prefixEnd_570479 : Nat := 4983230072969 + 3 ^ 40 * 570479 * 2
def baseEnd_570479 : Nat := 292929930296378731988921

theorem tailTrace_570479 : CollatzResearch.WordTrace tailWord_570479 prefixEnd_570479 292929930296378731988921 := by
  unfold tailWord_570479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807078500259487901506491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13871385666839658601004327 20807078500259487901506491)
  ·
    refine ⟨31210617750389231852259737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20807078500259487901506491 31210617750389231852259737)
    ·
      refine ⟨23407963312791923889194803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31210617750389231852259737 23407963312791923889194803)
      ·
        refine ⟨35111944969187885833792205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23407963312791923889194803 35111944969187885833792205)
        ·
          refine ⟨13166979363445457187672077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35111944969187885833792205 13166979363445457187672077)
          ·
            refine ⟨4937617261292046445377029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13166979363445457187672077 4937617261292046445377029)
            ·
              refine ⟨925803236492258708508193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4937617261292046445377029 925803236492258708508193)
              ·
                refine ⟨694352427369194031381145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925803236492258708508193 694352427369194031381145)
                ·
                  refine ⟨520764320526895523535859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694352427369194031381145 520764320526895523535859)
                  ·
                    refine ⟨781146480790343285303789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 520764320526895523535859 781146480790343285303789)
                    ·
                      refine ⟨292929930296378731988921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781146480790343285303789 292929930296378731988921)
                      ·
                        rfl

theorem cell23_570479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_570479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570479 prefixEnd_570479 := by exact prefixLift 570479
  have htrace : WordTrace (prefixWord ++ tailWord_570479) baseStart_570479 baseEnd_570479 := by
    simpa [prefixWord, tailWord_570479, baseEnd_570479] using wordTrace_append hprefix tailTrace_570479
  have hstable : (prefixWord ++ tailWord_570479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570479).length < 2 ^ (prefixWord ++ tailWord_570479).sum := by decide
  have hdescent : baseEnd_570479 < baseStart_570479 := by decide
  rcases family_descends (prefixWord ++ tailWord_570479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570519 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_570519 : Nat := 118140960795 + 570519 * 2 ^ 59
def prefixEnd_570519 : Nat := 4983230072969 + 3 ^ 40 * 570519 * 2
def baseEnd_570519 : Nat := 292950469522558575488737

theorem tailTrace_570519 : CollatzResearch.WordTrace tailWord_570519 prefixEnd_570519 292950469522558575488737 := by
  unfold tailWord_570519
  simp only [CollatzResearch.WordTrace]
  refine ⟨20808537420114574732962611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13872358280076383155308407 20808537420114574732962611)
  ·
    refine ⟨31212806130171862099443917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20808537420114574732962611 31212806130171862099443917)
    ·
      refine ⟨11704802298814448287291469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31212806130171862099443917 11704802298814448287291469)
      ·
        refine ⟨4389300862055418107734301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11704802298814448287291469 4389300862055418107734301)
        ·
          refine ⟨1645987823270781790400363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4389300862055418107734301 1645987823270781790400363)
          ·
            refine ⟨2468981734906172685600545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645987823270781790400363 2468981734906172685600545)
            ·
              refine ⟨1851736301179629514200409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468981734906172685600545 1851736301179629514200409)
              ·
                refine ⟨1388802225884722135650307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851736301179629514200409 1388802225884722135650307)
                ·
                  refine ⟨2083203338827083203475461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388802225884722135650307 2083203338827083203475461)
                  ·
                    refine ⟨390600626030078100651649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2083203338827083203475461 390600626030078100651649)
                    ·
                      refine ⟨292950469522558575488737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390600626030078100651649 292950469522558575488737)
                      ·
                        rfl

theorem cell23_570519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_570519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570519 prefixEnd_570519 := by exact prefixLift 570519
  have htrace : WordTrace (prefixWord ++ tailWord_570519) baseStart_570519 baseEnd_570519 := by
    simpa [prefixWord, tailWord_570519, baseEnd_570519] using wordTrace_append hprefix tailTrace_570519
  have hstable : (prefixWord ++ tailWord_570519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570519).length < 2 ^ (prefixWord ++ tailWord_570519).sum := by decide
  have hdescent : baseEnd_570519 < baseStart_570519 := by decide
  rcases family_descends (prefixWord ++ tailWord_570519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570525 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 9]
def baseStart_570525 : Nat := 118140960795 + 570525 * 2 ^ 59
def prefixEnd_570525 : Nat := 4983230072969 + 3 ^ 40 * 570525 * 2
def baseEnd_570525 : Nat := 32550394489609505779301

theorem tailTrace_570525 : CollatzResearch.WordTrace tailWord_570525 prefixEnd_570525 32550394489609505779301 := by
  unfold tailWord_570525
  simp only [CollatzResearch.WordTrace]
  refine ⟨20808756258092837757681029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13872504172061891838454019 20808756258092837757681029)
  ·
    refine ⟨3901641798392407079565193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20808756258092837757681029 3901641798392407079565193)
    ·
      refine ⟨2926231348794305309673895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3901641798392407079565193 2926231348794305309673895)
      ·
        refine ⟨4389347023191457964510843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926231348794305309673895 4389347023191457964510843)
        ·
          refine ⟨6584020534787186946766265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389347023191457964510843 6584020534787186946766265)
          ·
            refine ⟨4938015401090390210074699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6584020534787186946766265 4938015401090390210074699)
            ·
              refine ⟨7407023101635585315112049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4938015401090390210074699 7407023101635585315112049)
              ·
                refine ⟨5555267326226688986334037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7407023101635585315112049 5555267326226688986334037)
                ·
                  refine ⟨32550394489609505779301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5555267326226688986334037 32550394489609505779301)
                  ·
                    rfl

theorem cell23_570525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_570525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570525 prefixEnd_570525 := by exact prefixLift 570525
  have htrace : WordTrace (prefixWord ++ tailWord_570525) baseStart_570525 baseEnd_570525 := by
    simpa [prefixWord, tailWord_570525, baseEnd_570525] using wordTrace_append hprefix tailTrace_570525
  have hstable : (prefixWord ++ tailWord_570525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570525).length < 2 ^ (prefixWord ++ tailWord_570525).sum := by decide
  have hdescent : baseEnd_570525 < baseStart_570525 := by decide
  rcases family_descends (prefixWord ++ tailWord_570525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570530 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_570530 : Nat := 118140960795 + 570530 * 2 ^ 59
def prefixEnd_570530 : Nat := 4983230072969 + 3 ^ 40 * 570530 * 2
def baseEnd_570530 : Nat := 292956117809758032451187

theorem tailTrace_570530 : CollatzResearch.WordTrace tailWord_570530 prefixEnd_570530 292956117809758032451187 := by
  unfold tailWord_570530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202234655768680902903261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13872625748716482407742029 5202234655768680902903261)
  ·
    refine ⟨1950837995913255338588723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5202234655768680902903261 1950837995913255338588723)
    ·
      refine ⟨2926256993869883007883085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950837995913255338588723 2926256993869883007883085)
      ·
        refine ⟨1097346372701206127956157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2926256993869883007883085 1097346372701206127956157)
        ·
          refine ⟨411504889762952297983559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1097346372701206127956157 411504889762952297983559)
          ·
            refine ⟨617257334644428446975339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411504889762952297983559 617257334644428446975339)
            ·
              refine ⟨925886001966642670463009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617257334644428446975339 925886001966642670463009)
              ·
                refine ⟨694414501474982002847257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925886001966642670463009 694414501474982002847257)
                ·
                  refine ⟨520810876106236502135443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694414501474982002847257 520810876106236502135443)
                  ·
                    refine ⟨781216314159354753203165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 520810876106236502135443 781216314159354753203165)
                    ·
                      refine ⟨292956117809758032451187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781216314159354753203165 292956117809758032451187)
                      ·
                        rfl

theorem cell23_570530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_570530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570530 prefixEnd_570530 := by exact prefixLift 570530
  have htrace : WordTrace (prefixWord ++ tailWord_570530) baseStart_570530 baseEnd_570530 := by
    simpa [prefixWord, tailWord_570530, baseEnd_570530] using wordTrace_append hprefix tailTrace_570530
  have hstable : (prefixWord ++ tailWord_570530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570530).length < 2 ^ (prefixWord ++ tailWord_570530).sum := by decide
  have hdescent : baseEnd_570530 < baseStart_570530 := by decide
  rcases family_descends (prefixWord ++ tailWord_570530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570532 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_570532 : Nat := 118140960795 + 570532 * 2 ^ 59
def prefixEnd_570532 : Nat := 4983230072969 + 3 ^ 40 * 570532 * 2
def baseEnd_570532 : Nat := 292957144771067024626177

theorem tailTrace_570532 : CollatzResearch.WordTrace tailWord_570532 prefixEnd_570532 292957144771067024626177 := by
  unfold tailWord_570532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10404505784533738976592925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13872674379378318635457233 10404505784533738976592925)
  ·
    refine ⟨3901689669200152116222347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10404505784533738976592925 3901689669200152116222347)
    ·
      refine ⟨5852534503800228174333521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901689669200152116222347 5852534503800228174333521)
      ·
        refine ⟨4389400877850171130750141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5852534503800228174333521 4389400877850171130750141)
        ·
          refine ⟨1646025329193814174031303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4389400877850171130750141 1646025329193814174031303)
          ·
            refine ⟨2469037993790721261046955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646025329193814174031303 2469037993790721261046955)
            ·
              refine ⟨3703556990686081891570433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469037993790721261046955 3703556990686081891570433)
              ·
                refine ⟨2777667743014561418677825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703556990686081891570433 2777667743014561418677825)
                ·
                  refine ⟨2083250807260921064008369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777667743014561418677825 2083250807260921064008369)
                  ·
                    refine ⟨1562438105445690798006277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083250807260921064008369 1562438105445690798006277)
                    ·
                      refine ⟨292957144771067024626177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1562438105445690798006277 292957144771067024626177)
                      ·
                        rfl

theorem cell23_570532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_570532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570532 prefixEnd_570532 := by exact prefixLift 570532
  have htrace : WordTrace (prefixWord ++ tailWord_570532) baseStart_570532 baseEnd_570532 := by
    simpa [prefixWord, tailWord_570532, baseEnd_570532] using wordTrace_append hprefix tailTrace_570532
  have hstable : (prefixWord ++ tailWord_570532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570532).length < 2 ^ (prefixWord ++ tailWord_570532).sum := by decide
  have hdescent : baseEnd_570532 < baseStart_570532 := by decide
  rcases family_descends (prefixWord ++ tailWord_570532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570553 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 2, 2, 2]
def baseStart_570553 : Nat := 118140960795 + 570553 * 2 ^ 59
def prefixEnd_570553 : Nat := 4983230072969 + 3 ^ 40 * 570553 * 2
def baseEnd_570553 : Nat := 292967927864811442463581

theorem tailTrace_570553 : CollatzResearch.WordTrace tailWord_570553 prefixEnd_570553 292967927864811442463581 := by
  unfold tailWord_570553
  simp only [CollatzResearch.WordTrace]
  refine ⟨20809777501991398539700313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13873185001327599026466875 20809777501991398539700313)
  ·
    refine ⟨15607333126493548904775235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20809777501991398539700313 15607333126493548904775235)
    ·
      refine ⟨23410999689740323357162853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15607333126493548904775235 23410999689740323357162853)
      ·
        refine ⟨4389562441826310629468035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23410999689740323357162853 4389562441826310629468035)
        ·
          refine ⟨6584343662739465944202053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389562441826310629468035 6584343662739465944202053)
          ·
            refine ⟨1234564436763649864537885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6584343662739465944202053 1234564436763649864537885)
            ·
              refine ⟨462961663786368699201707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1234564436763649864537885 462961663786368699201707)
              ·
                refine ⟨694442495679553048802561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462961663786368699201707 694442495679553048802561)
                ·
                  refine ⟨520831871759664786601921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694442495679553048802561 520831871759664786601921)
                  ·
                    refine ⟨390623903819748589951441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 520831871759664786601921 390623903819748589951441)
                    ·
                      refine ⟨292967927864811442463581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390623903819748589951441 292967927864811442463581)
                      ·
                        rfl

theorem cell23_570553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_570553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570553 prefixEnd_570553 := by exact prefixLift 570553
  have htrace : WordTrace (prefixWord ++ tailWord_570553) baseStart_570553 baseEnd_570553 := by
    simpa [prefixWord, tailWord_570553, baseEnd_570553] using wordTrace_append hprefix tailTrace_570553
  have hstable : (prefixWord ++ tailWord_570553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570553).length < 2 ^ (prefixWord ++ tailWord_570553).sum := by decide
  have hdescent : baseEnd_570553 < baseStart_570553 := by decide
  rcases family_descends (prefixWord ++ tailWord_570553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570555 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 6, 5]
def baseStart_570555 : Nat := 118140960795 + 570555 * 2 ^ 59
def prefixEnd_570555 : Nat := 4983230072969 + 3 ^ 40 * 570555 * 2
def baseEnd_570555 : Nat := 97656318275373478212857

theorem tailTrace_570555 : CollatzResearch.WordTrace tailWord_570555 prefixEnd_570555 97656318275373478212857 := by
  unfold tailWord_570555
  simp only [CollatzResearch.WordTrace]
  refine ⟨20809850447984152881273119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13873233631989435254182079 20809850447984152881273119)
  ·
    refine ⟨31214775671976229321909679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20809850447984152881273119 31214775671976229321909679)
    ·
      refine ⟨46822163507964343982864519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31214775671976229321909679 46822163507964343982864519)
      ·
        refine ⟨70233245261946515974296779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46822163507964343982864519 70233245261946515974296779)
        ·
          refine ⟨105349867892919773961445169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70233245261946515974296779 105349867892919773961445169)
          ·
            refine ⟨79012400919689830471083877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105349867892919773961445169 79012400919689830471083877)
            ·
              refine ⟨14814825172441843213328227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79012400919689830471083877 14814825172441843213328227)
              ·
                refine ⟨22222237758662764819992341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14814825172441843213328227 22222237758662764819992341)
                ·
                  refine ⟨1041667394937317100937141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22222237758662764819992341 1041667394937317100937141)
                  ·
                    refine ⟨97656318275373478212857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1041667394937317100937141 97656318275373478212857)
                    ·
                      rfl

theorem cell23_570555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 5].length) (baseStart_570555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570555 prefixEnd_570555 := by exact prefixLift 570555
  have htrace : WordTrace (prefixWord ++ tailWord_570555) baseStart_570555 baseEnd_570555 := by
    simpa [prefixWord, tailWord_570555, baseEnd_570555] using wordTrace_append hprefix tailTrace_570555
  have hstable : (prefixWord ++ tailWord_570555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570555).length < 2 ^ (prefixWord ++ tailWord_570555).sum := by decide
  have hdescent : baseEnd_570555 < baseStart_570555 := by decide
  rcases family_descends (prefixWord ++ tailWord_570555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570565 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_570565 : Nat := 118140960795 + 570565 * 2 ^ 59
def prefixEnd_570565 : Nat := 4983230072969 + 3 ^ 40 * 570565 * 2
def baseEnd_570565 : Nat := 292974089632665395513525

theorem tailTrace_570565 : CollatzResearch.WordTrace tailWord_570565 prefixEnd_570565 292974089632665395513525 := by
  unfold tailWord_570565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20810215177947924589137149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13873476785298616392758099 20810215177947924589137149)
  ·
    refine ⟨7803830691730471720926431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20810215177947924589137149 7803830691730471720926431)
    ·
      refine ⟨11705746037595707581389647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7803830691730471720926431 11705746037595707581389647)
      ·
        refine ⟨17558619056393561372084471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11705746037595707581389647 17558619056393561372084471)
        ·
          refine ⟨26337928584590342058126707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17558619056393561372084471 26337928584590342058126707)
          ·
            refine ⟨39506892876885513087190061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26337928584590342058126707 39506892876885513087190061)
            ·
              refine ⟨14815084828832067407696273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39506892876885513087190061 14815084828832067407696273)
              ·
                refine ⟨11111313621624050555772205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14815084828832067407696273 11111313621624050555772205)
                ·
                  refine ⟨4166742608109018958414577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11111313621624050555772205 4166742608109018958414577)
                  ·
                    refine ⟨3125056956081764218810933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166742608109018958414577 3125056956081764218810933)
                    ·
                      refine ⟨292974089632665395513525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3125056956081764218810933 292974089632665395513525)
                      ·
                        rfl

theorem cell23_570565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_570565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570565 prefixEnd_570565 := by exact prefixLift 570565
  have htrace : WordTrace (prefixWord ++ tailWord_570565) baseStart_570565 baseEnd_570565 := by
    simpa [prefixWord, tailWord_570565, baseEnd_570565] using wordTrace_append hprefix tailTrace_570565
  have hstable : (prefixWord ++ tailWord_570565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570565).length < 2 ^ (prefixWord ++ tailWord_570565).sum := by decide
  have hdescent : baseEnd_570565 < baseStart_570565 := by decide
  rcases family_descends (prefixWord ++ tailWord_570565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570592 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_570592 : Nat := 118140960795 + 570592 * 2 ^ 59
def prefixEnd_570592 : Nat := 4983230072969 + 3 ^ 40 * 570592 * 2
def baseEnd_570592 : Nat := 292987953610336789875901

theorem tailTrace_570592 : CollatzResearch.WordTrace tailWord_570592 prefixEnd_570592 292987953610336789875901 := by
  unfold tailWord_570592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10405599974425054100185015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13874133299233405466913353 10405599974425054100185015)
  ·
    refine ⟨15608399961637581150277523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10405599974425054100185015 15608399961637581150277523)
    ·
      refine ⟨23412599942456371725416285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15608399961637581150277523 23412599942456371725416285)
      ·
        refine ⟨8779724978421139397031107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23412599942456371725416285 8779724978421139397031107)
        ·
          refine ⟨13169587467631709095546661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8779724978421139397031107 13169587467631709095546661)
          ·
            refine ⟨2469297650180945455414999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13169587467631709095546661 2469297650180945455414999)
            ·
              refine ⟨3703946475271418183122499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469297650180945455414999 3703946475271418183122499)
              ·
                refine ⟨5555919712907127274683749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3703946475271418183122499 5555919712907127274683749)
                ·
                  refine ⟨1041734946170086364003203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5555919712907127274683749 1041734946170086364003203)
                  ·
                    refine ⟨1562602419255129546004805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041734946170086364003203 1562602419255129546004805)
                    ·
                      refine ⟨292987953610336789875901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1562602419255129546004805 292987953610336789875901)
                      ·
                        rfl

theorem cell23_570592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_570592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570592 prefixEnd_570592 := by exact prefixLift 570592
  have htrace : WordTrace (prefixWord ++ tailWord_570592) baseStart_570592 baseEnd_570592 := by
    simpa [prefixWord, tailWord_570592, baseEnd_570592] using wordTrace_append hprefix tailTrace_570592
  have hstable : (prefixWord ++ tailWord_570592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570592).length < 2 ^ (prefixWord ++ tailWord_570592).sum := by decide
  have hdescent : baseEnd_570592 < baseStart_570592 := by decide
  rcases family_descends (prefixWord ++ tailWord_570592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570599 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_570599 : Nat := 118140960795 + 570599 * 2 ^ 59
def prefixEnd_570599 : Nat := 4983230072969 + 3 ^ 40 * 570599 * 2
def baseEnd_570599 : Nat := 292991547974918262488369

theorem tailTrace_570599 : CollatzResearch.WordTrace tailWord_570599 prefixEnd_570599 292991547974918262488369 := by
  unfold tailWord_570599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20811455259824748395874851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13874303506549832263916567 20811455259824748395874851)
  ·
    refine ⟨31217182889737122593812277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20811455259824748395874851 31217182889737122593812277)
    ·
      refine ⟨2926610895912855243169901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31217182889737122593812277 2926610895912855243169901)
      ·
        refine ⟨1097479085967320716188713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2926610895912855243169901 1097479085967320716188713)
        ·
          refine ⟨823109314475490537141535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097479085967320716188713 823109314475490537141535)
          ·
            refine ⟨1234663971713235805712303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823109314475490537141535 1234663971713235805712303)
            ·
              refine ⟨1851995957569853708568455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234663971713235805712303 1851995957569853708568455)
              ·
                refine ⟨2777993936354780562852683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851995957569853708568455 2777993936354780562852683)
                ·
                  refine ⟨4166990904532170844279025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777993936354780562852683 4166990904532170844279025)
                  ·
                    refine ⟨3125243178399128133209269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4166990904532170844279025 3125243178399128133209269)
                    ·
                      refine ⟨292991547974918262488369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3125243178399128133209269 292991547974918262488369)
                      ·
                        rfl

theorem cell23_570599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_570599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570599 prefixEnd_570599 := by exact prefixLift 570599
  have htrace : WordTrace (prefixWord ++ tailWord_570599) baseStart_570599 baseEnd_570599 := by
    simpa [prefixWord, tailWord_570599, baseEnd_570599] using wordTrace_append hprefix tailTrace_570599
  have hstable : (prefixWord ++ tailWord_570599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570599).length < 2 ^ (prefixWord ++ tailWord_570599).sum := by decide
  have hdescent : baseEnd_570599 < baseStart_570599 := by decide
  rcases family_descends (prefixWord ++ tailWord_570599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570629 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_570629 : Nat := 118140960795 + 570629 * 2 ^ 59
def prefixEnd_570629 : Nat := 4983230072969 + 3 ^ 40 * 570629 * 2
def baseEnd_570629 : Nat := 293006952394553145113231

theorem tailTrace_570629 : CollatzResearch.WordTrace tailWord_570629 prefixEnd_570629 293006952394553145113231 := by
  unfold tailWord_570629
  simp only [CollatzResearch.WordTrace]
  refine ⟨20812549449716063519466941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13875032966477375679644627 20812549449716063519466941)
  ·
    refine ⟨7804706043643523819800103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20812549449716063519466941 7804706043643523819800103)
    ·
      refine ⟨11707059065465285729700155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804706043643523819800103 11707059065465285729700155)
      ·
        refine ⟨17560588598197928594550233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707059065465285729700155 17560588598197928594550233)
        ·
          refine ⟨13170441448648446445912675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17560588598197928594550233 13170441448648446445912675)
          ·
            refine ⟨19755662172972669668869013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13170441448648446445912675 19755662172972669668869013)
            ·
              refine ⟨926046664358093890728235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19755662172972669668869013 926046664358093890728235)
              ·
                refine ⟨1389069996537140836092353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926046664358093890728235 1389069996537140836092353)
                ·
                  refine ⟨1041802497402855627069265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389069996537140836092353 1041802497402855627069265)
                  ·
                    refine ⟨781351873052141720301949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041802497402855627069265 781351873052141720301949)
                    ·
                      refine ⟨293006952394553145113231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781351873052141720301949 293006952394553145113231)
                      ·
                        rfl

theorem cell23_570629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_570629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570629 prefixEnd_570629 := by exact prefixLift 570629
  have htrace : WordTrace (prefixWord ++ tailWord_570629) baseStart_570629 baseEnd_570629 := by
    simpa [prefixWord, tailWord_570629, baseEnd_570629] using wordTrace_append hprefix tailTrace_570629
  have hstable : (prefixWord ++ tailWord_570629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570629).length < 2 ^ (prefixWord ++ tailWord_570629).sum := by decide
  have hdescent : baseEnd_570629 < baseStart_570629 := by decide
  rcases family_descends (prefixWord ++ tailWord_570629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570653 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_570653 : Nat := 118140960795 + 570653 * 2 ^ 59
def prefixEnd_570653 : Nat := 4983230072969 + 3 ^ 40 * 570653 * 2
def baseEnd_570653 : Nat := 97673091976753683737707

theorem tailTrace_570653 : CollatzResearch.WordTrace tailWord_570653 prefixEnd_570653 97673091976753683737707 := by
  unfold tailWord_570653
  simp only [CollatzResearch.WordTrace]
  refine ⟨20813424801629115618340613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13875616534419410412227075 20813424801629115618340613)
  ·
    refine ⟨3902517150305459178438865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20813424801629115618340613 3902517150305459178438865)
    ·
      refine ⟨2926887862729094383829149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3902517150305459178438865 2926887862729094383829149)
      ·
        refine ⟨1097582948523410393935931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2926887862729094383829149 1097582948523410393935931)
        ·
          refine ⟨1646374422785115590903897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097582948523410393935931 1646374422785115590903897)
          ·
            refine ⟨1234780817088836693177923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646374422785115590903897 1234780817088836693177923)
            ·
              refine ⟨1852171225633255039766885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234780817088836693177923 1852171225633255039766885)
              ·
                refine ⟨347282104806235319956291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1852171225633255039766885 347282104806235319956291)
                ·
                  refine ⟨520923157209352979934437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347282104806235319956291 520923157209352979934437)
                  ·
                    refine ⟨97673091976753683737707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520923157209352979934437 97673091976753683737707)
                    ·
                      rfl

theorem cell23_570653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_570653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570653 prefixEnd_570653 := by exact prefixLift 570653
  have htrace : WordTrace (prefixWord ++ tailWord_570653) baseStart_570653 baseEnd_570653 := by
    simpa [prefixWord, tailWord_570653, baseEnd_570653] using wordTrace_append hprefix tailTrace_570653
  have hstable : (prefixWord ++ tailWord_570653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570653).length < 2 ^ (prefixWord ++ tailWord_570653).sum := by decide
  have hdescent : baseEnd_570653 < baseStart_570653 := by decide
  rcases family_descends (prefixWord ++ tailWord_570653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570686 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_570686 : Nat := 118140960795 + 570686 * 2 ^ 59
def prefixEnd_570686 : Nat := 4983230072969 + 3 ^ 40 * 570686 * 2
def baseEnd_570686 : Nat := 293036220791859422100469

theorem tailTrace_570686 : CollatzResearch.WordTrace tailWord_570686 prefixEnd_570686 293036220791859422100469 := by
  unfold tailWord_570686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601828551313695281786489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13876418940339708169527941 2601828551313695281786489)
  ·
    refine ⟨1951371413485271461339867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2601828551313695281786489 1951371413485271461339867)
    ·
      refine ⟨2927057120227907192009801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951371413485271461339867 2927057120227907192009801)
      ·
        refine ⟨2195292840170930394007351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2927057120227907192009801 2195292840170930394007351)
        ·
          refine ⟨3292939260256395591011027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195292840170930394007351 3292939260256395591011027)
          ·
            refine ⟨4939408890384593386516541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292939260256395591011027 4939408890384593386516541)
            ·
              refine ⟨1852278333894222519943703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4939408890384593386516541 1852278333894222519943703)
              ·
                refine ⟨2778417500841333779915555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852278333894222519943703 2778417500841333779915555)
                ·
                  refine ⟨4167626251262000669873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778417500841333779915555 4167626251262000669873333)
                  ·
                    refine ⟨390714961055812562800625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4167626251262000669873333 390714961055812562800625)
                    ·
                      refine ⟨293036220791859422100469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390714961055812562800625 293036220791859422100469)
                      ·
                        rfl

theorem cell23_570686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_570686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570686 prefixEnd_570686 := by exact prefixLift 570686
  have htrace : WordTrace (prefixWord ++ tailWord_570686) baseStart_570686 baseEnd_570686 := by
    simpa [prefixWord, tailWord_570686, baseEnd_570686] using wordTrace_append hprefix tailTrace_570686
  have hstable : (prefixWord ++ tailWord_570686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570686).length < 2 ^ (prefixWord ++ tailWord_570686).sum := by decide
  have hdescent : baseEnd_570686 < baseStart_570686 := by decide
  rcases family_descends (prefixWord ++ tailWord_570686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570712 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_570712 : Nat := 118140960795 + 570712 * 2 ^ 59
def prefixEnd_570712 : Nat := 4983230072969 + 3 ^ 40 * 570712 * 2
def baseEnd_570712 : Nat := 293049571288876320375349

theorem tailTrace_570712 : CollatzResearch.WordTrace tailWord_570712 prefixEnd_570712 293049571288876320375349 := by
  unfold tailWord_570712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10407788354207684347369195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13877051138943579129825593 10407788354207684347369195)
  ·
    refine ⟨15611682531311526521053793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10407788354207684347369195 15611682531311526521053793)
    ·
      refine ⟨11708761898483644890790345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15611682531311526521053793 11708761898483644890790345)
      ·
        refine ⟨8781571423862733668092759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11708761898483644890790345 8781571423862733668092759)
        ·
          refine ⟨13172357135794100502139139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8781571423862733668092759 13172357135794100502139139)
          ·
            refine ⟨19758535703691150753208709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13172357135794100502139139 19758535703691150753208709)
            ·
              refine ⟨3704725444442090766226633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19758535703691150753208709 3704725444442090766226633)
              ·
                refine ⟨2778544083331568074669975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704725444442090766226633 2778544083331568074669975)
                ·
                  refine ⟨4167816124997352112004963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778544083331568074669975 4167816124997352112004963)
                  ·
                    refine ⟨6251724187496028168007445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4167816124997352112004963 6251724187496028168007445)
                    ·
                      refine ⟨293049571288876320375349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6251724187496028168007445 293049571288876320375349)
                      ·
                        rfl

theorem cell23_570712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_570712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570712 prefixEnd_570712 := by exact prefixLift 570712
  have htrace : WordTrace (prefixWord ++ tailWord_570712) baseStart_570712 baseEnd_570712 := by
    simpa [prefixWord, tailWord_570712, baseEnd_570712] using wordTrace_append hprefix tailTrace_570712
  have hstable : (prefixWord ++ tailWord_570712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570712).length < 2 ^ (prefixWord ++ tailWord_570712).sum := by decide
  have hdescent : baseEnd_570712 < baseStart_570712 := by decide
  rcases family_descends (prefixWord ++ tailWord_570712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570733 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_570733 : Nat := 118140960795 + 570733 * 2 ^ 59
def prefixEnd_570733 : Nat := 4983230072969 + 3 ^ 40 * 570733 * 2
def baseEnd_570733 : Nat := 293060354382620738212753

theorem tailTrace_570733 : CollatzResearch.WordTrace tailWord_570733 prefixEnd_570733 293060354382620738212753 := by
  unfold tailWord_570733
  simp only [CollatzResearch.WordTrace]
  refine ⟨20816342641339289281252853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13877561760892859520835235 20816342641339289281252853)
  ·
    refine ⟨1951532122625558370117455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20816342641339289281252853 1951532122625558370117455)
    ·
      refine ⟨2927298183938337555176183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951532122625558370117455 2927298183938337555176183)
      ·
        refine ⟨4390947275907506332764275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927298183938337555176183 4390947275907506332764275)
        ·
          refine ⟨6586420913861259499146413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390947275907506332764275 6586420913861259499146413)
          ·
            refine ⟨2469907842697972312179905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6586420913861259499146413 2469907842697972312179905)
            ·
              refine ⟨1852430882023479234134929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469907842697972312179905 1852430882023479234134929)
              ·
                refine ⟨1389323161517609425601197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1852430882023479234134929 1389323161517609425601197)
                ·
                  refine ⟨520996185569103534600449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1389323161517609425601197 520996185569103534600449)
                  ·
                    refine ⟨390747139176827650950337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 520996185569103534600449 390747139176827650950337)
                    ·
                      refine ⟨293060354382620738212753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390747139176827650950337 293060354382620738212753)
                      ·
                        rfl

theorem cell23_570733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_570733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570733 prefixEnd_570733 := by exact prefixLift 570733
  have htrace : WordTrace (prefixWord ++ tailWord_570733) baseStart_570733 baseEnd_570733 := by
    simpa [prefixWord, tailWord_570733, baseEnd_570733] using wordTrace_append hprefix tailTrace_570733
  have hstable : (prefixWord ++ tailWord_570733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570733).length < 2 ^ (prefixWord ++ tailWord_570733).sum := by decide
  have hdescent : baseEnd_570733 < baseStart_570733 := by decide
  rcases family_descends (prefixWord ++ tailWord_570733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570736 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_570736 : Nat := 118140960795 + 570736 * 2 ^ 59
def prefixEnd_570736 : Nat := 4983230072969 + 3 ^ 40 * 570736 * 2
def baseEnd_570736 : Nat := 293061894824584226475239

theorem tailTrace_570736 : CollatzResearch.WordTrace tailWord_570736 prefixEnd_570736 293061894824584226475239 := by
  unfold tailWord_570736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10408226030164210396806031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13877634706885613862408041 10408226030164210396806031)
  ·
    refine ⟨15612339045246315595209047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10408226030164210396806031 15612339045246315595209047)
    ·
      refine ⟨23418508567869473392813571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15612339045246315595209047 23418508567869473392813571)
      ·
        refine ⟨35127762851804210089220357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23418508567869473392813571 35127762851804210089220357)
        ·
          refine ⟨6586455534713289391728817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35127762851804210089220357 6586455534713289391728817)
          ·
            refine ⟨4939841651034967043796613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586455534713289391728817 4939841651034967043796613)
            ·
              refine ⟨926220309569056320711865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4939841651034967043796613 926220309569056320711865)
              ·
                refine ⟨694665232176792240533899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926220309569056320711865 694665232176792240533899)
                ·
                  refine ⟨1041997848265188360800849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694665232176792240533899 1041997848265188360800849)
                  ·
                    refine ⟨781498386198891270600637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041997848265188360800849 781498386198891270600637)
                    ·
                      refine ⟨293061894824584226475239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781498386198891270600637 293061894824584226475239)
                      ·
                        rfl

theorem cell23_570736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_570736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570736 prefixEnd_570736 := by exact prefixLift 570736
  have htrace : WordTrace (prefixWord ++ tailWord_570736) baseStart_570736 baseEnd_570736 := by
    simpa [prefixWord, tailWord_570736, baseEnd_570736] using wordTrace_append hprefix tailTrace_570736
  have hstable : (prefixWord ++ tailWord_570736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570736).length < 2 ^ (prefixWord ++ tailWord_570736).sum := by decide
  have hdescent : baseEnd_570736 < baseStart_570736 := by decide
  rcases family_descends (prefixWord ++ tailWord_570736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570749 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_570749 : Nat := 118140960795 + 570749 * 2 ^ 59
def prefixEnd_570749 : Nat := 4983230072969 + 3 ^ 40 * 570749 * 2
def baseEnd_570749 : Nat := 293068570073092675612679

theorem tailTrace_570749 : CollatzResearch.WordTrace tailWord_570749 prefixEnd_570749 293068570073092675612679 := by
  unfold tailWord_570749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20816926209281324013835301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13877950806187549342556867 20816926209281324013835301)
  ·
    refine ⟨3903173664240248252594119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20816926209281324013835301 3903173664240248252594119)
    ·
      refine ⟨5854760496360372378891179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903173664240248252594119 5854760496360372378891179)
      ·
        refine ⟨8782140744540558568336769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5854760496360372378891179 8782140744540558568336769)
        ·
          refine ⟨6586605558405418926252577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782140744540558568336769 6586605558405418926252577)
          ·
            refine ⟨4939954168804064194689433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586605558405418926252577 4939954168804064194689433)
            ·
              refine ⟨3704965626603048146017075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4939954168804064194689433 3704965626603048146017075)
              ·
                refine ⟨5557448439904572219025613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704965626603048146017075 5557448439904572219025613)
                ·
                  refine ⟨2084043164964214582134605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5557448439904572219025613 2084043164964214582134605)
                  ·
                    refine ⟨781516186861580468300477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084043164964214582134605 781516186861580468300477)
                    ·
                      refine ⟨293068570073092675612679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781516186861580468300477 293068570073092675612679)
                      ·
                        rfl

theorem cell23_570749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_570749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570749 prefixEnd_570749 := by exact prefixLift 570749
  have htrace : WordTrace (prefixWord ++ tailWord_570749) baseStart_570749 baseEnd_570749 := by
    simpa [prefixWord, tailWord_570749, baseEnd_570749] using wordTrace_append hprefix tailTrace_570749
  have hstable : (prefixWord ++ tailWord_570749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570749).length < 2 ^ (prefixWord ++ tailWord_570749).sum := by decide
  have hdescent : baseEnd_570749 < baseStart_570749 := by decide
  rcases family_descends (prefixWord ++ tailWord_570749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570783 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 3]
def baseStart_570783 : Nat := 118140960795 + 570783 * 2 ^ 59
def prefixEnd_570783 : Nat := 4983230072969 + 3 ^ 40 * 570783 * 2
def baseEnd_570783 : Nat := 293086028415345542587523

theorem tailTrace_570783 : CollatzResearch.WordTrace tailWord_570783 prefixEnd_570783 293086028415345542587523 := by
  unfold tailWord_570783
  simp only [CollatzResearch.WordTrace]
  refine ⟨20818166291158147820573003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13878777527438765213715335 20818166291158147820573003)
  ·
    refine ⟨31227249436737221730859505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20818166291158147820573003 31227249436737221730859505)
    ·
      refine ⟨23420437077552916298144629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31227249436737221730859505 23420437077552916298144629)
      ·
        refine ⟨2195665976020585902951059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23420437077552916298144629 2195665976020585902951059)
        ·
          refine ⟨3293498964030878854426589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195665976020585902951059 3293498964030878854426589)
          ·
            refine ⟨1235062111511579570409971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3293498964030878854426589 1235062111511579570409971)
            ·
              refine ⟨1852593167267369355614957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235062111511579570409971 1852593167267369355614957)
              ·
                refine ⟨694722437725263508355609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1852593167267369355614957 694722437725263508355609)
                ·
                  refine ⟨521041828293947631266707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 694722437725263508355609 521041828293947631266707)
                  ·
                    refine ⟨781562742440921446900061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 521041828293947631266707 781562742440921446900061)
                    ·
                      refine ⟨293086028415345542587523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781562742440921446900061 293086028415345542587523)
                      ·
                        rfl

theorem cell23_570783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_570783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570783 prefixEnd_570783 := by exact prefixLift 570783
  have htrace : WordTrace (prefixWord ++ tailWord_570783) baseStart_570783 baseEnd_570783 := by
    simpa [prefixWord, tailWord_570783, baseEnd_570783] using wordTrace_append hprefix tailTrace_570783
  have hstable : (prefixWord ++ tailWord_570783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570783).length < 2 ^ (prefixWord ++ tailWord_570783).sum := by decide
  have hdescent : baseEnd_570783 < baseStart_570783 := by decide
  rcases family_descends (prefixWord ++ tailWord_570783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570818 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_570818 : Nat := 118140960795 + 570818 * 2 ^ 59
def prefixEnd_570818 : Nat := 4983230072969 + 3 ^ 40 * 570818 * 2
def baseEnd_570818 : Nat := 293104000238252905649863

theorem tailTrace_570818 : CollatzResearch.WordTrace tailWord_570818 prefixEnd_570818 293104000238252905649863 := by
  unfold tailWord_570818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204860711507837199524277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13879628564020899198731405 5204860711507837199524277)
  ·
    refine ⟨487955691703859737455401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5204860711507837199524277 487955691703859737455401)
    ·
      refine ⟨365966768777894803091551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 487955691703859737455401 365966768777894803091551)
      ·
        refine ⟨548950153166842204637327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365966768777894803091551 548950153166842204637327)
        ·
          refine ⟨823425229750263306955991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548950153166842204637327 823425229750263306955991)
          ·
            refine ⟨1235137844625394960433987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823425229750263306955991 1235137844625394960433987)
            ·
              refine ⟨1852706766938092440650981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235137844625394960433987 1852706766938092440650981)
              ·
                refine ⟨347382518800892332622059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1852706766938092440650981 347382518800892332622059)
                ·
                  refine ⟨521073778201338498933089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347382518800892332622059 521073778201338498933089)
                  ·
                    refine ⟨390805333651003874199817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 521073778201338498933089 390805333651003874199817)
                    ·
                      refine ⟨293104000238252905649863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390805333651003874199817 293104000238252905649863)
                      ·
                        rfl

theorem cell23_570818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_570818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570818 prefixEnd_570818 := by exact prefixLift 570818
  have htrace : WordTrace (prefixWord ++ tailWord_570818) baseStart_570818 baseEnd_570818 := by
    simpa [prefixWord, tailWord_570818, baseEnd_570818] using wordTrace_append hprefix tailTrace_570818
  have hstable : (prefixWord ++ tailWord_570818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570818).length < 2 ^ (prefixWord ++ tailWord_570818).sum := by decide
  have hdescent : baseEnd_570818 < baseStart_570818 := by decide
  rcases family_descends (prefixWord ++ tailWord_570818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570859 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 2, 5]
def baseStart_570859 : Nat := 118140960795 + 570859 * 2 ^ 59
def prefixEnd_570859 : Nat := 4983230072969 + 3 ^ 40 * 570859 * 2
def baseEnd_570859 : Nat := 97708350981695748412391

theorem tailTrace_570859 : CollatzResearch.WordTrace tailWord_570859 prefixEnd_570859 97708350981695748412391 := by
  unfold tailWord_570859
  simp only [CollatzResearch.WordTrace]
  refine ⟨20820938238882812800339631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13880625492588541866893087 20820938238882812800339631)
  ·
    refine ⟨31231407358324219200509447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20820938238882812800339631 31231407358324219200509447)
    ·
      refine ⟨46847111037486328800764171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31231407358324219200509447 46847111037486328800764171)
      ·
        refine ⟨70270666556229493201146257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46847111037486328800764171 70270666556229493201146257)
        ·
          refine ⟨52702999917172119900859693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70270666556229493201146257 52702999917172119900859693)
          ·
            refine ⟨19763624968939544962822385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52702999917172119900859693 19763624968939544962822385)
            ·
              refine ⟨14822718726704658722116789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19763624968939544962822385 14822718726704658722116789)
              ·
                refine ⟨1389629880628561755198449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14822718726704658722116789 1389629880628561755198449)
                ·
                  refine ⟨1042222410471421316398837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389629880628561755198449 1042222410471421316398837)
                  ·
                    refine ⟨97708350981695748412391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1042222410471421316398837 97708350981695748412391)
                    ·
                      rfl

theorem cell23_570859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 5].length) (baseStart_570859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570859 prefixEnd_570859 := by exact prefixLift 570859
  have htrace : WordTrace (prefixWord ++ tailWord_570859) baseStart_570859 baseEnd_570859 := by
    simpa [prefixWord, tailWord_570859, baseEnd_570859] using wordTrace_append hprefix tailTrace_570859
  have hstable : (prefixWord ++ tailWord_570859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570859).length < 2 ^ (prefixWord ++ tailWord_570859).sum := by decide
  have hdescent : baseEnd_570859 < baseStart_570859 := by decide
  rcases family_descends (prefixWord ++ tailWord_570859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570933 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_570933 : Nat := 118140960795 + 570933 * 2 ^ 59
def prefixEnd_570933 : Nat := 4983230072969 + 3 ^ 40 * 570933 * 2
def baseEnd_570933 : Nat := 293163050513519955711833

theorem tailTrace_570933 : CollatzResearch.WordTrace tailWord_570933 prefixEnd_570933 293163050513519955711833 := by
  unfold tailWord_570933
  simp only [CollatzResearch.WordTrace]
  refine ⟨20823637240614723438533453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13882424827076482292355635 20823637240614723438533453)
  ·
    refine ⟨7808863965230521289450045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20823637240614723438533453 7808863965230521289450045)
    ·
      refine ⟨2928323986961445483543767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7808863965230521289450045 2928323986961445483543767)
      ·
        refine ⟨4392485980442168225315651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928323986961445483543767 4392485980442168225315651)
        ·
          refine ⟨6588728970663252337973477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392485980442168225315651 6588728970663252337973477)
          ·
            refine ⟨1235386681999359813370027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6588728970663252337973477 1235386681999359813370027)
            ·
              refine ⟨1853080022999039720055041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235386681999359813370027 1853080022999039720055041)
              ·
                refine ⟨1389810017249279790041281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853080022999039720055041 1389810017249279790041281)
                ·
                  refine ⟨1042357512936959842530961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1389810017249279790041281 1042357512936959842530961)
                  ·
                    refine ⟨781768134702719881898221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1042357512936959842530961 781768134702719881898221)
                    ·
                      refine ⟨293163050513519955711833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781768134702719881898221 293163050513519955711833)
                      ·
                        rfl

theorem cell23_570933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_570933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570933 prefixEnd_570933 := by exact prefixLift 570933
  have htrace : WordTrace (prefixWord ++ tailWord_570933) baseStart_570933 baseEnd_570933 := by
    simpa [prefixWord, tailWord_570933, baseEnd_570933] using wordTrace_append hprefix tailTrace_570933
  have hstable : (prefixWord ++ tailWord_570933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570933).length < 2 ^ (prefixWord ++ tailWord_570933).sum := by decide
  have hdescent : baseEnd_570933 < baseStart_570933 := by decide
  rcases family_descends (prefixWord ++ tailWord_570933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_570940 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_570940 : Nat := 118140960795 + 570940 * 2 ^ 59
def prefixEnd_570940 : Nat := 4983230072969 + 3 ^ 40 * 570940 * 2
def baseEnd_570940 : Nat := 97722214959367142774767

theorem tailTrace_570940 : CollatzResearch.WordTrace tailWord_570940 prefixEnd_570940 97722214959367142774767 := by
  unfold tailWord_570940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10411946275794681817019137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13882595034392909089358849 10411946275794681817019137)
  ·
    refine ⟨7808959706846011362764353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10411946275794681817019137 7808959706846011362764353)
    ·
      refine ⟨5856719780134508522073265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7808959706846011362764353 5856719780134508522073265)
      ·
        refine ⟨4392539835100881391554949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5856719780134508522073265 4392539835100881391554949)
        ·
          refine ⟨823601219081415260916553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4392539835100881391554949 823601219081415260916553)
          ·
            refine ⟨617700914311061445687415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823601219081415260916553 617700914311061445687415)
            ·
              refine ⟨926551371466592168531123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617700914311061445687415 926551371466592168531123)
              ·
                refine ⟨1389827057199888252796685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926551371466592168531123 1389827057199888252796685)
                ·
                  refine ⟨521185146449958094798757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1389827057199888252796685 521185146449958094798757)
                  ·
                    refine ⟨97722214959367142774767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521185146449958094798757 97722214959367142774767)
                    ·
                      rfl

theorem cell23_570940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_570940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_570940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_570940 prefixEnd_570940 := by exact prefixLift 570940
  have htrace : WordTrace (prefixWord ++ tailWord_570940) baseStart_570940 baseEnd_570940 := by
    simpa [prefixWord, tailWord_570940, baseEnd_570940] using wordTrace_append hprefix tailTrace_570940
  have hstable : (prefixWord ++ tailWord_570940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_570940).length < 2 ^ (prefixWord ++ tailWord_570940).sum := by decide
  have hdescent : baseEnd_570940 < baseStart_570940 := by decide
  rcases family_descends (prefixWord ++ tailWord_570940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571013 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_571013 : Nat := 118140960795 + 571013 * 2 ^ 59
def prefixEnd_571013 : Nat := 4983230072969 + 3 ^ 40 * 571013 * 2
def baseEnd_571013 : Nat := 97734709655293214237155

theorem tailTrace_571013 : CollatzResearch.WordTrace tailWord_571013 prefixEnd_571013 97734709655293214237155 := by
  unfold tailWord_571013
  simp only [CollatzResearch.WordTrace]
  refine ⟨20826555080324897101445693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13884370053549931400963795 20826555080324897101445693)
  ·
    refine ⟨7809958155121836413042135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20826555080324897101445693 7809958155121836413042135)
    ·
      refine ⟨11714937232682754619563203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7809958155121836413042135 11714937232682754619563203)
      ·
        refine ⟨17572405849024131929344805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11714937232682754619563203 17572405849024131929344805)
        ·
          refine ⟨3294826096692024736752151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17572405849024131929344805 3294826096692024736752151)
          ·
            refine ⟨4942239145038037105128227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294826096692024736752151 4942239145038037105128227)
            ·
              refine ⟨7413358717557055657692341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942239145038037105128227 7413358717557055657692341)
              ·
                refine ⟨695002379770973967908657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7413358717557055657692341 695002379770973967908657)
                ·
                  refine ⟨521251784828230475931493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695002379770973967908657 521251784828230475931493)
                  ·
                    refine ⟨97734709655293214237155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521251784828230475931493 97734709655293214237155)
                    ·
                      rfl

theorem cell23_571013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_571013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571013 prefixEnd_571013 := by exact prefixLift 571013
  have htrace : WordTrace (prefixWord ++ tailWord_571013) baseStart_571013 baseEnd_571013 := by
    simpa [prefixWord, tailWord_571013, baseEnd_571013] using wordTrace_append hprefix tailTrace_571013
  have hstable : (prefixWord ++ tailWord_571013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571013).length < 2 ^ (prefixWord ++ tailWord_571013).sum := by decide
  have hdescent : baseEnd_571013 < baseStart_571013 := by decide
  rcases family_descends (prefixWord ++ tailWord_571013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571020 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_571020 : Nat := 118140960795 + 571020 * 2 ^ 59
def prefixEnd_571020 : Nat := 4983230072969 + 3 ^ 40 * 571020 * 2
def baseEnd_571020 : Nat := 293207723330461115323933

theorem tailTrace_571020 : CollatzResearch.WordTrace tailWord_571020 prefixEnd_571020 293207723330461115323933 := by
  unfold tailWord_571020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413405195649768648475257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13884540260866358197967009 10413405195649768648475257)
  ·
    refine ⟨7810053896737326486356443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10413405195649768648475257 7810053896737326486356443)
    ·
      refine ⟨11715080845105989729534665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810053896737326486356443 11715080845105989729534665)
      ·
        refine ⟨8786310633829492297150999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11715080845105989729534665 8786310633829492297150999)
        ·
          refine ⟨13179465950744238445726499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8786310633829492297150999 13179465950744238445726499)
          ·
            refine ⟨19769198926116357668589749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13179465950744238445726499 19769198926116357668589749)
            ·
              refine ⟨1853362399323408531430289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19769198926116357668589749 1853362399323408531430289)
              ·
                refine ⟨1390021799492556398572717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853362399323408531430289 1390021799492556398572717)
                ·
                  refine ⟨521258174809708649464769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1390021799492556398572717 521258174809708649464769)
                  ·
                    refine ⟨390943631107281487098577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 521258174809708649464769 390943631107281487098577)
                    ·
                      refine ⟨293207723330461115323933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 390943631107281487098577 293207723330461115323933)
                      ·
                        rfl

theorem cell23_571020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_571020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571020 prefixEnd_571020 := by exact prefixLift 571020
  have htrace : WordTrace (prefixWord ++ tailWord_571020) baseStart_571020 baseEnd_571020 := by
    simpa [prefixWord, tailWord_571020, baseEnd_571020] using wordTrace_append hprefix tailTrace_571020
  have hstable : (prefixWord ++ tailWord_571020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571020).length < 2 ^ (prefixWord ++ tailWord_571020).sum := by decide
  have hdescent : baseEnd_571020 < baseStart_571020 := by decide
  rcases family_descends (prefixWord ++ tailWord_571020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571040 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_571040 : Nat := 118140960795 + 571040 * 2 ^ 59
def prefixEnd_571040 : Nat := 4983230072969 + 3 ^ 40 * 571040 * 2
def baseEnd_571040 : Nat := 293217992943551037073841

theorem tailTrace_571040 : CollatzResearch.WordTrace tailWord_571040 prefixEnd_571040 293217992943551037073841 := by
  unfold tailWord_571040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10413769925613540356339287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13885026567484720475119049 10413769925613540356339287)
  ·
    refine ⟨15620654888420310534508931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10413769925613540356339287 15620654888420310534508931)
    ·
      refine ⟨23430982332630465801763397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15620654888420310534508931 23430982332630465801763397)
      ·
        refine ⟨4393309187368212337830637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23430982332630465801763397 4393309187368212337830637)
        ·
          refine ⟨1647490945263079626686489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4393309187368212337830637 1647490945263079626686489)
          ·
            refine ⟨1235618208947309720014867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647490945263079626686489 1235618208947309720014867)
            ·
              refine ⟨1853427313420964580022301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235618208947309720014867 1853427313420964580022301)
              ·
                refine ⟨695035242532861717508363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1853427313420964580022301 695035242532861717508363)
                ·
                  refine ⟨1042552863799292576262545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695035242532861717508363 1042552863799292576262545)
                  ·
                    refine ⟨781914647849469432196909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1042552863799292576262545 781914647849469432196909)
                    ·
                      refine ⟨293217992943551037073841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781914647849469432196909 293217992943551037073841)
                      ·
                        rfl

theorem cell23_571040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_571040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571040 prefixEnd_571040 := by exact prefixLift 571040
  have htrace : WordTrace (prefixWord ++ tailWord_571040) baseStart_571040 baseEnd_571040 := by
    simpa [prefixWord, tailWord_571040, baseEnd_571040] using wordTrace_append hprefix tailTrace_571040
  have hstable : (prefixWord ++ tailWord_571040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571040).length < 2 ^ (prefixWord ++ tailWord_571040).sum := by decide
  have hdescent : baseEnd_571040 < baseStart_571040 := by decide
  rcases family_descends (prefixWord ++ tailWord_571040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571070 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_571070 : Nat := 118140960795 + 571070 * 2 ^ 59
def prefixEnd_571070 : Nat := 4983230072969 + 3 ^ 40 * 571070 * 2
def baseEnd_571070 : Nat := 293233397363185919698703

theorem tailTrace_571070 : CollatzResearch.WordTrace tailWord_571070 prefixEnd_571070 293233397363185919698703 := by
  unfold tailWord_571070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603579255139799479533833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13885756027412263890847109 2603579255139799479533833)
  ·
    refine ⟨1952684441354849609650375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2603579255139799479533833 1952684441354849609650375)
    ·
      refine ⟨2929026662032274414475563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952684441354849609650375 2929026662032274414475563)
      ·
        refine ⟨4393539993048411621713345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929026662032274414475563 4393539993048411621713345)
        ·
          refine ⟨3295154994786308716285009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4393539993048411621713345 3295154994786308716285009)
          ·
            refine ⟨2471366246089731537213757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295154994786308716285009 2471366246089731537213757)
            ·
              refine ⟨926762342283649326455159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2471366246089731537213757 926762342283649326455159)
              ·
                refine ⟨1390143513425473989682739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926762342283649326455159 1390143513425473989682739)
                ·
                  refine ⟨2085215270138210984524109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390143513425473989682739 2085215270138210984524109)
                  ·
                    refine ⟨781955726301829119196541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085215270138210984524109 781955726301829119196541)
                    ·
                      refine ⟨293233397363185919698703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 781955726301829119196541 293233397363185919698703)
                      ·
                        rfl

theorem cell23_571070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_571070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571070 prefixEnd_571070 := by exact prefixLift 571070
  have htrace : WordTrace (prefixWord ++ tailWord_571070) baseStart_571070 baseEnd_571070 := by
    simpa [prefixWord, tailWord_571070, baseEnd_571070] using wordTrace_append hprefix tailTrace_571070
  have hstable : (prefixWord ++ tailWord_571070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571070).length < 2 ^ (prefixWord ++ tailWord_571070).sum := by decide
  have hdescent : baseEnd_571070 < baseStart_571070 := by decide
  rcases family_descends (prefixWord ++ tailWord_571070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571170 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_571170 : Nat := 118140960795 + 571170 * 2 ^ 59
def prefixEnd_571170 : Nat := 4983230072969 + 3 ^ 40 * 571170 * 2
def baseEnd_571170 : Nat := 293284745428635528448243

theorem tailTrace_571170 : CollatzResearch.WordTrace tailWord_571170 prefixEnd_571170 293284745428635528448243 := by
  unfold tailWord_571170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208070335189028228727741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13888187560504075276607309 5208070335189028228727741)
  ·
    refine ⟨1953026375695885585772903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5208070335189028228727741 1953026375695885585772903)
    ·
      refine ⟨2929539563543828378659355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1953026375695885585772903 2929539563543828378659355)
      ·
        refine ⟨4394309345315742567989033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929539563543828378659355 4394309345315742567989033)
        ·
          refine ⟨3295732008986806925991775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4394309345315742567989033 3295732008986806925991775)
          ·
            refine ⟨4943598013480210388987663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295732008986806925991775 4943598013480210388987663)
            ·
              refine ⟨7415397020220315583481495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943598013480210388987663 7415397020220315583481495)
              ·
                refine ⟨11123095530330473375222243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7415397020220315583481495 11123095530330473375222243)
                ·
                  refine ⟨16684643295495710062833365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11123095530330473375222243 16684643295495710062833365)
                  ·
                    refine ⟨391046327238180704597657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16684643295495710062833365 391046327238180704597657)
                    ·
                      refine ⟨293284745428635528448243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391046327238180704597657 293284745428635528448243)
                      ·
                        rfl

theorem cell23_571170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_571170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571170 prefixEnd_571170 := by exact prefixLift 571170
  have htrace : WordTrace (prefixWord ++ tailWord_571170) baseStart_571170 baseEnd_571170 := by
    simpa [prefixWord, tailWord_571170, baseEnd_571170] using wordTrace_append hprefix tailTrace_571170
  have hstable : (prefixWord ++ tailWord_571170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571170).length < 2 ^ (prefixWord ++ tailWord_571170).sum := by decide
  have hdescent : baseEnd_571170 < baseStart_571170 := by decide
  rcases family_descends (prefixWord ++ tailWord_571170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571173 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_571173 : Nat := 118140960795 + 571173 * 2 ^ 59
def prefixEnd_571173 : Nat := 4983230072969 + 3 ^ 40 * 571173 * 2
def baseEnd_571173 : Nat := 293286285870599016710729

theorem tailTrace_571173 : CollatzResearch.WordTrace tailWord_571173 prefixEnd_571173 293286285870599016710729 := by
  unfold tailWord_571173
  simp only [CollatzResearch.WordTrace]
  refine ⟨20832390759745244427270173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13888260506496829618180115 20832390759745244427270173)
  ·
    refine ⟨7812146534904466660226315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20832390759745244427270173 7812146534904466660226315)
    ·
      refine ⟨11718219802356699990339473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7812146534904466660226315 11718219802356699990339473)
      ·
        refine ⟨8788664851767524992754605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11718219802356699990339473 8788664851767524992754605)
        ·
          refine ⟨3295749319412821872282977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8788664851767524992754605 3295749319412821872282977)
          ·
            refine ⟨2471811989559616404212233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295749319412821872282977 2471811989559616404212233)
            ·
              refine ⟨1853858992169712303159175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471811989559616404212233 1853858992169712303159175)
              ·
                refine ⟨2780788488254568454738763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853858992169712303159175 2780788488254568454738763)
                ·
                  refine ⟨4171182732381852682108145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780788488254568454738763 4171182732381852682108145)
                  ·
                    refine ⟨3128387049286389511581109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171182732381852682108145 3128387049286389511581109)
                    ·
                      refine ⟨293286285870599016710729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3128387049286389511581109 293286285870599016710729)
                      ·
                        rfl

theorem cell23_571173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_571173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571173 prefixEnd_571173 := by exact prefixLift 571173
  have htrace : WordTrace (prefixWord ++ tailWord_571173) baseStart_571173 baseEnd_571173 := by
    simpa [prefixWord, tailWord_571173, baseEnd_571173] using wordTrace_append hprefix tailTrace_571173
  have hstable : (prefixWord ++ tailWord_571173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571173).length < 2 ^ (prefixWord ++ tailWord_571173).sum := by decide
  have hdescent : baseEnd_571173 < baseStart_571173 := by decide
  rcases family_descends (prefixWord ++ tailWord_571173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571197 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_571197 : Nat := 118140960795 + 571197 * 2 ^ 59
def prefixEnd_571197 : Nat := 4983230072969 + 3 ^ 40 * 571197 * 2
def baseEnd_571197 : Nat := 97766203135435640936873

theorem tailTrace_571197 : CollatzResearch.WordTrace tailWord_571197 prefixEnd_571197 97766203135435640936873 := by
  unfold tailWord_571197
  simp only [CollatzResearch.WordTrace]
  refine ⟨20833266111658296526143845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13888844074438864350762563 20833266111658296526143845)
  ·
    refine ⟨3906237395935930598651971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20833266111658296526143845 3906237395935930598651971)
    ·
      refine ⟨5859356093903895897977957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3906237395935930598651971 5859356093903895897977957)
      ·
        refine ⟨1098629267606980480870867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5859356093903895897977957 1098629267606980480870867)
        ·
          refine ⟨1647943901410470721306301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098629267606980480870867 1647943901410470721306301)
          ·
            refine ⟨617978963028926520489863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1647943901410470721306301 617978963028926520489863)
            ·
              refine ⟨926968444543389780734795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617978963028926520489863 926968444543389780734795)
              ·
                refine ⟨1390452666815084671102193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926968444543389780734795 1390452666815084671102193)
                ·
                  refine ⟨1042839500111313503326645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1390452666815084671102193 1042839500111313503326645)
                  ·
                    refine ⟨97766203135435640936873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1042839500111313503326645 97766203135435640936873)
                    ·
                      rfl

theorem cell23_571197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_571197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571197 prefixEnd_571197 := by exact prefixLift 571197
  have htrace : WordTrace (prefixWord ++ tailWord_571197) baseStart_571197 baseEnd_571197 := by
    simpa [prefixWord, tailWord_571197, baseEnd_571197] using wordTrace_append hprefix tailTrace_571197
  have hstable : (prefixWord ++ tailWord_571197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571197).length < 2 ^ (prefixWord ++ tailWord_571197).sum := by decide
  have hdescent : baseEnd_571197 < baseStart_571197 := by decide
  rcases family_descends (prefixWord ++ tailWord_571197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571278 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_571278 : Nat := 118140960795 + 571278 * 2 ^ 59
def prefixEnd_571278 : Nat := 4983230072969 + 3 ^ 40 * 571278 * 2
def baseEnd_571278 : Nat := 97780067113107035299249

theorem tailTrace_571278 : CollatzResearch.WordTrace tailWord_571278 prefixEnd_571278 97780067113107035299249 := by
  unfold tailWord_571278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604527553045605919980311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13890813616243231573228325 2604527553045605919980311)
  ·
    refine ⟨3906791329568408879970467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2604527553045605919980311 3906791329568408879970467)
    ·
      refine ⟨5860186994352613319955701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3906791329568408879970467 5860186994352613319955701)
      ·
        refine ⟨549392530720557498745847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5860186994352613319955701 549392530720557498745847)
        ·
          refine ⟨824088796080836248118771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549392530720557498745847 824088796080836248118771)
          ·
            refine ⟨1236133194121254372178157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824088796080836248118771 1236133194121254372178157)
            ·
              refine ⟨463549947795470389566809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236133194121254372178157 463549947795470389566809)
              ·
                refine ⟨347662460846602792175107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463549947795470389566809 347662460846602792175107)
                ·
                  refine ⟨521493691269904188262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347662460846602792175107 521493691269904188262661)
                  ·
                    refine ⟨97780067113107035299249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521493691269904188262661 97780067113107035299249)
                    ·
                      rfl

theorem cell23_571278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_571278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571278 prefixEnd_571278 := by exact prefixLift 571278
  have htrace : WordTrace (prefixWord ++ tailWord_571278) baseStart_571278 baseEnd_571278 := by
    simpa [prefixWord, tailWord_571278, baseEnd_571278] using wordTrace_append hprefix tailTrace_571278
  have hstable : (prefixWord ++ tailWord_571278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571278).length < 2 ^ (prefixWord ++ tailWord_571278).sum := by decide
  have hdescent : baseEnd_571278 < baseStart_571278 := by decide
  rcases family_descends (prefixWord ++ tailWord_571278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571284 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_571284 : Nat := 118140960795 + 571284 * 2 ^ 59
def prefixEnd_571284 : Nat := 4983230072969 + 3 ^ 40 * 571284 * 2
def baseEnd_571284 : Nat := 293343282223248082422719

theorem tailTrace_571284 : CollatzResearch.WordTrace tailWord_571284 prefixEnd_571284 293343282223248082422719 := by
  unfold tailWord_571284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418219631171555192280453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13890959508228740256373937 10418219631171555192280453)
  ·
    refine ⟨1953416180844666598552585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10418219631171555192280453 1953416180844666598552585)
    ·
      refine ⟨1465062135633499948914439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1953416180844666598552585 1465062135633499948914439)
      ·
        refine ⟨2197593203450249923371659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465062135633499948914439 2197593203450249923371659)
        ·
          refine ⟨3296389805175374885057489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197593203450249923371659 3296389805175374885057489)
          ·
            refine ⟨2472292353881531163793117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3296389805175374885057489 2472292353881531163793117)
            ·
              refine ⟨927109632705574186422419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2472292353881531163793117 927109632705574186422419)
              ·
                refine ⟨1390664449058361279633629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927109632705574186422419 1390664449058361279633629)
                ·
                  refine ⟨521499168396885479862611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1390664449058361279633629 521499168396885479862611)
                  ·
                    refine ⟨782248752595328219793917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 521499168396885479862611 782248752595328219793917)
                    ·
                      refine ⟨293343282223248082422719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 782248752595328219793917 293343282223248082422719)
                      ·
                        rfl

theorem cell23_571284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_571284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571284 prefixEnd_571284 := by exact prefixLift 571284
  have htrace : WordTrace (prefixWord ++ tailWord_571284) baseStart_571284 baseEnd_571284 := by
    simpa [prefixWord, tailWord_571284, baseEnd_571284] using wordTrace_append hprefix tailTrace_571284
  have hstable : (prefixWord ++ tailWord_571284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571284).length < 2 ^ (prefixWord ++ tailWord_571284).sum := by decide
  have hdescent : baseEnd_571284 < baseStart_571284 := by decide
  rcases family_descends (prefixWord ++ tailWord_571284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571304 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_571304 : Nat := 118140960795 + 571304 * 2 ^ 59
def prefixEnd_571304 : Nat := 4983230072969 + 3 ^ 40 * 571304 * 2
def baseEnd_571304 : Nat := 97784517278779334724209

theorem tailTrace_571304 : CollatzResearch.WordTrace tailWord_571304 prefixEnd_571304 97784517278779334724209 := by
  unfold tailWord_571304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418584361135326900144483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13891445814847102533525977 10418584361135326900144483)
  ·
    refine ⟨15627876541702990350216725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10418584361135326900144483 15627876541702990350216725)
    ·
      refine ⟨732556712892327672666409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15627876541702990350216725 732556712892327672666409)
      ·
        refine ⟨549417534669245754499807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732556712892327672666409 549417534669245754499807)
        ·
          refine ⟨824126302003868631749711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549417534669245754499807 824126302003868631749711)
          ·
            refine ⟨1236189453005802947624567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824126302003868631749711 1236189453005802947624567)
            ·
              refine ⟨1854284179508704421436851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236189453005802947624567 1854284179508704421436851)
              ·
                refine ⟨2781426269263056632155277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854284179508704421436851 2781426269263056632155277)
                ·
                  refine ⟨1043034850973646237058229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2781426269263056632155277 1043034850973646237058229)
                  ·
                    refine ⟨97784517278779334724209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1043034850973646237058229 97784517278779334724209)
                    ·
                      rfl

theorem cell23_571304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_571304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571304 prefixEnd_571304 := by exact prefixLift 571304
  have htrace : WordTrace (prefixWord ++ tailWord_571304) baseStart_571304 baseEnd_571304 := by
    simpa [prefixWord, tailWord_571304, baseEnd_571304] using wordTrace_append hprefix tailTrace_571304
  have hstable : (prefixWord ++ tailWord_571304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571304).length < 2 ^ (prefixWord ++ tailWord_571304).sum := by decide
  have hdescent : baseEnd_571304 < baseStart_571304 := by decide
  rcases family_descends (prefixWord ++ tailWord_571304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571320 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_571320 : Nat := 118140960795 + 571320 * 2 ^ 59
def prefixEnd_571320 : Nat := 4983230072969 + 3 ^ 40 * 571320 * 2
def baseEnd_571320 : Nat := 293361767526809941572553

theorem tailTrace_571320 : CollatzResearch.WordTrace tailWord_571320 prefixEnd_571320 293361767526809941572553 := by
  unfold tailWord_571320
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418876145106344266435707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13891834860141792355247609 10418876145106344266435707)
  ·
    refine ⟨15628314217659516399653561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10418876145106344266435707 15628314217659516399653561)
    ·
      refine ⟨11721235663244637299740171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15628314217659516399653561 11721235663244637299740171)
      ·
        refine ⟨17581853494866955949610257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11721235663244637299740171 17581853494866955949610257)
        ·
          refine ⟨13186390121150216962207693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17581853494866955949610257 13186390121150216962207693)
          ·
            refine ⟨4944896295431331360827885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13186390121150216962207693 4944896295431331360827885)
            ·
              refine ⟨1854336110786749260310457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4944896295431331360827885 1854336110786749260310457)
              ·
                refine ⟨1390752083090061945232843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854336110786749260310457 1390752083090061945232843)
                ·
                  refine ⟨2086128124635092917849265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390752083090061945232843 2086128124635092917849265)
                  ·
                    refine ⟨1564596093476319688386949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2086128124635092917849265 1564596093476319688386949)
                    ·
                      refine ⟨293361767526809941572553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1564596093476319688386949 293361767526809941572553)
                      ·
                        rfl

theorem cell23_571320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_571320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571320 prefixEnd_571320 := by exact prefixLift 571320
  have htrace : WordTrace (prefixWord ++ tailWord_571320) baseStart_571320 baseEnd_571320 := by
    simpa [prefixWord, tailWord_571320, baseEnd_571320] using wordTrace_append hprefix tailTrace_571320
  have hstable : (prefixWord ++ tailWord_571320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571320).length < 2 ^ (prefixWord ++ tailWord_571320).sum := by decide
  have hdescent : baseEnd_571320 < baseStart_571320 := by decide
  rcases family_descends (prefixWord ++ tailWord_571320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_571333 : Nat := 118140960795 + 571333 * 2 ^ 59
def prefixEnd_571333 : Nat := 4983230072969 + 3 ^ 40 * 571333 * 2
def baseEnd_571333 : Nat := 293368442775318390709993

theorem tailTrace_571333 : CollatzResearch.WordTrace tailWord_571333 prefixEnd_571333 293368442775318390709993 := by
  unfold tailWord_571333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20838226439165591753094653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13892150959443727835396435 20838226439165591753094653)
  ·
    refine ⟨7814334914687096907410495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20838226439165591753094653 7814334914687096907410495)
    ·
      refine ⟨11721502372030645361115743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7814334914687096907410495 11721502372030645361115743)
      ·
        refine ⟨17582253558045968041673615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11721502372030645361115743 17582253558045968041673615)
        ·
          refine ⟨26373380337068952062510423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17582253558045968041673615 26373380337068952062510423)
          ·
            refine ⟨39560070505603428093765635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26373380337068952062510423 39560070505603428093765635)
            ·
              refine ⟨59340105758405142140648453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39560070505603428093765635 59340105758405142140648453)
              ·
                refine ⟨11126269829700964151371585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59340105758405142140648453 11126269829700964151371585)
                ·
                  refine ⟨8344702372275723113528689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11126269829700964151371585 8344702372275723113528689)
                  ·
                    refine ⟨6258526779206792335146517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8344702372275723113528689 6258526779206792335146517)
                    ·
                      refine ⟨293368442775318390709993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6258526779206792335146517 293368442775318390709993)
                      ·
                        rfl

theorem cell23_571333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_571333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571333 prefixEnd_571333 := by exact prefixLift 571333
  have htrace : WordTrace (prefixWord ++ tailWord_571333) baseStart_571333 baseEnd_571333 := by
    simpa [prefixWord, tailWord_571333, baseEnd_571333] using wordTrace_append hprefix tailTrace_571333
  have hstable : (prefixWord ++ tailWord_571333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571333).length < 2 ^ (prefixWord ++ tailWord_571333).sum := by decide
  have hdescent : baseEnd_571333 < baseStart_571333 := by decide
  rcases family_descends (prefixWord ++ tailWord_571333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571343 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 9]
def baseStart_571343 : Nat := 118140960795 + 571343 * 2 ^ 59
def prefixEnd_571343 : Nat := 4983230072969 + 3 ^ 40 * 571343 * 2
def baseEnd_571343 : Nat := 97791192527287783861649

theorem tailTrace_571343 : CollatzResearch.WordTrace tailWord_571343 prefixEnd_571343 97791192527287783861649 := by
  unfold tailWord_571343
  simp only [CollatzResearch.WordTrace]
  refine ⟨20838591169129363460958683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13892394112752908973972455 20838591169129363460958683)
  ·
    refine ⟨31257886753694045191438025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20838591169129363460958683 31257886753694045191438025)
    ·
      refine ⟨23443415065270533893578519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31257886753694045191438025 23443415065270533893578519)
      ·
        refine ⟨35165122597905800840367779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23443415065270533893578519 35165122597905800840367779)
        ·
          refine ⟨52747683896858701260551669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35165122597905800840367779 52747683896858701260551669)
          ·
            refine ⟨4945095365330503243176719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52747683896858701260551669 4945095365330503243176719)
            ·
              refine ⟨7417643047995754864765079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4945095365330503243176719 7417643047995754864765079)
              ·
                refine ⟨11126464571993632297147619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417643047995754864765079 11126464571993632297147619)
                ·
                  refine ⟨16689696857990448445721429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11126464571993632297147619 16689696857990448445721429)
                  ·
                    refine ⟨97791192527287783861649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16689696857990448445721429 97791192527287783861649)
                    ·
                      rfl

theorem cell23_571343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_571343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571343 prefixEnd_571343 := by exact prefixLift 571343
  have htrace : WordTrace (prefixWord ++ tailWord_571343) baseStart_571343 baseEnd_571343 := by
    simpa [prefixWord, tailWord_571343, baseEnd_571343] using wordTrace_append hprefix tailTrace_571343
  have hstable : (prefixWord ++ tailWord_571343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571343).length < 2 ^ (prefixWord ++ tailWord_571343).sum := by decide
  have hdescent : baseEnd_571343 < baseStart_571343 := by decide
  rcases family_descends (prefixWord ++ tailWord_571343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571370 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_571370 : Nat := 118140960795 + 571370 * 2 ^ 59
def prefixEnd_571370 : Nat := 4983230072969 + 3 ^ 40 * 571370 * 2
def baseEnd_571370 : Nat := 293387441559534745947323

theorem tailTrace_571370 : CollatzResearch.WordTrace tailWord_571370 prefixEnd_571370 293387441559534745947323 := by
  unfold tailWord_571370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5209893985007886768047891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13893050626687698048127709 5209893985007886768047891)
  ·
    refine ⟨7814840977511830152071837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5209893985007886768047891 7814840977511830152071837)
    ·
      refine ⟨2930565366566936307026939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7814840977511830152071837 2930565366566936307026939)
      ·
        refine ⟨4395848049850404460540409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930565366566936307026939 4395848049850404460540409)
        ·
          refine ⟨3296886037387803345405307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4395848049850404460540409 3296886037387803345405307)
          ·
            refine ⟨4945329056081705018107961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296886037387803345405307 4945329056081705018107961)
            ·
              refine ⟨3708996792061278763580971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4945329056081705018107961 3708996792061278763580971)
              ·
                refine ⟨5563495188091918145371457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708996792061278763580971 5563495188091918145371457)
                ·
                  refine ⟨4172621391068938609028593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5563495188091918145371457 4172621391068938609028593)
                  ·
                    refine ⟨3129466043301703956771445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4172621391068938609028593 3129466043301703956771445)
                    ·
                      refine ⟨293387441559534745947323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3129466043301703956771445 293387441559534745947323)
                      ·
                        rfl

theorem cell23_571370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_571370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571370 prefixEnd_571370 := by exact prefixLift 571370
  have htrace : WordTrace (prefixWord ++ tailWord_571370) baseStart_571370 baseEnd_571370 := by
    simpa [prefixWord, tailWord_571370, baseEnd_571370] using wordTrace_append hprefix tailTrace_571370
  have hstable : (prefixWord ++ tailWord_571370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571370).length < 2 ^ (prefixWord ++ tailWord_571370).sum := by decide
  have hdescent : baseEnd_571370 < baseStart_571370 := by decide
  rcases family_descends (prefixWord ++ tailWord_571370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571405 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_571405 : Nat := 118140960795 + 571405 * 2 ^ 59
def prefixEnd_571405 : Nat := 4983230072969 + 3 ^ 40 * 571405 * 2
def baseEnd_571405 : Nat := 293405413382442109009663

theorem tailTrace_571405 : CollatzResearch.WordTrace tailWord_571405 prefixEnd_571405 293405413382442109009663 := by
  unfold tailWord_571405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20840852494904748049715669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13893901663269832033143779 20840852494904748049715669)
  ·
    refine ⟨488457480349330032415211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20840852494904748049715669 488457480349330032415211)
    ·
      refine ⟨732686220523995048622817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 488457480349330032415211 732686220523995048622817)
      ·
        refine ⟨549514665392996286467113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732686220523995048622817 549514665392996286467113)
        ·
          refine ⟨412135999044747214850335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549514665392996286467113 412135999044747214850335)
          ·
            refine ⟨618203998567120822275503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412135999044747214850335 618203998567120822275503)
            ·
              refine ⟨927305997850681233413255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618203998567120822275503 927305997850681233413255)
              ·
                refine ⟨1390958996776021850119883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927305997850681233413255 1390958996776021850119883)
                ·
                  refine ⟨2086438495164032775179825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390958996776021850119883 2086438495164032775179825)
                  ·
                    refine ⟨1564828871373024581384869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2086438495164032775179825 1564828871373024581384869)
                    ·
                      refine ⟨293405413382442109009663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1564828871373024581384869 293405413382442109009663)
                      ·
                        rfl

theorem cell23_571405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_571405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571405 prefixEnd_571405 := by exact prefixLift 571405
  have htrace : WordTrace (prefixWord ++ tailWord_571405) baseStart_571405 baseEnd_571405 := by
    simpa [prefixWord, tailWord_571405, baseEnd_571405] using wordTrace_append hprefix tailTrace_571405
  have hstable : (prefixWord ++ tailWord_571405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571405).length < 2 ^ (prefixWord ++ tailWord_571405).sum := by decide
  have hdescent : baseEnd_571405 < baseStart_571405 := by decide
  rcases family_descends (prefixWord ++ tailWord_571405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571484 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_571484 : Nat := 118140960795 + 571484 * 2 ^ 59
def prefixEnd_571484 : Nat := 4983230072969 + 3 ^ 40 * 571484 * 2
def baseEnd_571484 : Nat := 97815326118049099973933

theorem tailTrace_571484 : CollatzResearch.WordTrace tailWord_571484 prefixEnd_571484 97815326118049099973933 := by
  unfold tailWord_571484
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421866930809272270920753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13895822574412363027894337 10421866930809272270920753)
  ·
    refine ⟨7816400198106954203190565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10421866930809272270920753 7816400198106954203190565)
    ·
      refine ⟨1465575037145053913098231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7816400198106954203190565 1465575037145053913098231)
      ·
        refine ⟨2198362555717580869647347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465575037145053913098231 2198362555717580869647347)
        ·
          refine ⟨3297543833576371304471021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198362555717580869647347 3297543833576371304471021)
          ·
            refine ⟨1236578937591139239176633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3297543833576371304471021 1236578937591139239176633)
            ·
              refine ⟨927434203193354429382475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236578937591139239176633 927434203193354429382475)
              ·
                refine ⟨1391151304790031644073713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927434203193354429382475 1391151304790031644073713)
                ·
                  refine ⟨1043363478592523733055285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1391151304790031644073713 1043363478592523733055285)
                  ·
                    refine ⟨97815326118049099973933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1043363478592523733055285 97815326118049099973933)
                    ·
                      rfl

theorem cell23_571484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_571484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571484 prefixEnd_571484 := by exact prefixLift 571484
  have htrace : WordTrace (prefixWord ++ tailWord_571484) baseStart_571484 baseEnd_571484 := by
    simpa [prefixWord, tailWord_571484, baseEnd_571484] using wordTrace_append hprefix tailTrace_571484
  have hstable : (prefixWord ++ tailWord_571484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571484).length < 2 ^ (prefixWord ++ tailWord_571484).sum := by decide
  have hdescent : baseEnd_571484 < baseStart_571484 := by decide
  rcases family_descends (prefixWord ++ tailWord_571484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571487 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 6, 2]
def baseStart_571487 : Nat := 118140960795 + 571487 * 2 ^ 59
def prefixEnd_571487 : Nat := 4983230072969 + 3 ^ 40 * 571487 * 2
def baseEnd_571487 : Nat := 293447518796110788184285

theorem tailTrace_571487 : CollatzResearch.WordTrace tailWord_571487 prefixEnd_571487 293447518796110788184285 := by
  unfold tailWord_571487
  simp only [CollatzResearch.WordTrace]
  refine ⟨20843843280607676054200715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13895895520405117369467143 20843843280607676054200715)
  ·
    refine ⟨31265764920911514081301073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20843843280607676054200715 31265764920911514081301073)
    ·
      refine ⟨23449323690683635560975805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31265764920911514081301073 23449323690683635560975805)
      ·
        refine ⟨8793496384006363335365927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23449323690683635560975805 8793496384006363335365927)
        ·
          refine ⟨13190244576009545003048891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8793496384006363335365927 13190244576009545003048891)
          ·
            refine ⟨19785366864014317504573337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13190244576009545003048891 19785366864014317504573337)
            ·
              refine ⟨14839025148010738128430003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19785366864014317504573337 14839025148010738128430003)
              ·
                refine ⟨22258537722016107192645005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14839025148010738128430003 22258537722016107192645005)
                ·
                  refine ⟨8346951645756040197241877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22258537722016107192645005 8346951645756040197241877)
                  ·
                    refine ⟨391263358394814384245713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8346951645756040197241877 391263358394814384245713)
                    ·
                      refine ⟨293447518796110788184285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391263358394814384245713 293447518796110788184285)
                      ·
                        rfl

theorem cell23_571487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_571487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571487 prefixEnd_571487 := by exact prefixLift 571487
  have htrace : WordTrace (prefixWord ++ tailWord_571487) baseStart_571487 baseEnd_571487 := by
    simpa [prefixWord, tailWord_571487, baseEnd_571487] using wordTrace_append hprefix tailTrace_571487
  have hstable : (prefixWord ++ tailWord_571487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571487).length < 2 ^ (prefixWord ++ tailWord_571487).sum := by decide
  have hdescent : baseEnd_571487 < baseStart_571487 := by decide
  rcases family_descends (prefixWord ++ tailWord_571487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571521 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_571521 : Nat := 118140960795 + 571521 * 2 ^ 59
def prefixEnd_571521 : Nat := 4983230072969 + 3 ^ 40 * 571521 * 2
def baseEnd_571521 : Nat := 293464977138363655159129

theorem tailTrace_571521 : CollatzResearch.WordTrace tailWord_571521 prefixEnd_571521 293464977138363655159129 := by
  unfold tailWord_571521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20845083362484499860938417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13896722241656333240625611 20845083362484499860938417)
  ·
    refine ⟨15633812521863374895703813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20845083362484499860938417 15633812521863374895703813)
    ·
      refine ⟨2931339847849382792944465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15633812521863374895703813 2931339847849382792944465)
      ·
        refine ⟨2198504885887037094708349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2931339847849382792944465 2198504885887037094708349)
        ·
          refine ⟨824439332207638910515631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2198504885887037094708349 824439332207638910515631)
          ·
            refine ⟨1236658998311458365773447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824439332207638910515631 1236658998311458365773447)
            ·
              refine ⟨1854988497467187548660171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236658998311458365773447 1854988497467187548660171)
              ·
                refine ⟨2782482746200781322990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854988497467187548660171 2782482746200781322990257)
                ·
                  refine ⟨2086862059650585992242693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2782482746200781322990257 2086862059650585992242693)
                  ·
                    refine ⟨391286636184484873545505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2086862059650585992242693 391286636184484873545505)
                    ·
                      refine ⟨293464977138363655159129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391286636184484873545505 293464977138363655159129)
                      ·
                        rfl

theorem cell23_571521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_571521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571521 prefixEnd_571521 := by exact prefixLift 571521
  have htrace : WordTrace (prefixWord ++ tailWord_571521) baseStart_571521 baseEnd_571521 := by
    simpa [prefixWord, tailWord_571521, baseEnd_571521] using wordTrace_append hprefix tailTrace_571521
  have hstable : (prefixWord ++ tailWord_571521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571521).length < 2 ^ (prefixWord ++ tailWord_571521).sum := by decide
  have hdescent : baseEnd_571521 < baseStart_571521 := by decide
  rcases family_descends (prefixWord ++ tailWord_571521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571527 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 6]
def baseStart_571527 : Nat := 118140960795 + 571527 * 2 ^ 59
def prefixEnd_571527 : Nat := 4983230072969 + 3 ^ 40 * 571527 * 2
def baseEnd_571527 : Nat := 32607562002476736853789

theorem tailTrace_571527 : CollatzResearch.WordTrace tailWord_571527 prefixEnd_571527 32607562002476736853789 := by
  unfold tailWord_571527
  simp only [CollatzResearch.WordTrace]
  refine ⟨20845302200462762885656835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13896868133641841923771223 20845302200462762885656835)
  ·
    refine ⟨31267953300694144328485253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20845302200462762885656835 31267953300694144328485253)
    ·
      refine ⟨5862741243880152061590985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31267953300694144328485253 5862741243880152061590985)
      ·
        refine ⟨4397055932910114046193239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5862741243880152061590985 4397055932910114046193239)
        ·
          refine ⟨6595583899365171069289859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397055932910114046193239 6595583899365171069289859)
          ·
            refine ⟨9893375849047756603934789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595583899365171069289859 9893375849047756603934789)
            ·
              refine ⟨1855007971696454363237773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9893375849047756603934789 1855007971696454363237773)
              ·
                refine ⟨695627989386170386214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1855007971696454363237773 695627989386170386214165)
                ·
                  refine ⟨32607562002476736853789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 695627989386170386214165 32607562002476736853789)
                  ·
                    rfl

theorem cell23_571527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 6].length) (baseStart_571527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571527 prefixEnd_571527 := by exact prefixLift 571527
  have htrace : WordTrace (prefixWord ++ tailWord_571527) baseStart_571527 baseEnd_571527 := by
    simpa [prefixWord, tailWord_571527, baseEnd_571527] using wordTrace_append hprefix tailTrace_571527
  have hstable : (prefixWord ++ tailWord_571527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571527).length < 2 ^ (prefixWord ++ tailWord_571527).sum := by decide
  have hdescent : baseEnd_571527 < baseStart_571527 := by decide
  rcases family_descends (prefixWord ++ tailWord_571527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571594 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_571594 : Nat := 118140960795 + 571594 * 2 ^ 59
def prefixEnd_571594 : Nat := 4983230072969 + 3 ^ 40 * 571594 * 2
def baseEnd_571594 : Nat := 293502461226141869546293

theorem tailTrace_571594 : CollatzResearch.WordTrace tailWord_571594 prefixEnd_571594 293502461226141869546293 := by
  unfold tailWord_571594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211936472805008332086459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13898497260813355552230557 5211936472805008332086459)
  ·
    refine ⟨7817904709207512498129689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211936472805008332086459 7817904709207512498129689)
    ·
      refine ⟨5863428531905634373597267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7817904709207512498129689 5863428531905634373597267)
      ·
        refine ⟨8795142797858451560395901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5863428531905634373597267 8795142797858451560395901)
        ·
          refine ⟨3298178549196919335148463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8795142797858451560395901 3298178549196919335148463)
          ·
            refine ⟨4947267823795379002722695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298178549196919335148463 4947267823795379002722695)
            ·
              refine ⟨7420901735693068504084043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947267823795379002722695 7420901735693068504084043)
              ·
                refine ⟨11131352603539602756126065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7420901735693068504084043 11131352603539602756126065)
                ·
                  refine ⟨8348514452654702067094549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11131352603539602756126065 8348514452654702067094549)
                  ·
                    refine ⟨391336614968189159395057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8348514452654702067094549 391336614968189159395057)
                    ·
                      refine ⟨293502461226141869546293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391336614968189159395057 293502461226141869546293)
                      ·
                        rfl

theorem cell23_571594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_571594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571594 prefixEnd_571594 := by exact prefixLift 571594
  have htrace : WordTrace (prefixWord ++ tailWord_571594) baseStart_571594 baseEnd_571594 := by
    simpa [prefixWord, tailWord_571594, baseEnd_571594] using wordTrace_append hprefix tailTrace_571594
  have hstable : (prefixWord ++ tailWord_571594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571594).length < 2 ^ (prefixWord ++ tailWord_571594).sum := by decide
  have hdescent : baseEnd_571594 < baseStart_571594 := by decide
  rcases family_descends (prefixWord ++ tailWord_571594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571607 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_571607 : Nat := 118140960795 + 571607 * 2 ^ 59
def prefixEnd_571607 : Nat := 4983230072969 + 3 ^ 40 * 571607 * 2
def baseEnd_571607 : Nat := 293509136474650318683733

theorem tailTrace_571607 : CollatzResearch.WordTrace tailWord_571607 prefixEnd_571607 293509136474650318683733 := by
  unfold tailWord_571607
  simp only [CollatzResearch.WordTrace]
  refine ⟨20848220040172936548569075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13898813360115291032379383 20848220040172936548569075)
  ·
    refine ⟨31272330060259404822853613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20848220040172936548569075 31272330060259404822853613)
    ·
      refine ⟨11727123772597276808570105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31272330060259404822853613 11727123772597276808570105)
      ·
        refine ⟨8795342829447957606427579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11727123772597276808570105 8795342829447957606427579)
        ·
          refine ⟨13193014244171936409641369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8795342829447957606427579 13193014244171936409641369)
          ·
            refine ⟨9894760683128952307231027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13193014244171936409641369 9894760683128952307231027)
            ·
              refine ⟨14842141024693428460846541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9894760683128952307231027 14842141024693428460846541)
              ·
                refine ⟨5565802884260035672817453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14842141024693428460846541 5565802884260035672817453)
                ·
                  refine ⟨2087176081597513377306545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5565802884260035672817453 2087176081597513377306545)
                  ·
                    refine ⟨1565382061198135032979909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087176081597513377306545 1565382061198135032979909)
                    ·
                      refine ⟨293509136474650318683733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1565382061198135032979909 293509136474650318683733)
                      ·
                        rfl

theorem cell23_571607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_571607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571607 prefixEnd_571607 := by exact prefixLift 571607
  have htrace : WordTrace (prefixWord ++ tailWord_571607) baseStart_571607 baseEnd_571607 := by
    simpa [prefixWord, tailWord_571607, baseEnd_571607] using wordTrace_append hprefix tailTrace_571607
  have hstable : (prefixWord ++ tailWord_571607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571607).length < 2 ^ (prefixWord ++ tailWord_571607).sum := by decide
  have hdescent : baseEnd_571607 < baseStart_571607 := by decide
  rcases family_descends (prefixWord ++ tailWord_571607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571634 : List Nat := [3, 2, 1, 3, 2, 2, 2, 8]
def baseStart_571634 : Nat := 118140960795 + 571634 * 2 ^ 59
def prefixEnd_571634 : Nat := 4983230072969 + 3 ^ 40 * 571634 * 2
def baseEnd_571634 : Nat := 10871222238974878260967

theorem tailTrace_571634 : CollatzResearch.WordTrace tailWord_571634 prefixEnd_571634 10871222238974878260967 := by
  unfold tailWord_571634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212301202768780039950489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13899469874050080106534637 5212301202768780039950489)
  ·
    refine ⟨3909225902076585029962867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5212301202768780039950489 3909225902076585029962867)
    ·
      refine ⟨5863838853114877544944301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909225902076585029962867 5863838853114877544944301)
      ·
        refine ⟨2198939569918079079354113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5863838853114877544944301 2198939569918079079354113)
        ·
          refine ⟨1649204677438559309515585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198939569918079079354113 1649204677438559309515585)
          ·
            refine ⟨1236903508078919482136689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649204677438559309515585 1236903508078919482136689)
            ·
              refine ⟨927677631059189611602517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236903508078919482136689 927677631059189611602517)
              ·
                refine ⟨10871222238974878260967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 927677631059189611602517 10871222238974878260967)
                ·
                  rfl

theorem cell23_571634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_571634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571634 prefixEnd_571634 := by exact prefixLift 571634
  have htrace : WordTrace (prefixWord ++ tailWord_571634) baseStart_571634 baseEnd_571634 := by
    simpa [prefixWord, tailWord_571634, baseEnd_571634] using wordTrace_append hprefix tailTrace_571634
  have hstable : (prefixWord ++ tailWord_571634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571634).length < 2 ^ (prefixWord ++ tailWord_571634).sum := by decide
  have hdescent : baseEnd_571634 < baseStart_571634 := by decide
  rcases family_descends (prefixWord ++ tailWord_571634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571638 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_571638 : Nat := 118140960795 + 571638 * 2 ^ 59
def prefixEnd_571638 : Nat := 4983230072969 + 3 ^ 40 * 571638 * 2
def baseEnd_571638 : Nat := 97841684791646565798697

theorem tailTrace_571638 : CollatzResearch.WordTrace tailWord_571638 prefixEnd_571638 97841684791646565798697 := by
  unfold tailWord_571638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303084418941289302684223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13899567135373752561965045 1303084418941289302684223)
  ·
    refine ⟨1954626628411933954026335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1303084418941289302684223 1954626628411933954026335)
    ·
      refine ⟨2931939942617900931039503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954626628411933954026335 2931939942617900931039503)
      ·
        refine ⟨4397909913926851396559255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931939942617900931039503 4397909913926851396559255)
        ·
          refine ⟨6596864870890277094838883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397909913926851396559255 6596864870890277094838883)
          ·
            refine ⟨9895297306335415642258325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596864870890277094838883 9895297306335415642258325)
            ·
              refine ⟨463842061234472608230859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9895297306335415642258325 463842061234472608230859)
              ·
                refine ⟨695763091851708912346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463842061234472608230859 695763091851708912346289)
                ·
                  refine ⟨521822318888781684259717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695763091851708912346289 521822318888781684259717)
                  ·
                    refine ⟨97841684791646565798697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 521822318888781684259717 97841684791646565798697)
                    ·
                      rfl

theorem cell23_571638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_571638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571638 prefixEnd_571638 := by exact prefixLift 571638
  have htrace : WordTrace (prefixWord ++ tailWord_571638) baseStart_571638 baseEnd_571638 := by
    simpa [prefixWord, tailWord_571638, baseEnd_571638] using wordTrace_append hprefix tailTrace_571638
  have hstable : (prefixWord ++ tailWord_571638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571638).length < 2 ^ (prefixWord ++ tailWord_571638).sum := by decide
  have hdescent : baseEnd_571638 < baseStart_571638 := by decide
  rcases family_descends (prefixWord ++ tailWord_571638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571667 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_571667 : Nat := 118140960795 + 571667 * 2 ^ 59
def prefixEnd_571667 : Nat := 4983230072969 + 3 ^ 40 * 571667 * 2
def baseEnd_571667 : Nat := 293539945313920083933457

theorem tailTrace_571667 : CollatzResearch.WordTrace tailWord_571667 prefixEnd_571667 293539945313920083933457 := by
  unfold tailWord_571667
  simp only [CollatzResearch.WordTrace]
  refine ⟨20850408419955566795753255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13900272279970377863835503 20850408419955566795753255)
  ·
    refine ⟨31275612629933350193629883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20850408419955566795753255 31275612629933350193629883)
    ·
      refine ⟨46913418944900025290444825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31275612629933350193629883 46913418944900025290444825)
      ·
        refine ⟨35185064208675018967833619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46913418944900025290444825 35185064208675018967833619)
        ·
          refine ⟨52777596313012528451750429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35185064208675018967833619 52777596313012528451750429)
          ·
            refine ⟨19791598617379698169406411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52777596313012528451750429 19791598617379698169406411)
            ·
              refine ⟨29687397926069547254109617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19791598617379698169406411 29687397926069547254109617)
              ·
                refine ⟨22265548444552160440582213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29687397926069547254109617 22265548444552160440582213)
                ·
                  refine ⟨4174790333353530082609165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22265548444552160440582213 4174790333353530082609165)
                  ·
                    refine ⟨1565546375007573780978437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4174790333353530082609165 1565546375007573780978437)
                    ·
                      refine ⟨293539945313920083933457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1565546375007573780978437 293539945313920083933457)
                      ·
                        rfl

theorem cell23_571667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_571667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571667 prefixEnd_571667 := by exact prefixLift 571667
  have htrace : WordTrace (prefixWord ++ tailWord_571667) baseStart_571667 baseEnd_571667 := by
    simpa [prefixWord, tailWord_571667, baseEnd_571667] using wordTrace_append hprefix tailTrace_571667
  have hstable : (prefixWord ++ tailWord_571667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571667).length < 2 ^ (prefixWord ++ tailWord_571667).sum := by decide
  have hdescent : baseEnd_571667 < baseStart_571667 := by decide
  rcases family_descends (prefixWord ++ tailWord_571667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571684 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_571684 : Nat := 118140960795 + 571684 * 2 ^ 59
def prefixEnd_571684 : Nat := 4983230072969 + 3 ^ 40 * 571684 * 2
def baseEnd_571684 : Nat := 293548674485046517420879

theorem tailTrace_571684 : CollatzResearch.WordTrace tailWord_571684 prefixEnd_571684 293548674485046517420879 := by
  unfold tailWord_571684
  simp only [CollatzResearch.WordTrace]
  refine ⟨10425514230446989349561053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13900685640595985799414737 10425514230446989349561053)
  ·
    refine ⟨3909567836417621006085395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10425514230446989349561053 3909567836417621006085395)
    ·
      refine ⟨5864351754626431509128093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909567836417621006085395 5864351754626431509128093)
      ·
        refine ⟨2199131907984911815923035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5864351754626431509128093 2199131907984911815923035)
        ·
          refine ⟨3298697861977367723884553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199131907984911815923035 3298697861977367723884553)
          ·
            refine ⟨2474023396483025792913415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3298697861977367723884553 2474023396483025792913415)
            ·
              refine ⟨3711035094724538689370123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474023396483025792913415 3711035094724538689370123)
              ·
                refine ⟨5566552642086808034055185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711035094724538689370123 5566552642086808034055185)
                ·
                  refine ⟨4174914481565106025541389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5566552642086808034055185 4174914481565106025541389)
                  ·
                    refine ⟨1565592930586914759578021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4174914481565106025541389 1565592930586914759578021)
                    ·
                      refine ⟨293548674485046517420879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1565592930586914759578021 293548674485046517420879)
                      ·
                        rfl

theorem cell23_571684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_571684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571684 prefixEnd_571684 := by exact prefixLift 571684
  have htrace : WordTrace (prefixWord ++ tailWord_571684) baseStart_571684 baseEnd_571684 := by
    simpa [prefixWord, tailWord_571684, baseEnd_571684] using wordTrace_append hprefix tailTrace_571684
  have hstable : (prefixWord ++ tailWord_571684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571684).length < 2 ^ (prefixWord ++ tailWord_571684).sum := by decide
  have hdescent : baseEnd_571684 < baseStart_571684 := by decide
  rcases family_descends (prefixWord ++ tailWord_571684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571717 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_571717 : Nat := 118140960795 + 571717 * 2 ^ 59
def prefixEnd_571717 : Nat := 4983230072969 + 3 ^ 40 * 571717 * 2
def baseEnd_571717 : Nat := 293565619346644888308227

theorem tailTrace_571717 : CollatzResearch.WordTrace tailWord_571717 prefixEnd_571717 293565619346644888308227 := by
  unfold tailWord_571717
  simp only [CollatzResearch.WordTrace]
  refine ⟨20852232069774425335073405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13901488046516283556715603 20852232069774425335073405)
  ·
    refine ⟨7819587026165409500652527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20852232069774425335073405 7819587026165409500652527)
    ·
      refine ⟨11729380539248114250978791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7819587026165409500652527 11729380539248114250978791)
      ·
        refine ⟨17594070808872171376468187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11729380539248114250978791 17594070808872171376468187)
        ·
          refine ⟨26391106213308257064702281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17594070808872171376468187 26391106213308257064702281)
          ·
            refine ⟨19793329659981192798526711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26391106213308257064702281 19793329659981192798526711)
            ·
              refine ⟨29689994489971789197790067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19793329659981192798526711 29689994489971789197790067)
              ·
                refine ⟨44534991734957683796685101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29689994489971789197790067 44534991734957683796685101)
                ·
                  refine ⟨16700621900609131423756913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44534991734957683796685101 16700621900609131423756913)
                  ·
                    refine ⟨12525466425456848567817685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16700621900609131423756913 12525466425456848567817685)
                    ·
                      refine ⟨293565619346644888308227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12525466425456848567817685 293565619346644888308227)
                      ·
                        rfl

theorem cell23_571717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_571717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571717 prefixEnd_571717 := by exact prefixLift 571717
  have htrace : WordTrace (prefixWord ++ tailWord_571717) baseStart_571717 baseEnd_571717 := by
    simpa [prefixWord, tailWord_571717, baseEnd_571717] using wordTrace_append hprefix tailTrace_571717
  have hstable : (prefixWord ++ tailWord_571717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571717).length < 2 ^ (prefixWord ++ tailWord_571717).sum := by decide
  have hdescent : baseEnd_571717 < baseStart_571717 := by decide
  rcases family_descends (prefixWord ++ tailWord_571717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571751 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_571751 : Nat := 118140960795 + 571751 * 2 ^ 59
def prefixEnd_571751 : Nat := 4983230072969 + 3 ^ 40 * 571751 * 2
def baseEnd_571751 : Nat := 293583077688897755283071

theorem tailTrace_571751 : CollatzResearch.WordTrace tailWord_571751 prefixEnd_571751 293583077688897755283071 := by
  unfold tailWord_571751
  simp only [CollatzResearch.WordTrace]
  refine ⟨20853472151651249141811107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13902314767767499427874071 20853472151651249141811107)
  ·
    refine ⟨31280208227476873712716661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20853472151651249141811107 31280208227476873712716661)
    ·
      refine ⟨2932519521325956910567187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31280208227476873712716661 2932519521325956910567187)
      ·
        refine ⟨4398779281988935365850781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932519521325956910567187 4398779281988935365850781)
        ·
          refine ⟨1649542230745850762194043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4398779281988935365850781 1649542230745850762194043)
          ·
            refine ⟨2474313346118776143291065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649542230745850762194043 2474313346118776143291065)
            ·
              refine ⟨1855735009589082107468299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474313346118776143291065 1855735009589082107468299)
              ·
                refine ⟨2783602514383623161202449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855735009589082107468299 2783602514383623161202449)
                ·
                  refine ⟨2087701885787717370901837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783602514383623161202449 2087701885787717370901837)
                  ·
                    refine ⟨782888207170394014088189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087701885787717370901837 782888207170394014088189)
                    ·
                      refine ⟨293583077688897755283071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 782888207170394014088189 293583077688897755283071)
                      ·
                        rfl

theorem cell23_571751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_571751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571751 prefixEnd_571751 := by exact prefixLift 571751
  have htrace : WordTrace (prefixWord ++ tailWord_571751) baseStart_571751 baseEnd_571751 := by
    simpa [prefixWord, tailWord_571751, baseEnd_571751] using wordTrace_append hprefix tailTrace_571751
  have hstable : (prefixWord ++ tailWord_571751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571751).length < 2 ^ (prefixWord ++ tailWord_571751).sum := by decide
  have hdescent : baseEnd_571751 < baseStart_571751 := by decide
  rcases family_descends (prefixWord ++ tailWord_571751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571752 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_571752 : Nat := 118140960795 + 571752 * 2 ^ 59
def prefixEnd_571752 : Nat := 4983230072969 + 3 ^ 40 * 571752 * 2
def baseEnd_571752 : Nat := 293583591169552251370567

theorem tailTrace_571752 : CollatzResearch.WordTrace tailWord_571752 prefixEnd_571752 293583591169552251370567 := by
  unfold tailWord_571752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10426754312323813156298755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13902339083098417541731673 10426754312323813156298755)
  ·
    refine ⟨15640131468485719734448133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10426754312323813156298755 15640131468485719734448133)
    ·
      refine ⟨2932524650341072450209025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15640131468485719734448133 2932524650341072450209025)
      ·
        refine ⟨2199393487755804337656769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2932524650341072450209025 2199393487755804337656769)
        ·
          refine ⟨1649545115816853253242577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2199393487755804337656769 1649545115816853253242577)
          ·
            refine ⟨1237158836862639939931933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649545115816853253242577 1237158836862639939931933)
            ·
              refine ⟨463934563823489977474475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1237158836862639939931933 463934563823489977474475)
              ·
                refine ⟨695901845735234966211713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463934563823489977474475 695901845735234966211713)
                ·
                  refine ⟨521926384301426224658785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 695901845735234966211713 521926384301426224658785)
                  ·
                    refine ⟨391444788226069668494089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 521926384301426224658785 391444788226069668494089)
                    ·
                      refine ⟨293583591169552251370567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391444788226069668494089 293583591169552251370567)
                      ·
                        rfl

theorem cell23_571752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_571752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571752 prefixEnd_571752 := by exact prefixLift 571752
  have htrace : WordTrace (prefixWord ++ tailWord_571752) baseStart_571752 baseEnd_571752 := by
    simpa [prefixWord, tailWord_571752, baseEnd_571752] using wordTrace_append hprefix tailTrace_571752
  have hstable : (prefixWord ++ tailWord_571752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571752).length < 2 ^ (prefixWord ++ tailWord_571752).sum := by decide
  have hdescent : baseEnd_571752 < baseStart_571752 := by decide
  rcases family_descends (prefixWord ++ tailWord_571752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571851 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 5, 2]
def baseStart_571851 : Nat := 118140960795 + 571851 * 2 ^ 59
def prefixEnd_571851 : Nat := 4983230072969 + 3 ^ 40 * 571851 * 2
def baseEnd_571851 : Nat := 293634425754347364032611

theorem tailTrace_571851 : CollatzResearch.WordTrace tailWord_571851 prefixEnd_571851 293634425754347364032611 := by
  unfold tailWord_571851
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857119451288966220451407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13904746300859310813634271 20857119451288966220451407)
  ·
    refine ⟨31285679176933449330677111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20857119451288966220451407 31285679176933449330677111)
    ·
      refine ⟨46928518765400173996015667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31285679176933449330677111 46928518765400173996015667)
      ·
        refine ⟨70392778148100260994023501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46928518765400173996015667 70392778148100260994023501)
        ·
          refine ⟨26397291805537597872758813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70392778148100260994023501 26397291805537597872758813)
          ·
            refine ⟨9898984427076599202284555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26397291805537597872758813 9898984427076599202284555)
            ·
              refine ⟨14848476640614898803426833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9898984427076599202284555 14848476640614898803426833)
              ·
                refine ⟨11136357480461174102570125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14848476640614898803426833 11136357480461174102570125)
                ·
                  refine ⟨4176134055172940288463797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11136357480461174102570125 4176134055172940288463797)
                  ·
                    refine ⟨391512567672463152043481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4176134055172940288463797 391512567672463152043481)
                    ·
                      refine ⟨293634425754347364032611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391512567672463152043481 293634425754347364032611)
                      ·
                        rfl

theorem cell23_571851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5, 2].length) (baseStart_571851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571851 prefixEnd_571851 := by exact prefixLift 571851
  have htrace : WordTrace (prefixWord ++ tailWord_571851) baseStart_571851 baseEnd_571851 := by
    simpa [prefixWord, tailWord_571851, baseEnd_571851] using wordTrace_append hprefix tailTrace_571851
  have hstable : (prefixWord ++ tailWord_571851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571851).length < 2 ^ (prefixWord ++ tailWord_571851).sum := by decide
  have hdescent : baseEnd_571851 < baseStart_571851 := by decide
  rcases family_descends (prefixWord ++ tailWord_571851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571861 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_571861 : Nat := 118140960795 + 571861 * 2 ^ 59
def prefixEnd_571861 : Nat := 4983230072969 + 3 ^ 40 * 571861 * 2
def baseEnd_571861 : Nat := 97879853520297441635855

theorem tailTrace_571861 : CollatzResearch.WordTrace tailWord_571861 prefixEnd_571861 97879853520297441635855 := by
  unfold tailWord_571861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857484181252737928315437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13904989454168491952210291 20857484181252737928315437)
  ·
    refine ⟨7821556567969776723118289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20857484181252737928315437 7821556567969776723118289)
    ·
      refine ⟨5866167425977332542338717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7821556567969776723118289 5866167425977332542338717)
      ·
        refine ⟨2199812784741499703377019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5866167425977332542338717 2199812784741499703377019)
        ·
          refine ⟨3299719177112249555065529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199812784741499703377019 3299719177112249555065529)
          ·
            refine ⟨2474789382834187166299147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299719177112249555065529 2474789382834187166299147)
            ·
              refine ⟨3712184074251280749448721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474789382834187166299147 3712184074251280749448721)
              ·
                refine ⟨2784138055688460562086541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712184074251280749448721 2784138055688460562086541)
                ·
                  refine ⟨1044051770883172710782453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2784138055688460562086541 1044051770883172710782453)
                  ·
                    refine ⟨97879853520297441635855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1044051770883172710782453 97879853520297441635855)
                    ·
                      rfl

theorem cell23_571861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_571861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571861 prefixEnd_571861 := by exact prefixLift 571861
  have htrace : WordTrace (prefixWord ++ tailWord_571861) baseStart_571861 baseEnd_571861 := by
    simpa [prefixWord, tailWord_571861, baseEnd_571861] using wordTrace_append hprefix tailTrace_571861
  have hstable : (prefixWord ++ tailWord_571861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571861).length < 2 ^ (prefixWord ++ tailWord_571861).sum := by decide
  have hdescent : baseEnd_571861 < baseStart_571861 := by decide
  rcases family_descends (prefixWord ++ tailWord_571861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571875 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 3]
def baseStart_571875 : Nat := 118140960795 + 571875 * 2 ^ 59
def prefixEnd_571875 : Nat := 4983230072969 + 3 ^ 40 * 571875 * 2
def baseEnd_571875 : Nat := 293646749290055270132501

theorem tailTrace_571875 : CollatzResearch.WordTrace tailWord_571875 prefixEnd_571875 293646749290055270132501 := by
  unfold tailWord_571875
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857994803202018319325079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905329868801345546216719 20857994803202018319325079)
  ·
    refine ⟨31286992204803027478987619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20857994803202018319325079 31286992204803027478987619)
    ·
      refine ⟨46930488307204541218481429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31286992204803027478987619 46930488307204541218481429)
      ·
        refine ⟨2199866639400212869616317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46930488307204541218481429 2199866639400212869616317)
        ·
          refine ⟨824949989775079826106119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2199866639400212869616317 824949989775079826106119)
          ·
            refine ⟨1237424984662619739159179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824949989775079826106119 1237424984662619739159179)
            ·
              refine ⟨1856137476993929608738769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237424984662619739159179 1856137476993929608738769)
              ·
                refine ⟨1392103107745447206554077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856137476993929608738769 1392103107745447206554077)
                ·
                  refine ⟨522038665404542702457779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1392103107745447206554077 522038665404542702457779)
                  ·
                    refine ⟨783057998106814053686669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522038665404542702457779 783057998106814053686669)
                    ·
                      refine ⟨293646749290055270132501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783057998106814053686669 293646749290055270132501)
                      ·
                        rfl

theorem cell23_571875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_571875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571875 prefixEnd_571875 := by exact prefixLift 571875
  have htrace : WordTrace (prefixWord ++ tailWord_571875) baseStart_571875 baseEnd_571875 := by
    simpa [prefixWord, tailWord_571875, baseEnd_571875] using wordTrace_append hprefix tailTrace_571875
  have hstable : (prefixWord ++ tailWord_571875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571875).length < 2 ^ (prefixWord ++ tailWord_571875).sum := by decide
  have hdescent : baseEnd_571875 < baseStart_571875 := by decide
  rcases family_descends (prefixWord ++ tailWord_571875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571881 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 8, 2]
def baseStart_571881 : Nat := 118140960795 + 571881 * 2 ^ 59
def prefixEnd_571881 : Nat := 4983230072969 + 3 ^ 40 * 571881 * 2
def baseEnd_571881 : Nat := 293649830173982246657473

theorem tailTrace_571881 : CollatzResearch.WordTrace tailWord_571881 prefixEnd_571881 293649830173982246657473 := by
  unfold tailWord_571881
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858213641180281344043497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905475760786854229362331 20858213641180281344043497)
  ·
    refine ⟨15643660230885211008032623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20858213641180281344043497 15643660230885211008032623)
    ·
      refine ⟨23465490346327816512048935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15643660230885211008032623 23465490346327816512048935)
      ·
        refine ⟨35198235519491724768073403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23465490346327816512048935 35198235519491724768073403)
        ·
          refine ⟨52797353279237587152110105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35198235519491724768073403 52797353279237587152110105)
          ·
            refine ⟨39598014959428190364082579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52797353279237587152110105 39598014959428190364082579)
            ·
              refine ⟨59397022439142285546123869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39598014959428190364082579 59397022439142285546123869)
              ·
                refine ⟨22273883414678357079796451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59397022439142285546123869 22273883414678357079796451)
                ·
                  refine ⟨33410825122017535619694677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22273883414678357079796451 33410825122017535619694677)
                  ·
                    refine ⟨391533106898642995543297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33410825122017535619694677 391533106898642995543297)
                    ·
                      refine ⟨293649830173982246657473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391533106898642995543297 293649830173982246657473)
                      ·
                        rfl

theorem cell23_571881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8, 2].length) (baseStart_571881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571881 prefixEnd_571881 := by exact prefixLift 571881
  have htrace : WordTrace (prefixWord ++ tailWord_571881) baseStart_571881 baseEnd_571881 := by
    simpa [prefixWord, tailWord_571881, baseEnd_571881] using wordTrace_append hprefix tailTrace_571881
  have hstable : (prefixWord ++ tailWord_571881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571881).length < 2 ^ (prefixWord ++ tailWord_571881).sum := by decide
  have hdescent : baseEnd_571881 < baseStart_571881 := by decide
  rcases family_descends (prefixWord ++ tailWord_571881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571885 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_571885 : Nat := 118140960795 + 571885 * 2 ^ 59
def prefixEnd_571885 : Nat := 4983230072969 + 3 ^ 40 * 571885 * 2
def baseEnd_571885 : Nat := 293651884096600231007455

theorem tailTrace_571885 : CollatzResearch.WordTrace tailWord_571885 prefixEnd_571885 293651884096600231007455 := by
  unfold tailWord_571885
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858359533165790027189109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905573022110526684792739 20858359533165790027189109)
  ·
    refine ⟨1955471206234292815048979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20858359533165790027189109 1955471206234292815048979)
    ·
      refine ⟨2933206809351439222573469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955471206234292815048979 2933206809351439222573469)
      ·
        refine ⟨1099952553506789708465051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2933206809351439222573469 1099952553506789708465051)
        ·
          refine ⟨1649928830260184562697577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099952553506789708465051 1649928830260184562697577)
          ·
            refine ⟨1237446622695138422023183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649928830260184562697577 1237446622695138422023183)
            ·
              refine ⟨1856169934042707633034775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237446622695138422023183 1856169934042707633034775)
              ·
                refine ⟨2784254901064061449552163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856169934042707633034775 2784254901064061449552163)
                ·
                  refine ⟨4176382351596092174328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784254901064061449552163 4176382351596092174328245)
                  ·
                    refine ⟨391535845462133641343273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4176382351596092174328245 391535845462133641343273)
                    ·
                      refine ⟨293651884096600231007455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391535845462133641343273 293651884096600231007455)
                      ·
                        rfl

theorem cell23_571885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_571885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571885 prefixEnd_571885 := by exact prefixLift 571885
  have htrace : WordTrace (prefixWord ++ tailWord_571885) baseStart_571885 baseEnd_571885 := by
    simpa [prefixWord, tailWord_571885, baseEnd_571885] using wordTrace_append hprefix tailTrace_571885
  have hstable : (prefixWord ++ tailWord_571885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571885).length < 2 ^ (prefixWord ++ tailWord_571885).sum := by decide
  have hdescent : baseEnd_571885 < baseStart_571885 := by decide
  rcases family_descends (prefixWord ++ tailWord_571885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571891 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 4, 4]
def baseStart_571891 : Nat := 118140960795 + 571891 * 2 ^ 59
def prefixEnd_571891 : Nat := 4983230072969 + 3 ^ 40 * 571891 * 2
def baseEnd_571891 : Nat := 97884988326842402510809

theorem tailTrace_571891 : CollatzResearch.WordTrace tailWord_571891 prefixEnd_571891 97884988326842402510809 := by
  unfold tailWord_571891
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858578371144053051907527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905718914096035367938351 20858578371144053051907527)
  ·
    refine ⟨31287867556716079577861291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20858578371144053051907527 31287867556716079577861291)
    ·
      refine ⟨46931801335074119366791937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31287867556716079577861291 46931801335074119366791937)
      ·
        refine ⟨35198851001305589525093953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46931801335074119366791937 35198851001305589525093953)
        ·
          refine ⟨26399138250979192143820465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35198851001305589525093953 26399138250979192143820465)
          ·
            refine ⟨19799353688234394107865349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26399138250979192143820465 19799353688234394107865349)
            ·
              refine ⟨3712378816543948895224753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19799353688234394107865349 3712378816543948895224753)
              ·
                refine ⟨2784284112407961671418565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712378816543948895224753 2784284112407961671418565)
                ·
                  refine ⟨522053271076492813390981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2784284112407961671418565 522053271076492813390981)
                  ·
                    refine ⟨97884988326842402510809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522053271076492813390981 97884988326842402510809)
                    ·
                      rfl

theorem cell23_571891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 4].length) (baseStart_571891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571891 prefixEnd_571891 := by exact prefixLift 571891
  have htrace : WordTrace (prefixWord ++ tailWord_571891) baseStart_571891 baseEnd_571891 := by
    simpa [prefixWord, tailWord_571891, baseEnd_571891] using wordTrace_append hprefix tailTrace_571891
  have hstable : (prefixWord ++ tailWord_571891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571891).length < 2 ^ (prefixWord ++ tailWord_571891).sum := by decide
  have hdescent : baseEnd_571891 < baseStart_571891 := by decide
  rcases family_descends (prefixWord ++ tailWord_571891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571901 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_571901 : Nat := 118140960795 + 571901 * 2 ^ 59
def prefixEnd_571901 : Nat := 4983230072969 + 3 ^ 40 * 571901 * 2
def baseEnd_571901 : Nat := 293660099787072168407381

theorem tailTrace_571901 : CollatzResearch.WordTrace tailWord_571901 prefixEnd_571901 293660099787072168407381 := by
  unfold tailWord_571901
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858943101107824759771557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13905962067405216506514371 20858943101107824759771557)
  ·
    refine ⟨3911051831457717142457167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20858943101107824759771557 3911051831457717142457167)
    ·
      refine ⟨5866577747186575713685751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911051831457717142457167 5866577747186575713685751)
      ·
        refine ⟨8799866620779863570528627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866577747186575713685751 8799866620779863570528627)
        ·
          refine ⟨13199799931169795355792941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799866620779863570528627 13199799931169795355792941)
          ·
            refine ⟨4949924974188673258422353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13199799931169795355792941 4949924974188673258422353)
            ·
              refine ⟨3712443730641504943816765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4949924974188673258422353 3712443730641504943816765)
              ·
                refine ⟨1392166398990564353931287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3712443730641504943816765 1392166398990564353931287)
                ·
                  refine ⟨2088249598485846530896931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392166398990564353931287 2088249598485846530896931)
                  ·
                    refine ⟨3132374397728769796345397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2088249598485846530896931 3132374397728769796345397)
                    ·
                      refine ⟨293660099787072168407381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3132374397728769796345397 293660099787072168407381)
                      ·
                        rfl

theorem cell23_571901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_571901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571901 prefixEnd_571901 := by exact prefixLift 571901
  have htrace : WordTrace (prefixWord ++ tailWord_571901) baseStart_571901 baseEnd_571901 := by
    simpa [prefixWord, tailWord_571901, baseEnd_571901] using wordTrace_append hprefix tailTrace_571901
  have hstable : (prefixWord ++ tailWord_571901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571901).length < 2 ^ (prefixWord ++ tailWord_571901).sum := by decide
  have hdescent : baseEnd_571901 < baseStart_571901 := by decide
  rcases family_descends (prefixWord ++ tailWord_571901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571915 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 3, 2, 2]
def baseStart_571915 : Nat := 118140960795 + 571915 * 2 ^ 59
def prefixEnd_571915 : Nat := 4983230072969 + 3 ^ 40 * 571915 * 2
def baseEnd_571915 : Nat := 293667288516235113632317

theorem tailTrace_571915 : CollatzResearch.WordTrace tailWord_571915 prefixEnd_571915 293667288516235113632317 := by
  unfold tailWord_571915
  simp only [CollatzResearch.WordTrace]
  refine ⟨20859453723057105150781199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13906302482038070100520799 20859453723057105150781199)
  ·
    refine ⟨31289180584585657726171799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20859453723057105150781199 31289180584585657726171799)
    ·
      refine ⟨46933770876878486589257699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31289180584585657726171799 46933770876878486589257699)
      ·
        refine ⟨70400656315317729883886549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46933770876878486589257699 70400656315317729883886549)
        ·
          refine ⟨1650015382390259294153591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70400656315317729883886549 1650015382390259294153591)
          ·
            refine ⟨2475023073585388941230387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650015382390259294153591 2475023073585388941230387)
            ·
              refine ⟨3712534610378083411845581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475023073585388941230387 3712534610378083411845581)
              ·
                refine ⟨1392200478891781279442093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3712534610378083411845581 1392200478891781279442093)
                ·
                  refine ⟨522075179584417979790785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1392200478891781279442093 522075179584417979790785)
                  ·
                    refine ⟨391556384688313484843089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522075179584417979790785 391556384688313484843089)
                    ·
                      refine ⟨293667288516235113632317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391556384688313484843089 293667288516235113632317)
                      ·
                        rfl

theorem cell23_571915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 2, 2].length) (baseStart_571915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571915 prefixEnd_571915 := by exact prefixLift 571915
  have htrace : WordTrace (prefixWord ++ tailWord_571915) baseStart_571915 baseEnd_571915 := by
    simpa [prefixWord, tailWord_571915, baseEnd_571915] using wordTrace_append hprefix tailTrace_571915
  have hstable : (prefixWord ++ tailWord_571915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571915).length < 2 ^ (prefixWord ++ tailWord_571915).sum := by decide
  have hdescent : baseEnd_571915 < baseStart_571915 := by decide
  rcases family_descends (prefixWord ++ tailWord_571915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571918 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_571918 : Nat := 118140960795 + 571918 * 2 ^ 59
def prefixEnd_571918 : Nat := 4983230072969 + 3 ^ 40 * 571918 * 2
def baseEnd_571918 : Nat := 293668828958198601894803

theorem tailTrace_571918 : CollatzResearch.WordTrace tailWord_571918 prefixEnd_571918 293668828958198601894803 := by
  unfold tailWord_571918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607445392755779582892551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13906375428030824442093605 2607445392755779582892551)
  ·
    refine ⟨3911168089133669374338827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2607445392755779582892551 3911168089133669374338827)
    ·
      refine ⟨5866752133700504061508241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911168089133669374338827 5866752133700504061508241)
      ·
        refine ⟨4400064100275378046131181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5866752133700504061508241 4400064100275378046131181)
        ·
          refine ⟨1650024037603266767299193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4400064100275378046131181 1650024037603266767299193)
          ·
            refine ⟨1237518028202450075474395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1650024037603266767299193 1237518028202450075474395)
            ·
              refine ⟨1856277042303675113211593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237518028202450075474395 1856277042303675113211593)
              ·
                refine ⟨1392207781727756334908695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856277042303675113211593 1392207781727756334908695)
                ·
                  refine ⟨2088311672591634502363043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392207781727756334908695 2088311672591634502363043)
                  ·
                    refine ⟨3132467508887451753544565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2088311672591634502363043 3132467508887451753544565)
                    ·
                      refine ⟨293668828958198601894803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3132467508887451753544565 293668828958198601894803)
                      ·
                        rfl

theorem cell23_571918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_571918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571918 prefixEnd_571918 := by exact prefixLift 571918
  have htrace : WordTrace (prefixWord ++ tailWord_571918) baseStart_571918 baseEnd_571918 := by
    simpa [prefixWord, tailWord_571918, baseEnd_571918] using wordTrace_append hprefix tailTrace_571918
  have hstable : (prefixWord ++ tailWord_571918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571918).length < 2 ^ (prefixWord ++ tailWord_571918).sum := by decide
  have hdescent : baseEnd_571918 < baseStart_571918 := by decide
  rcases family_descends (prefixWord ++ tailWord_571918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571925 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_571925 : Nat := 118140960795 + 571925 * 2 ^ 59
def prefixEnd_571925 : Nat := 4983230072969 + 3 ^ 40 * 571925 * 2
def baseEnd_571925 : Nat := 97890807774260024835757

theorem tailTrace_571925 : CollatzResearch.WordTrace tailWord_571925 prefixEnd_571925 97890807774260024835757 := by
  unfold tailWord_571925
  simp only [CollatzResearch.WordTrace]
  refine ⟨20859818453020876858645229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13906545635347251239096819 20859818453020876858645229)
  ·
    refine ⟨7822431919882828821991961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20859818453020876858645229 7822431919882828821991961)
    ·
      refine ⟨5866823939912121616493971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7822431919882828821991961 5866823939912121616493971)
      ·
        refine ⟨8800235909868182424740957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866823939912121616493971 8800235909868182424740957)
        ·
          refine ⟨3300088466200568409277859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8800235909868182424740957 3300088466200568409277859)
          ·
            refine ⟨4950132699300852613916789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300088466200568409277859 4950132699300852613916789)
            ·
              refine ⟨464074940559454932554699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4950132699300852613916789 464074940559454932554699)
              ·
                refine ⟨696112410839182398832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464074940559454932554699 696112410839182398832049)
                ·
                  refine ⟨522084308129386799124037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 696112410839182398832049 522084308129386799124037)
                  ·
                    refine ⟨97890807774260024835757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522084308129386799124037 97890807774260024835757)
                    ·
                      rfl

theorem cell23_571925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_571925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571925 prefixEnd_571925 := by exact prefixLift 571925
  have htrace : WordTrace (prefixWord ++ tailWord_571925) baseStart_571925 baseEnd_571925 := by
    simpa [prefixWord, tailWord_571925, baseEnd_571925] using wordTrace_append hprefix tailTrace_571925
  have hstable : (prefixWord ++ tailWord_571925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571925).length < 2 ^ (prefixWord ++ tailWord_571925).sum := by decide
  have hdescent : baseEnd_571925 < baseStart_571925 := by decide
  rcases family_descends (prefixWord ++ tailWord_571925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571928 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_571928 : Nat := 118140960795 + 571928 * 2 ^ 59
def prefixEnd_571928 : Nat := 4983230072969 + 3 ^ 40 * 571928 * 2
def baseEnd_571928 : Nat := 293673963764743562769757

theorem tailTrace_571928 : CollatzResearch.WordTrace tailWord_571928 prefixEnd_571928 293673963764743562769757 := by
  unfold tailWord_571928
  simp only [CollatzResearch.WordTrace]
  refine ⟨10429963936005004185502219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13906618581340005580669625 10429963936005004185502219)
  ·
    refine ⟨15644945904007506278253329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10429963936005004185502219 15644945904007506278253329)
    ·
      refine ⟨11733709428005629708689997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15644945904007506278253329 11733709428005629708689997)
      ·
        refine ⟨4400141035502111140758749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11733709428005629708689997 4400141035502111140758749)
        ·
          refine ⟨1650052888313291677784531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4400141035502111140758749 1650052888313291677784531)
          ·
            refine ⟨2475079332469937516676797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650052888313291677784531 2475079332469937516676797)
            ·
              refine ⟨928154749676226568753799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2475079332469937516676797 928154749676226568753799)
              ·
                refine ⟨1392232124514339853130699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928154749676226568753799 1392232124514339853130699)
                ·
                  refine ⟨2088348186771509779696049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392232124514339853130699 2088348186771509779696049)
                  ·
                    refine ⟨1566261140078632334772037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088348186771509779696049 1566261140078632334772037)
                    ·
                      refine ⟨293673963764743562769757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1566261140078632334772037 293673963764743562769757)
                      ·
                        rfl

theorem cell23_571928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_571928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571928 prefixEnd_571928 := by exact prefixLift 571928
  have htrace : WordTrace (prefixWord ++ tailWord_571928) baseStart_571928 baseEnd_571928 := by
    simpa [prefixWord, tailWord_571928, baseEnd_571928] using wordTrace_append hprefix tailTrace_571928
  have hstable : (prefixWord ++ tailWord_571928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571928).length < 2 ^ (prefixWord ++ tailWord_571928).sum := by decide
  have hdescent : baseEnd_571928 < baseStart_571928 := by decide
  rcases family_descends (prefixWord ++ tailWord_571928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571943 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_571943 : Nat := 118140960795 + 571943 * 2 ^ 59
def prefixEnd_571943 : Nat := 4983230072969 + 3 ^ 40 * 571943 * 2
def baseEnd_571943 : Nat := 293681665974561004082189

theorem tailTrace_571943 : CollatzResearch.WordTrace tailWord_571943 prefixEnd_571943 293681665974561004082189 := by
  unfold tailWord_571943
  simp only [CollatzResearch.WordTrace]
  refine ⟨20860474966955665932800483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13906983311303777288533655 20860474966955665932800483)
  ·
    refine ⟨31290712450433498899200725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20860474966955665932800483 31290712450433498899200725)
    ·
      refine ⟨733376073057035130450017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31290712450433498899200725 733376073057035130450017)
      ·
        refine ⟨550032054792776347837513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733376073057035130450017 550032054792776347837513)
        ·
          refine ⟨412524041094582260878135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550032054792776347837513 412524041094582260878135)
          ·
            refine ⟨618786061641873391317203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412524041094582260878135 618786061641873391317203)
            ·
              refine ⟨928179092462810086975805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618786061641873391317203 928179092462810086975805)
              ·
                refine ⟨348067159673553782615927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928179092462810086975805 348067159673553782615927)
                ·
                  refine ⟨522100739510330673923891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348067159673553782615927 522100739510330673923891)
                  ·
                    refine ⟨783151109265496010885837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522100739510330673923891 783151109265496010885837)
                    ·
                      refine ⟨293681665974561004082189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783151109265496010885837 293681665974561004082189)
                      ·
                        rfl

theorem cell23_571943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_571943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571943 prefixEnd_571943 := by exact prefixLift 571943
  have htrace : WordTrace (prefixWord ++ tailWord_571943) baseStart_571943 baseEnd_571943 := by
    simpa [prefixWord, tailWord_571943, baseEnd_571943] using wordTrace_append hprefix tailTrace_571943
  have hstable : (prefixWord ++ tailWord_571943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571943).length < 2 ^ (prefixWord ++ tailWord_571943).sum := by decide
  have hdescent : baseEnd_571943 < baseStart_571943 := by decide
  rcases family_descends (prefixWord ++ tailWord_571943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571961 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_571961 : Nat := 118140960795 + 571961 * 2 ^ 59
def prefixEnd_571961 : Nat := 4983230072969 + 3 ^ 40 * 571961 * 2
def baseEnd_571961 : Nat := 293690908626341933657105

theorem tailTrace_571961 : CollatzResearch.WordTrace tailWord_571961 prefixEnd_571961 293690908626341933657105 := by
  unfold tailWord_571961
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861131480890455006955737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13907420987260303337970491 20861131480890455006955737)
  ·
    refine ⟨15645848610667841255216803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20861131480890455006955737 15645848610667841255216803)
    ·
      refine ⟨23468772916001761882825205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15645848610667841255216803 23468772916001761882825205)
      ·
        refine ⟨2200197460875165176514863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23468772916001761882825205 2200197460875165176514863)
        ·
          refine ⟨3300296191312747764772295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200197460875165176514863 3300296191312747764772295)
          ·
            refine ⟨4950444286969121647158443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300296191312747764772295 4950444286969121647158443)
            ·
              refine ⟨7425666430453682470737665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950444286969121647158443 7425666430453682470737665)
              ·
                refine ⟨5569249822840261853053249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7425666430453682470737665 5569249822840261853053249)
                ·
                  refine ⟨4176937367130196389789937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5569249822840261853053249 4176937367130196389789937)
                  ·
                    refine ⟨3132703025347647292342453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4176937367130196389789937 3132703025347647292342453)
                    ·
                      refine ⟨293690908626341933657105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3132703025347647292342453 293690908626341933657105)
                      ·
                        rfl

theorem cell23_571961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_571961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571961 prefixEnd_571961 := by exact prefixLift 571961
  have htrace : WordTrace (prefixWord ++ tailWord_571961) baseStart_571961 baseEnd_571961 := by
    simpa [prefixWord, tailWord_571961, baseEnd_571961] using wordTrace_append hprefix tailTrace_571961
  have hstable : (prefixWord ++ tailWord_571961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571961).length < 2 ^ (prefixWord ++ tailWord_571961).sum := by decide
  have hdescent : baseEnd_571961 < baseStart_571961 := by decide
  rcases family_descends (prefixWord ++ tailWord_571961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571965 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_571965 : Nat := 118140960795 + 571965 * 2 ^ 59
def prefixEnd_571965 : Nat := 4983230072969 + 3 ^ 40 * 571965 * 2
def baseEnd_571965 : Nat := 293692962548959918007087

theorem tailTrace_571965 : CollatzResearch.WordTrace tailWord_571965 prefixEnd_571965 293692962548959918007087 := by
  unfold tailWord_571965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861277372875963690101349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13907518248583975793400899 20861277372875963690101349)
  ·
    refine ⟨3911489507414243191894003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20861277372875963690101349 3911489507414243191894003)
    ·
      refine ⟨5867234261121364787841005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911489507414243191894003 5867234261121364787841005)
      ·
        refine ⟨2200212847920511795440377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5867234261121364787841005 2200212847920511795440377)
        ·
          refine ⟨1650159635940383846580283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2200212847920511795440377 1650159635940383846580283)
          ·
            refine ⟨2475239453910575769870425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650159635940383846580283 2475239453910575769870425)
            ·
              refine ⟨1856429590432931827402819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475239453910575769870425 1856429590432931827402819)
              ·
                refine ⟨2784644385649397741104229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856429590432931827402819 2784644385649397741104229)
                ·
                  refine ⟨522120822309262076457043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2784644385649397741104229 522120822309262076457043)
                  ·
                    refine ⟨783181233463893114685565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522120822309262076457043 783181233463893114685565)
                    ·
                      refine ⟨293692962548959918007087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783181233463893114685565 293692962548959918007087)
                      ·
                        rfl

theorem cell23_571965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_571965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571965 prefixEnd_571965 := by exact prefixLift 571965
  have htrace : WordTrace (prefixWord ++ tailWord_571965) baseStart_571965 baseEnd_571965 := by
    simpa [prefixWord, tailWord_571965, baseEnd_571965] using wordTrace_append hprefix tailTrace_571965
  have hstable : (prefixWord ++ tailWord_571965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571965).length < 2 ^ (prefixWord ++ tailWord_571965).sum := by decide
  have hdescent : baseEnd_571965 < baseStart_571965 := by decide
  rcases family_descends (prefixWord ++ tailWord_571965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571966 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_571966 : Nat := 118140960795 + 571966 * 2 ^ 59
def prefixEnd_571966 : Nat := 4983230072969 + 3 ^ 40 * 571966 * 2
def baseEnd_571966 : Nat := 293693476029614414094583

theorem tailTrace_571966 : CollatzResearch.WordTrace tailWord_571966 prefixEnd_571966 293693476029614414094583 := by
  unfold tailWord_571966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607664230734042607610969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13907542563914893907258501 2607664230734042607610969)
  ·
    refine ⟨1955748173050531955708227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2607664230734042607610969 1955748173050531955708227)
    ·
      refine ⟨2933622259575797933562341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955748173050531955708227 2933622259575797933562341)
      ·
        refine ⟨550054173670462112542939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2933622259575797933562341 550054173670462112542939)
        ·
          refine ⟨825081260505693168814409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550054173670462112542939 825081260505693168814409)
          ·
            refine ⟨618810945379269876610807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825081260505693168814409 618810945379269876610807)
            ·
              refine ⟨928216418068904814916211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618810945379269876610807 928216418068904814916211)
              ·
                refine ⟨1392324627103357222374317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928216418068904814916211 1392324627103357222374317)
                ·
                  refine ⟨522121735163758958390369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1392324627103357222374317 522121735163758958390369)
                  ·
                    refine ⟨391591301372819218792777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522121735163758958390369 391591301372819218792777)
                    ·
                      refine ⟨293693476029614414094583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391591301372819218792777 293693476029614414094583)
                      ·
                        rfl

theorem cell23_571966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_571966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571966 prefixEnd_571966 := by exact prefixLift 571966
  have htrace : WordTrace (prefixWord ++ tailWord_571966) baseStart_571966 baseEnd_571966 := by
    simpa [prefixWord, tailWord_571966, baseEnd_571966] using wordTrace_append hprefix tailTrace_571966
  have hstable : (prefixWord ++ tailWord_571966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571966).length < 2 ^ (prefixWord ++ tailWord_571966).sum := by decide
  have hdescent : baseEnd_571966 < baseStart_571966 := by decide
  rcases family_descends (prefixWord ++ tailWord_571966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571972 : List Nat := [2, 3, 5, 1, 1, 1, 2, 8]
def baseStart_571972 : Nat := 118140960795 + 571972 * 2 ^ 59
def prefixEnd_571972 : Nat := 4983230072969 + 3 ^ 40 * 571972 * 2
def baseEnd_571972 : Nat := 10877650256057088541465

theorem tailTrace_571972 : CollatzResearch.WordTrace tailWord_571972 prefixEnd_571972 10877650256057088541465 := by
  unfold tailWord_571972
  simp only [CollatzResearch.WordTrace]
  refine ⟨10430766341925301942803085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13907688455900402590404113 10430766341925301942803085)
  ·
    refine ⟨3911537378221988228551157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10430766341925301942803085 3911537378221988228551157)
    ·
      refine ⟨366706629208311396426671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3911537378221988228551157 366706629208311396426671)
      ·
        refine ⟨550059943812467094640007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366706629208311396426671 550059943812467094640007)
        ·
          refine ⟨825089915718700641960011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550059943812467094640007 825089915718700641960011)
          ·
            refine ⟨1237634873578050962940017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825089915718700641960011 1237634873578050962940017)
            ·
              refine ⟨928226155183538222205013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237634873578050962940017 928226155183538222205013)
              ·
                refine ⟨10877650256057088541465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 928226155183538222205013 10877650256057088541465)
                ·
                  rfl

theorem cell23_571972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 8].length) (baseStart_571972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571972 prefixEnd_571972 := by exact prefixLift 571972
  have htrace : WordTrace (prefixWord ++ tailWord_571972) baseStart_571972 baseEnd_571972 := by
    simpa [prefixWord, tailWord_571972, baseEnd_571972] using wordTrace_append hprefix tailTrace_571972
  have hstable : (prefixWord ++ tailWord_571972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571972).length < 2 ^ (prefixWord ++ tailWord_571972).sum := by decide
  have hdescent : baseEnd_571972 < baseStart_571972 := by decide
  rcases family_descends (prefixWord ++ tailWord_571972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571982 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_571982 : Nat := 118140960795 + 571982 * 2 ^ 59
def prefixEnd_571982 : Nat := 4983230072969 + 3 ^ 40 * 571982 * 2
def baseEnd_571982 : Nat := 293701691720086351494509

theorem tailTrace_571982 : CollatzResearch.WordTrace tailWord_571982 prefixEnd_571982 293701691720086351494509 := by
  unfold tailWord_571982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607737176726796949183775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13907931609209583728980133 2607737176726796949183775)
  ·
    refine ⟨3911605765090195423775663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2607737176726796949183775 3911605765090195423775663)
    ·
      refine ⟨5867408647635293135663495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911605765090195423775663 5867408647635293135663495)
      ·
        refine ⟨8801112971452939703495243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867408647635293135663495 8801112971452939703495243)
        ·
          refine ⟨13201669457179409555242865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801112971452939703495243 13201669457179409555242865)
          ·
            refine ⟨9901252092884557166432149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13201669457179409555242865 9901252092884557166432149)
            ·
              refine ⟨464121191853963617176507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9901252092884557166432149 464121191853963617176507)
              ·
                refine ⟨696181787780945425764761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464121191853963617176507 696181787780945425764761)
                ·
                  refine ⟨522136340835709069323571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 696181787780945425764761 522136340835709069323571)
                  ·
                    refine ⟨783204511253563603985357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522136340835709069323571 783204511253563603985357)
                    ·
                      refine ⟨293701691720086351494509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783204511253563603985357 293701691720086351494509)
                      ·
                        rfl

theorem cell23_571982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_571982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571982 prefixEnd_571982 := by exact prefixLift 571982
  have htrace : WordTrace (prefixWord ++ tailWord_571982) baseStart_571982 baseEnd_571982 := by
    simpa [prefixWord, tailWord_571982, baseEnd_571982] using wordTrace_append hprefix tailTrace_571982
  have hstable : (prefixWord ++ tailWord_571982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571982).length < 2 ^ (prefixWord ++ tailWord_571982).sum := by decide
  have hdescent : baseEnd_571982 < baseStart_571982 := by decide
  rcases family_descends (prefixWord ++ tailWord_571982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571991 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_571991 : Nat := 118140960795 + 571991 * 2 ^ 59
def prefixEnd_571991 : Nat := 4983230072969 + 3 ^ 40 * 571991 * 2
def baseEnd_571991 : Nat := 293706313045976816281967

theorem tailTrace_571991 : CollatzResearch.WordTrace tailWord_571991 prefixEnd_571991 293706313045976816281967 := by
  unfold tailWord_571991
  simp only [CollatzResearch.WordTrace]
  refine ⟨20862225670781770130547827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13908150447187846753698551 20862225670781770130547827)
  ·
    refine ⟨31293338506172655195821741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20862225670781770130547827 31293338506172655195821741)
    ·
      refine ⟨11735001939814745698433153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31293338506172655195821741 11735001939814745698433153)
      ·
        refine ⟨8801251454861059273824865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11735001939814745698433153 8801251454861059273824865)
        ·
          refine ⟨6600938591145794455368649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8801251454861059273824865 6600938591145794455368649)
          ·
            refine ⟨4950703943359345841526487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6600938591145794455368649 4950703943359345841526487)
            ·
              refine ⟨7426055915039018762289731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950703943359345841526487 7426055915039018762289731)
              ·
                refine ⟨11139083872558528143434597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426055915039018762289731 11139083872558528143434597)
                ·
                  refine ⟨2088578226104724026893987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11139083872558528143434597 2088578226104724026893987)
                  ·
                    refine ⟨3132867339157086040340981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2088578226104724026893987 3132867339157086040340981)
                    ·
                      refine ⟨293706313045976816281967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3132867339157086040340981 293706313045976816281967)
                      ·
                        rfl

theorem cell23_571991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_571991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_571991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_571991 prefixEnd_571991 := by exact prefixLift 571991
  have htrace : WordTrace (prefixWord ++ tailWord_571991) baseStart_571991 baseEnd_571991 := by
    simpa [prefixWord, tailWord_571991, baseEnd_571991] using wordTrace_append hprefix tailTrace_571991
  have hstable : (prefixWord ++ tailWord_571991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571991).length < 2 ^ (prefixWord ++ tailWord_571991).sum := by decide
  have hdescent : baseEnd_571991 < baseStart_571991 := by decide
  rcases family_descends (prefixWord ++ tailWord_571991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572041 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_572041 : Nat := 118140960795 + 572041 * 2 ^ 59
def prefixEnd_572041 : Nat := 4983230072969 + 3 ^ 40 * 572041 * 2
def baseEnd_572041 : Nat := 97910662359567206885579

theorem tailTrace_572041 : CollatzResearch.WordTrace tailWord_572041 prefixEnd_572041 97910662359567206885579 := by
  unfold tailWord_572041
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864049320600628669867977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13909366213733752446578651 20864049320600628669867977)
  ·
    refine ⟨15648036990450471502400983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20864049320600628669867977 15648036990450471502400983)
    ·
      refine ⟨23472055485675707253601475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15648036990450471502400983 23472055485675707253601475)
      ·
        refine ⟨35208083228513560880402213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23472055485675707253601475 35208083228513560880402213)
        ·
          refine ⟨6601515605346292665075415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35208083228513560880402213 6601515605346292665075415)
          ·
            refine ⟨9902273408019438997613123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6601515605346292665075415 9902273408019438997613123)
            ·
              refine ⟨14853410112029158496419685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9902273408019438997613123 14853410112029158496419685)
              ·
                refine ⟨2785014396005467218078691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14853410112029158496419685 2785014396005467218078691)
                ·
                  refine ⟨4177521594008200827118037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785014396005467218078691 4177521594008200827118037)
                  ·
                    refine ⟨97910662359567206885579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4177521594008200827118037 97910662359567206885579)
                    ·
                      rfl

theorem cell23_572041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_572041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572041 prefixEnd_572041 := by exact prefixLift 572041
  have htrace : WordTrace (prefixWord ++ tailWord_572041) baseStart_572041 baseEnd_572041 := by
    simpa [prefixWord, tailWord_572041, baseEnd_572041] using wordTrace_append hprefix tailTrace_572041
  have hstable : (prefixWord ++ tailWord_572041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572041).length < 2 ^ (prefixWord ++ tailWord_572041).sum := by decide
  have hdescent : baseEnd_572041 < baseStart_572041 := by decide
  rcases family_descends (prefixWord ++ tailWord_572041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572062 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_572062 : Nat := 118140960795 + 572062 * 2 ^ 59
def prefixEnd_572062 : Nat := 4983230072969 + 3 ^ 40 * 572062 * 2
def baseEnd_572062 : Nat := 32638085574716226499349

theorem tailTrace_572062 : CollatzResearch.WordTrace tailWord_572062 prefixEnd_572062 32638085574716226499349 := by
  unfold tailWord_572062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608101906690568657047805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13909876835683032837588293 2608101906690568657047805)
  ·
    refine ⟨978038215008963246392927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2608101906690568657047805 978038215008963246392927)
    ·
      refine ⟨1467057322513444869589391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978038215008963246392927 1467057322513444869589391)
      ·
        refine ⟨2200585983770167304384087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467057322513444869589391 2200585983770167304384087)
        ·
          refine ⟨3300878975655250956576131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200585983770167304384087 3300878975655250956576131)
          ·
            refine ⟨4951318463482876434864197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300878975655250956576131 4951318463482876434864197)
            ·
              refine ⟨928372211903039331537037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4951318463482876434864197 928372211903039331537037)
              ·
                refine ⟨348139579463639749326389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928372211903039331537037 348139579463639749326389)
                ·
                  refine ⟨32638085574716226499349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348139579463639749326389 32638085574716226499349)
                  ·
                    rfl

theorem cell23_572062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_572062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572062 prefixEnd_572062 := by exact prefixLift 572062
  have htrace : WordTrace (prefixWord ++ tailWord_572062) baseStart_572062 baseEnd_572062 := by
    simpa [prefixWord, tailWord_572062, baseEnd_572062] using wordTrace_append hprefix tailTrace_572062
  have hstable : (prefixWord ++ tailWord_572062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572062).length < 2 ^ (prefixWord ++ tailWord_572062).sum := by decide
  have hdescent : baseEnd_572062 < baseStart_572062 := by decide
  rcases family_descends (prefixWord ++ tailWord_572062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572095 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 2, 4, 2]
def baseStart_572095 : Nat := 118140960795 + 572095 * 2 ^ 59
def prefixEnd_572095 : Nat := 4983230072969 + 3 ^ 40 * 572095 * 2
def baseEnd_572095 : Nat := 293759715034044409381489

theorem tailTrace_572095 : CollatzResearch.WordTrace tailWord_572095 prefixEnd_572095 293759715034044409381489 := by
  unfold tailWord_572095
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866018862404995892333739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13910679241603330594889159 20866018862404995892333739)
  ·
    refine ⟨31299028293607493838500609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20866018862404995892333739 31299028293607493838500609)
    ·
      refine ⟨23474271220205620378875457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31299028293607493838500609 23474271220205620378875457)
      ·
        refine ⟨17605703415154215284156593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23474271220205620378875457 17605703415154215284156593)
        ·
          refine ⟨13204277561365661463117445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17605703415154215284156593 13204277561365661463117445)
          ·
            refine ⟨2475802042756061524334521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13204277561365661463117445 2475802042756061524334521)
            ·
              refine ⟨1856851532067046143250891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475802042756061524334521 1856851532067046143250891)
              ·
                refine ⟨2785277298100569214876337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856851532067046143250891 2785277298100569214876337)
                ·
                  refine ⟨2088957973575426911157253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2785277298100569214876337 2088957973575426911157253)
                  ·
                    refine ⟨391679620045392545841985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2088957973575426911157253 391679620045392545841985)
                    ·
                      refine ⟨293759715034044409381489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391679620045392545841985 293759715034044409381489)
                      ·
                        rfl

theorem cell23_572095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_572095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572095 prefixEnd_572095 := by exact prefixLift 572095
  have htrace : WordTrace (prefixWord ++ tailWord_572095) baseStart_572095 baseEnd_572095 := by
    simpa [prefixWord, tailWord_572095, baseEnd_572095] using wordTrace_append hprefix tailTrace_572095
  have hstable : (prefixWord ++ tailWord_572095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572095).length < 2 ^ (prefixWord ++ tailWord_572095).sum := by decide
  have hdescent : baseEnd_572095 < baseStart_572095 := by decide
  rcases family_descends (prefixWord ++ tailWord_572095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572101 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 12]
def baseStart_572101 : Nat := 118140960795 + 572101 * 2 ^ 59
def prefixEnd_572101 : Nat := 4983230072969 + 3 ^ 40 * 572101 * 2
def baseEnd_572101 : Nat := 32640310657552376211829

theorem tailTrace_572101 : CollatzResearch.WordTrace tailWord_572101 prefixEnd_572101 32640310657552376211829 := by
  unfold tailWord_572101
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866237700383258917052157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13910825133588839278034771 20866237700383258917052157)
  ·
    refine ⟨7824839137643722093894559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20866237700383258917052157 7824839137643722093894559)
    ·
      refine ⟨11737258706465583140841839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7824839137643722093894559 11737258706465583140841839)
      ·
        refine ⟨17605888059698374711262759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11737258706465583140841839 17605888059698374711262759)
        ·
          refine ⟨26408832089547562066894139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17605888059698374711262759 26408832089547562066894139)
          ·
            refine ⟨39613248134321343100341209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26408832089547562066894139 39613248134321343100341209)
            ·
              refine ⟨29709936100741007325255907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39613248134321343100341209 29709936100741007325255907)
              ·
                refine ⟨44564904151111510987883861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29709936100741007325255907 44564904151111510987883861)
                ·
                  refine ⟨32640310657552376211829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 44564904151111510987883861 32640310657552376211829)
                  ·
                    rfl

theorem cell23_572101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_572101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572101 prefixEnd_572101 := by exact prefixLift 572101
  have htrace : WordTrace (prefixWord ++ tailWord_572101) baseStart_572101 baseEnd_572101 := by
    simpa [prefixWord, tailWord_572101, baseEnd_572101] using wordTrace_append hprefix tailTrace_572101
  have hstable : (prefixWord ++ tailWord_572101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572101).length < 2 ^ (prefixWord ++ tailWord_572101).sum := by decide
  have hdescent : baseEnd_572101 < baseStart_572101 := by decide
  rcases family_descends (prefixWord ++ tailWord_572101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572111 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_572111 : Nat := 118140960795 + 572111 * 2 ^ 59
def prefixEnd_572111 : Nat := 4983230072969 + 3 ^ 40 * 572111 * 2
def baseEnd_572111 : Nat := 293767930724516346781415

theorem tailTrace_572111 : CollatzResearch.WordTrace tailWord_572111 prefixEnd_572111 293767930724516346781415 := by
  unfold tailWord_572111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866602430347030624916187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13911068286898020416610791 20866602430347030624916187)
  ·
    refine ⟨31299903645520545937374281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20866602430347030624916187 31299903645520545937374281)
    ·
      refine ⟨23474927734140409453030711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31299903645520545937374281 23474927734140409453030711)
      ·
        refine ⟨35212391601210614179546067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23474927734140409453030711 35212391601210614179546067)
        ·
          refine ⟨52818587401815921269319101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35212391601210614179546067 52818587401815921269319101)
          ·
            refine ⟨19806970275680970475994663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52818587401815921269319101 19806970275680970475994663)
            ·
              refine ⟨29710455413521455713991995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19806970275680970475994663 29710455413521455713991995)
              ·
                refine ⟨44565683120282183570987993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29710455413521455713991995 44565683120282183570987993)
                ·
                  refine ⟨33424262340211637678240995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44565683120282183570987993 33424262340211637678240995)
                  ·
                    refine ⟨50136393510317456517361493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33424262340211637678240995 50136393510317456517361493)
                    ·
                      refine ⟨293767930724516346781415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 50136393510317456517361493 293767930724516346781415)
                      ·
                        rfl

theorem cell23_572111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_572111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572111 prefixEnd_572111 := by exact prefixLift 572111
  have htrace : WordTrace (prefixWord ++ tailWord_572111) baseStart_572111 baseEnd_572111 := by
    simpa [prefixWord, tailWord_572111, baseEnd_572111] using wordTrace_append hprefix tailTrace_572111
  have hstable : (prefixWord ++ tailWord_572111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572111).length < 2 ^ (prefixWord ++ tailWord_572111).sum := by decide
  have hdescent : baseEnd_572111 < baseStart_572111 := by decide
  rcases family_descends (prefixWord ++ tailWord_572111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572196 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_572196 : Nat := 118140960795 + 572196 * 2 ^ 59
def prefixEnd_572196 : Nat := 4983230072969 + 3 ^ 40 * 572196 * 2
def baseEnd_572196 : Nat := 293811576580148514218525

theorem tailTrace_572196 : CollatzResearch.WordTrace tailWord_572196 prefixEnd_572196 293811576580148514218525 := by
  unfold tailWord_572196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434851317519545070880221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13913135090026060094506961 10434851317519545070880221)
  ·
    refine ⟨3913069244069829401580083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10434851317519545070880221 3913069244069829401580083)
    ·
      refine ⟨5869603866104744102370125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3913069244069829401580083 5869603866104744102370125)
      ·
        refine ⟨2201101449789279038388797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5869603866104744102370125 2201101449789279038388797)
        ·
          refine ⟨825413043670979639395799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2201101449789279038388797 825413043670979639395799)
          ·
            refine ⟨1238119565506469459093699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825413043670979639395799 1238119565506469459093699)
            ·
              refine ⟨1857179348259704188640549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238119565506469459093699 1857179348259704188640549)
              ·
                refine ⟨348221127798694535370103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1857179348259704188640549 348221127798694535370103)
                ·
                  refine ⟨522331691698041803055155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348221127798694535370103 522331691698041803055155)
                  ·
                    refine ⟨783497537547062704582733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522331691698041803055155 783497537547062704582733)
                    ·
                      refine ⟨293811576580148514218525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783497537547062704582733 293811576580148514218525)
                      ·
                        rfl

theorem cell23_572196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_572196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572196 prefixEnd_572196 := by exact prefixLift 572196
  have htrace : WordTrace (prefixWord ++ tailWord_572196) baseStart_572196 baseEnd_572196 := by
    simpa [prefixWord, tailWord_572196, baseEnd_572196] using wordTrace_append hprefix tailTrace_572196
  have hstable : (prefixWord ++ tailWord_572196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572196).length < 2 ^ (prefixWord ++ tailWord_572196).sum := by decide
  have hdescent : baseEnd_572196 < baseStart_572196 := by decide
  rcases family_descends (prefixWord ++ tailWord_572196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572215 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_572215 : Nat := 118140960795 + 572215 * 2 ^ 59
def prefixEnd_572215 : Nat := 4983230072969 + 3 ^ 40 * 572215 * 2
def baseEnd_572215 : Nat := 293821332712583939880937

theorem tailTrace_572215 : CollatzResearch.WordTrace tailWord_572215 prefixEnd_572215 293821332712583939880937 := by
  unfold tailWord_572215
  simp only [CollatzResearch.WordTrace]
  refine ⟨20870395621970256386702099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13913597081313504257801399 20870395621970256386702099)
  ·
    refine ⟨31305593432955384580053149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20870395621970256386702099 31305593432955384580053149)
    ·
      refine ⟨11739597537358269217519931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31305593432955384580053149 11739597537358269217519931)
      ·
        refine ⟨17609396306037403826279897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11739597537358269217519931 17609396306037403826279897)
        ·
          refine ⟨13207047229528052869709923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17609396306037403826279897 13207047229528052869709923)
          ·
            refine ⟨19810570844292079304564885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13207047229528052869709923 19810570844292079304564885)
            ·
              refine ⟨928620508326191217401479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19810570844292079304564885 928620508326191217401479)
              ·
                refine ⟨1392930762489286826102219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928620508326191217401479 1392930762489286826102219)
                ·
                  refine ⟨2089396143733930239153329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392930762489286826102219 2089396143733930239153329)
                  ·
                    refine ⟨1567047107800447679364997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089396143733930239153329 1567047107800447679364997)
                    ·
                      refine ⟨293821332712583939880937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1567047107800447679364997 293821332712583939880937)
                      ·
                        rfl

theorem cell23_572215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_572215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572215 prefixEnd_572215 := by exact prefixLift 572215
  have htrace : WordTrace (prefixWord ++ tailWord_572215) baseStart_572215 baseEnd_572215 := by
    simpa [prefixWord, tailWord_572215, baseEnd_572215] using wordTrace_append hprefix tailTrace_572215
  have hstable : (prefixWord ++ tailWord_572215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572215).length < 2 ^ (prefixWord ++ tailWord_572215).sum := by decide
  have hdescent : baseEnd_572215 < baseStart_572215 := by decide
  rcases family_descends (prefixWord ++ tailWord_572215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572230 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_572230 : Nat := 118140960795 + 572230 * 2 ^ 59
def prefixEnd_572230 : Nat := 4983230072969 + 3 ^ 40 * 572230 * 2
def baseEnd_572230 : Nat := 293829034922401381193369

theorem tailTrace_572230 : CollatzResearch.WordTrace tailWord_572230 prefixEnd_572230 293829034922401381193369 := by
  unfold tailWord_572230
  simp only [CollatzResearch.WordTrace]
  refine ⟨652216959903622310890567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13913961811277275965665429 652216959903622310890567)
  ·
    refine ⟨978325439855433466335851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 652216959903622310890567 978325439855433466335851)
    ·
      refine ⟨1467488159783150199503777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978325439855433466335851 1467488159783150199503777)
      ·
        refine ⟨1100616119837362649627833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467488159783150199503777 1100616119837362649627833)
        ·
          refine ⟨825462089878021987220875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100616119837362649627833 825462089878021987220875)
          ·
            refine ⟨1238193134817032980831313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825462089878021987220875 1238193134817032980831313)
            ·
              refine ⟨928644851112774735623485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1238193134817032980831313 928644851112774735623485)
              ·
                refine ⟨348241819167290525858807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928644851112774735623485 348241819167290525858807)
                ·
                  refine ⟨522362728750935788788211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348241819167290525858807 522362728750935788788211)
                  ·
                    refine ⟨783544093126403683182317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522362728750935788788211 783544093126403683182317)
                    ·
                      refine ⟨293829034922401381193369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783544093126403683182317 293829034922401381193369)
                      ·
                        rfl

theorem cell23_572230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_572230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572230 prefixEnd_572230 := by exact prefixLift 572230
  have htrace : WordTrace (prefixWord ++ tailWord_572230) baseStart_572230 baseEnd_572230 := by
    simpa [prefixWord, tailWord_572230, baseEnd_572230] using wordTrace_append hprefix tailTrace_572230
  have hstable : (prefixWord ++ tailWord_572230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572230).length < 2 ^ (prefixWord ++ tailWord_572230).sum := by decide
  have hdescent : baseEnd_572230 < baseStart_572230 := by decide
  rcases family_descends (prefixWord ++ tailWord_572230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572236 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 1, 2, 2]
def baseStart_572236 : Nat := 118140960795 + 572236 * 2 ^ 59
def prefixEnd_572236 : Nat := 4983230072969 + 3 ^ 40 * 572236 * 2
def baseEnd_572236 : Nat := 293832115806328357718341

theorem tailTrace_572236 : CollatzResearch.WordTrace tailWord_572236 prefixEnd_572236 293832115806328357718341 := by
  unfold tailWord_572236
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435580777447088486608281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13914107703262784648811041 10435580777447088486608281)
  ·
    refine ⟨7826685583085316364956211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10435580777447088486608281 7826685583085316364956211)
    ·
      refine ⟨11740028374627974547434317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7826685583085316364956211 11740028374627974547434317)
      ·
        refine ⟨4402510640485490455287869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11740028374627974547434317 4402510640485490455287869)
        ·
          refine ⟨1650941490182058920732951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4402510640485490455287869 1650941490182058920732951)
          ·
            refine ⟨2476412235273088381099427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650941490182058920732951 2476412235273088381099427)
            ·
              refine ⟨3714618352909632571649141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476412235273088381099427 3714618352909632571649141)
              ·
                refine ⟨348245470585278053592107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3714618352909632571649141 348245470585278053592107)
                ·
                  refine ⟨522368205877917080388161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348245470585278053592107 522368205877917080388161)
                  ·
                    refine ⟨391776154408437810291121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522368205877917080388161 391776154408437810291121)
                    ·
                      refine ⟨293832115806328357718341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391776154408437810291121 293832115806328357718341)
                      ·
                        rfl

theorem cell23_572236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_572236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572236 prefixEnd_572236 := by exact prefixLift 572236
  have htrace : WordTrace (prefixWord ++ tailWord_572236) baseStart_572236 baseEnd_572236 := by
    simpa [prefixWord, tailWord_572236, baseEnd_572236] using wordTrace_append hprefix tailTrace_572236
  have hstable : (prefixWord ++ tailWord_572236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572236).length < 2 ^ (prefixWord ++ tailWord_572236).sum := by decide
  have hdescent : baseEnd_572236 < baseStart_572236 := by decide
  rcases family_descends (prefixWord ++ tailWord_572236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572292 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_572292 : Nat := 118140960795 + 572292 * 2 ^ 59
def prefixEnd_572292 : Nat := 4983230072969 + 3 ^ 40 * 572292 * 2
def baseEnd_572292 : Nat := 293860870722980138618083

theorem tailTrace_572292 : CollatzResearch.WordTrace tailWord_572292 prefixEnd_572292 293860870722980138618083 := by
  unfold tailWord_572292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436602021345649268627565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13915469361794199024836753 10436602021345649268627565)
  ·
    refine ⟨3913725758004618475735337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10436602021345649268627565 3913725758004618475735337)
    ·
      refine ⟨2935294318503463856801503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3913725758004618475735337 2935294318503463856801503)
      ·
        refine ⟨4402941477755195785202255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935294318503463856801503 4402941477755195785202255)
        ·
          refine ⟨6604412216632793677803383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402941477755195785202255 6604412216632793677803383)
          ·
            refine ⟨9906618324949190516705075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604412216632793677803383 9906618324949190516705075)
            ·
              refine ⟨14859927487423785775057613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9906618324949190516705075 14859927487423785775057613)
              ·
                refine ⟨5572472807783919665646605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14859927487423785775057613 5572472807783919665646605)
                ·
                  refine ⟨2089677302918969874617477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5572472807783919665646605 2089677302918969874617477)
                  ·
                    refine ⟨391814494297306851490777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2089677302918969874617477 391814494297306851490777)
                    ·
                      refine ⟨293860870722980138618083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391814494297306851490777 293860870722980138618083)
                      ·
                        rfl

theorem cell23_572292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_572292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572292 prefixEnd_572292 := by exact prefixLift 572292
  have htrace : WordTrace (prefixWord ++ tailWord_572292) baseStart_572292 baseEnd_572292 := by
    simpa [prefixWord, tailWord_572292, baseEnd_572292] using wordTrace_append hprefix tailTrace_572292
  have hstable : (prefixWord ++ tailWord_572292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572292).length < 2 ^ (prefixWord ++ tailWord_572292).sum := by decide
  have hdescent : baseEnd_572292 < baseStart_572292 := by decide
  rcases family_descends (prefixWord ++ tailWord_572292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572295 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_572295 : Nat := 118140960795 + 572295 * 2 ^ 59
def prefixEnd_572295 : Nat := 4983230072969 + 3 ^ 40 * 572295 * 2
def baseEnd_572295 : Nat := 293862411164943626880569

theorem tailTrace_572295 : CollatzResearch.WordTrace tailWord_572295 prefixEnd_572295 293862411164943626880569 := by
  unfold tailWord_572295
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873313461680430049614339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13915542307786953366409559 20873313461680430049614339)
  ·
    refine ⟨31309970192520645074421509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20873313461680430049614339 31309970192520645074421509)
    ·
      refine ⟨5870619411097620951454033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31309970192520645074421509 5870619411097620951454033)
      ·
        refine ⟨4402964558323215713590525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5870619411097620951454033 4402964558323215713590525)
        ·
          refine ⟨1651111709371205892596447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4402964558323215713590525 1651111709371205892596447)
          ·
            refine ⟨2476667564056808838894671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651111709371205892596447 2476667564056808838894671)
            ·
              refine ⟨3715001346085213258342007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476667564056808838894671 3715001346085213258342007)
              ·
                refine ⟨5572502019127819887513011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715001346085213258342007 5572502019127819887513011)
                ·
                  refine ⟨8358753028691729831269517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5572502019127819887513011 8358753028691729831269517)
                  ·
                    refine ⟨3134532385759398686726069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8358753028691729831269517 3134532385759398686726069)
                    ·
                      refine ⟨293862411164943626880569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3134532385759398686726069 293862411164943626880569)
                      ·
                        rfl

theorem cell23_572295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_572295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572295 prefixEnd_572295 := by exact prefixLift 572295
  have htrace : WordTrace (prefixWord ++ tailWord_572295) baseStart_572295 baseEnd_572295 := by
    simpa [prefixWord, tailWord_572295, baseEnd_572295] using wordTrace_append hprefix tailTrace_572295
  have hstable : (prefixWord ++ tailWord_572295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572295).length < 2 ^ (prefixWord ++ tailWord_572295).sum := by decide
  have hdescent : baseEnd_572295 < baseStart_572295 := by decide
  rcases family_descends (prefixWord ++ tailWord_572295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572309 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_572309 : Nat := 118140960795 + 572309 * 2 ^ 59
def prefixEnd_572309 : Nat := 4983230072969 + 3 ^ 40 * 572309 * 2
def baseEnd_572309 : Nat := 293869599894106572105505

theorem tailTrace_572309 : CollatzResearch.WordTrace tailWord_572309 prefixEnd_572309 293869599894106572105505 := by
  unfold tailWord_572309
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873824083629710440623981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13915882722419806960415987 20873824083629710440623981)
  ·
    refine ⟨7827684031361141415233993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20873824083629710440623981 7827684031361141415233993)
    ·
      refine ⟨5870763023520856061425495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7827684031361141415233993 5870763023520856061425495)
      ·
        refine ⟨8806144535281284092138243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5870763023520856061425495 8806144535281284092138243)
        ·
          refine ⟨13209216802921926138207365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8806144535281284092138243 13209216802921926138207365)
          ·
            refine ⟨2476728150547861150913881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13209216802921926138207365 2476728150547861150913881)
            ·
              refine ⟨1857546112910895863185411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476728150547861150913881 1857546112910895863185411)
              ·
                refine ⟨2786319169366343794778117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857546112910895863185411 2786319169366343794778117)
                ·
                  refine ⟨522434844256189461520897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2786319169366343794778117 522434844256189461520897)
                  ·
                    refine ⟨391826133192142096140673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 522434844256189461520897 391826133192142096140673)
                    ·
                      refine ⟨293869599894106572105505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391826133192142096140673 293869599894106572105505)
                      ·
                        rfl

theorem cell23_572309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_572309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572309 prefixEnd_572309 := by exact prefixLift 572309
  have htrace : WordTrace (prefixWord ++ tailWord_572309) baseStart_572309 baseEnd_572309 := by
    simpa [prefixWord, tailWord_572309, baseEnd_572309] using wordTrace_append hprefix tailTrace_572309
  have hstable : (prefixWord ++ tailWord_572309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572309).length < 2 ^ (prefixWord ++ tailWord_572309).sum := by decide
  have hdescent : baseEnd_572309 < baseStart_572309 := by decide
  rcases family_descends (prefixWord ++ tailWord_572309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572366 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_572366 : Nat := 118140960795 + 572366 * 2 ^ 59
def prefixEnd_572366 : Nat := 4983230072969 + 3 ^ 40 * 572366 * 2
def baseEnd_572366 : Nat := 32655429810156983232527

theorem tailTrace_572366 : CollatzResearch.WordTrace tailWord_572366 prefixEnd_572366 32655429810156983232527 := by
  unfold tailWord_572366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609487880552901146931119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13917268696282139450299301 2609487880552901146931119)
  ·
    refine ⟨3914231820829351720396679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2609487880552901146931119 3914231820829351720396679)
    ·
      refine ⟨5871347731244027580595019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3914231820829351720396679 5871347731244027580595019)
      ·
        refine ⟨8807021596866041370892529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871347731244027580595019 8807021596866041370892529)
        ·
          refine ⟨6605266197649531028169397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8807021596866041370892529 6605266197649531028169397)
          ·
            refine ⟨619243706029643533890881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6605266197649531028169397 619243706029643533890881)
            ·
              refine ⟨464432779522232650418161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619243706029643533890881 464432779522232650418161)
              ·
                refine ⟨348324584641674487813621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464432779522232650418161 348324584641674487813621)
                ·
                  refine ⟨32655429810156983232527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348324584641674487813621 32655429810156983232527)
                  ·
                    rfl

theorem cell23_572366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_572366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572366 prefixEnd_572366 := by exact prefixLift 572366
  have htrace : WordTrace (prefixWord ++ tailWord_572366) baseStart_572366 baseEnd_572366 := by
    simpa [prefixWord, tailWord_572366, baseEnd_572366] using wordTrace_append hprefix tailTrace_572366
  have hstable : (prefixWord ++ tailWord_572366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572366).length < 2 ^ (prefixWord ++ tailWord_572366).sum := by decide
  have hdescent : baseEnd_572366 < baseStart_572366 := by decide
  rcases family_descends (prefixWord ++ tailWord_572366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572372 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_572372 : Nat := 118140960795 + 572372 * 2 ^ 59
def prefixEnd_572372 : Nat := 4983230072969 + 3 ^ 40 * 572372 * 2
def baseEnd_572372 : Nat := 293901949175339825617715

theorem tailTrace_572372 : CollatzResearch.WordTrace tailWord_572372 prefixEnd_572372 293901949175339825617715 := by
  unfold tailWord_572372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438060941200736100083685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13917414588267648133444913 10438060941200736100083685)
  ·
    refine ⟨1957136426475138018765691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10438060941200736100083685 1957136426475138018765691)
    ·
      refine ⟨2935704639712707028148537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957136426475138018765691 2935704639712707028148537)
      ·
        refine ⟨2201778479784530271111403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935704639712707028148537 2201778479784530271111403)
        ·
          refine ⟨3302667719676795406667105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201778479784530271111403 3302667719676795406667105)
          ·
            refine ⟨2477000789757596555000329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3302667719676795406667105 2477000789757596555000329)
            ·
              refine ⟨1857750592318197416250247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477000789757596555000329 1857750592318197416250247)
              ·
                refine ⟨2786625888477296124375371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857750592318197416250247 2786625888477296124375371)
                ·
                  refine ⟨4179938832715944186563057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786625888477296124375371 4179938832715944186563057)
                  ·
                    refine ⟨3134954124536958139922293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4179938832715944186563057 3134954124536958139922293)
                    ·
                      refine ⟨293901949175339825617715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3134954124536958139922293 293901949175339825617715)
                      ·
                        rfl

theorem cell23_572372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_572372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572372 prefixEnd_572372 := by exact prefixLift 572372
  have htrace : WordTrace (prefixWord ++ tailWord_572372) baseStart_572372 baseEnd_572372 := by
    simpa [prefixWord, tailWord_572372, baseEnd_572372] using wordTrace_append hprefix tailTrace_572372
  have hstable : (prefixWord ++ tailWord_572372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572372).length < 2 ^ (prefixWord ++ tailWord_572372).sum := by decide
  have hdescent : baseEnd_572372 < baseStart_572372 := by decide
  rcases family_descends (prefixWord ++ tailWord_572372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572392 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_572392 : Nat := 118140960795 + 572392 * 2 ^ 59
def prefixEnd_572392 : Nat := 4983230072969 + 3 ^ 40 * 572392 * 2
def baseEnd_572392 : Nat := 97970739596143249122541

theorem tailTrace_572392 : CollatzResearch.WordTrace tailWord_572392 prefixEnd_572392 97970739596143249122541 := by
  unfold tailWord_572392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10438425671164507807947715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13917900894886010410596953 10438425671164507807947715)
  ·
    refine ⟨15657638506746761711921573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10438425671164507807947715 15657638506746761711921573)
    ·
      refine ⟨2935807220015017820985295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15657638506746761711921573 2935807220015017820985295)
      ·
        refine ⟨4403710830022526731477943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935807220015017820985295 4403710830022526731477943)
        ·
          refine ⟨6605566245033790097216915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403710830022526731477943 6605566245033790097216915)
          ·
            refine ⟨9908349367550685145825373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6605566245033790097216915 9908349367550685145825373)
            ·
              refine ⟨3715631012831506929684515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9908349367550685145825373 3715631012831506929684515)
              ·
                refine ⟨5573446519247260394526773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715631012831506929684515 5573446519247260394526773)
                ·
                  refine ⟨522510611179430661986885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5573446519247260394526773 522510611179430661986885)
                  ·
                    refine ⟨97970739596143249122541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522510611179430661986885 97970739596143249122541)
                    ·
                      rfl

theorem cell23_572392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_572392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572392 prefixEnd_572392 := by exact prefixLift 572392
  have htrace : WordTrace (prefixWord ++ tailWord_572392) baseStart_572392 baseEnd_572392 := by
    simpa [prefixWord, tailWord_572392, baseEnd_572392] using wordTrace_append hprefix tailTrace_572392
  have hstable : (prefixWord ++ tailWord_572392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572392).length < 2 ^ (prefixWord ++ tailWord_572392).sum := by decide
  have hdescent : baseEnd_572392 < baseStart_572392 := by decide
  rcases family_descends (prefixWord ++ tailWord_572392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572399 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_572399 : Nat := 118140960795 + 572399 * 2 ^ 59
def prefixEnd_572399 : Nat := 4983230072969 + 3 ^ 40 * 572399 * 2
def baseEnd_572399 : Nat := 293915813153011219980091

theorem tailTrace_572399 : CollatzResearch.WordTrace tailWord_572399 prefixEnd_572399 293915813153011219980091 := by
  unfold tailWord_572399
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877106653303655811400251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13918071102202437207600167 20877106653303655811400251)
  ·
    refine ⟨31315659979955483717100377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20877106653303655811400251 31315659979955483717100377)
    ·
      refine ⟨23486744984966612787825283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31315659979955483717100377 23486744984966612787825283)
      ·
        refine ⟨35230117477449919181737925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23486744984966612787825283 35230117477449919181737925)
        ·
          refine ⟨6605647027021859846575861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35230117477449919181737925 6605647027021859846575861)
          ·
            refine ⟨619279408783299360616487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6605647027021859846575861 619279408783299360616487)
            ·
              refine ⟨928919113174949040924731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619279408783299360616487 928919113174949040924731)
              ·
                refine ⟨1393378669762423561387097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928919113174949040924731 1393378669762423561387097)
                ·
                  refine ⟨1045034002321817671040323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393378669762423561387097 1045034002321817671040323)
                  ·
                    refine ⟨1567551003482726506560485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045034002321817671040323 1567551003482726506560485)
                    ·
                      refine ⟨293915813153011219980091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1567551003482726506560485 293915813153011219980091)
                      ·
                        rfl

theorem cell23_572399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_572399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572399 prefixEnd_572399 := by exact prefixLift 572399
  have htrace : WordTrace (prefixWord ++ tailWord_572399) baseStart_572399 baseEnd_572399 := by
    simpa [prefixWord, tailWord_572399, baseEnd_572399] using wordTrace_append hprefix tailTrace_572399
  have hstable : (prefixWord ++ tailWord_572399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572399).length < 2 ^ (prefixWord ++ tailWord_572399).sum := by decide
  have hdescent : baseEnd_572399 < baseStart_572399 := by decide
  rcases family_descends (prefixWord ++ tailWord_572399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572426 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_572426 : Nat := 118140960795 + 572426 * 2 ^ 59
def prefixEnd_572426 : Nat := 4983230072969 + 3 ^ 40 * 572426 * 2
def baseEnd_572426 : Nat := 97976559043560871447489

theorem tailTrace_572426 : CollatzResearch.WordTrace tailWord_572426 prefixEnd_572426 97976559043560871447489 := by
  unfold tailWord_572426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5219522856051459855658283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13918727616137226281755421 5219522856051459855658283)
  ·
    refine ⟨7829284284077189783487425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5219522856051459855658283 7829284284077189783487425)
    ·
      refine ⟨5871963213057892337615569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7829284284077189783487425 5871963213057892337615569)
      ·
        refine ⟨4403972409793419253211677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5871963213057892337615569 4403972409793419253211677)
        ·
          refine ⟨1651489653672532219954379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403972409793419253211677 1651489653672532219954379)
          ·
            refine ⟨2477234480508798329931569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651489653672532219954379 2477234480508798329931569)
            ·
              refine ⟨1857925860381598747448677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477234480508798329931569 1857925860381598747448677)
              ·
                refine ⟨348361098821549765146627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1857925860381598747448677 348361098821549765146627)
                ·
                  refine ⟨522541648232324647719941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348361098821549765146627 522541648232324647719941)
                  ·
                    refine ⟨97976559043560871447489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522541648232324647719941 97976559043560871447489)
                    ·
                      rfl

theorem cell23_572426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_572426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572426 prefixEnd_572426 := by exact prefixLift 572426
  have htrace : WordTrace (prefixWord ++ tailWord_572426) baseStart_572426 baseEnd_572426 := by
    simpa [prefixWord, tailWord_572426, baseEnd_572426] using wordTrace_append hprefix tailTrace_572426
  have hstable : (prefixWord ++ tailWord_572426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572426).length < 2 ^ (prefixWord ++ tailWord_572426).sum := by decide
  have hdescent : baseEnd_572426 < baseStart_572426 := by decide
  rcases family_descends (prefixWord ++ tailWord_572426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572459 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 2, 3, 2]
def baseStart_572459 : Nat := 118140960795 + 572459 * 2 ^ 59
def prefixEnd_572459 : Nat := 4983230072969 + 3 ^ 40 * 572459 * 2
def baseEnd_572459 : Nat := 293946621992280985229815

theorem tailTrace_572459 : CollatzResearch.WordTrace tailWord_572459 prefixEnd_572459 293946621992280985229815 := by
  unfold tailWord_572459
  simp only [CollatzResearch.WordTrace]
  refine ⟨20879295033086286058584431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13919530022057524039056287 20879295033086286058584431)
  ·
    refine ⟨31318942549629429087876647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20879295033086286058584431 31318942549629429087876647)
    ·
      refine ⟨46978413824444143631814971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31318942549629429087876647 46978413824444143631814971)
      ·
        refine ⟨70467620736666215447722457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46978413824444143631814971 70467620736666215447722457)
        ·
          refine ⟨52850715552499661585791843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70467620736666215447722457 52850715552499661585791843)
          ·
            refine ⟨79276073328749492378687765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52850715552499661585791843 79276073328749492378687765)
            ·
              refine ⟨3716065937285132455250989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79276073328749492378687765 3716065937285132455250989)
              ·
                refine ⟨1393524726481924670719121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3716065937285132455250989 1393524726481924670719121)
                ·
                  refine ⟨1045143544861443503039341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393524726481924670719121 1045143544861443503039341)
                  ·
                    refine ⟨391928829323041313639753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045143544861443503039341 391928829323041313639753)
                    ·
                      refine ⟨293946621992280985229815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391928829323041313639753 293946621992280985229815)
                      ·
                        rfl

theorem cell23_572459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 3, 2].length) (baseStart_572459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572459 prefixEnd_572459 := by exact prefixLift 572459
  have htrace : WordTrace (prefixWord ++ tailWord_572459) baseStart_572459 baseEnd_572459 := by
    simpa [prefixWord, tailWord_572459, baseEnd_572459] using wordTrace_append hprefix tailTrace_572459
  have hstable : (prefixWord ++ tailWord_572459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572459).length < 2 ^ (prefixWord ++ tailWord_572459).sum := by decide
  have hdescent : baseEnd_572459 < baseStart_572459 := by decide
  rcases family_descends (prefixWord ++ tailWord_572459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572476 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_572476 : Nat := 118140960795 + 572476 * 2 ^ 59
def prefixEnd_572476 : Nat := 4983230072969 + 3 ^ 40 * 572476 * 2
def baseEnd_572476 : Nat := 293955351163407418717237

theorem tailTrace_572476 : CollatzResearch.WordTrace tailWord_572476 prefixEnd_572476 293955351163407418717237 := by
  unfold tailWord_572476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439957537012348980976641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13919943382683131974635521 10439957537012348980976641)
  ·
    refine ⟨7829968152759261735732481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10439957537012348980976641 7829968152759261735732481)
    ·
      refine ⟨5872476114569446301799361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7829968152759261735732481 5872476114569446301799361)
      ·
        refine ⟨4404357085927084726349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5872476114569446301799361 4404357085927084726349521)
        ·
          refine ⟨3303267814445313544762141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404357085927084726349521 3303267814445313544762141)
          ·
            refine ⟨1238725430416992579285803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3303267814445313544762141 1238725430416992579285803)
            ·
              refine ⟨1858088145625488868928705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238725430416992579285803 1858088145625488868928705)
              ·
                refine ⟨1393566109219116651696529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858088145625488868928705 1393566109219116651696529)
                ·
                  refine ⟨1045174581914337488772397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393566109219116651696529 1045174581914337488772397)
                  ·
                    refine ⟨391940468217876558289649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045174581914337488772397 391940468217876558289649)
                    ·
                      refine ⟨293955351163407418717237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391940468217876558289649 293955351163407418717237)
                      ·
                        rfl

theorem cell23_572476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_572476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572476 prefixEnd_572476 := by exact prefixLift 572476
  have htrace : WordTrace (prefixWord ++ tailWord_572476) baseStart_572476 baseEnd_572476 := by
    simpa [prefixWord, tailWord_572476, baseEnd_572476] using wordTrace_append hprefix tailTrace_572476
  have hstable : (prefixWord ++ tailWord_572476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572476).length < 2 ^ (prefixWord ++ tailWord_572476).sum := by decide
  have hdescent : baseEnd_572476 < baseStart_572476 := by decide
  rcases family_descends (prefixWord ++ tailWord_572476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572483 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 1, 1, 3]
def baseStart_572483 : Nat := 118140960795 + 572483 * 2 ^ 59
def prefixEnd_572483 : Nat := 4983230072969 + 3 ^ 40 * 572483 * 2
def baseEnd_572483 : Nat := 293958945527988891329705

theorem tailTrace_572483 : CollatzResearch.WordTrace tailWord_572483 prefixEnd_572483 293958945527988891329705 := by
  unfold tailWord_572483
  simp only [CollatzResearch.WordTrace]
  refine ⟨20880170384999338157458103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13920113589999558771638735 20880170384999338157458103)
  ·
    refine ⟨31320255577499007236187155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20880170384999338157458103 31320255577499007236187155)
    ·
      refine ⟨46980383366248510854280733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31320255577499007236187155 46980383366248510854280733)
      ·
        refine ⟨17617643762343191570355275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46980383366248510854280733 17617643762343191570355275)
        ·
          refine ⟨26426465643514787355532913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17617643762343191570355275 26426465643514787355532913)
          ·
            refine ⟨19819849232636090516649685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26426465643514787355532913 19819849232636090516649685)
            ·
              refine ⟨464527716389908371483977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19819849232636090516649685 464527716389908371483977)
              ·
                refine ⟨348395787292431278612983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464527716389908371483977 348395787292431278612983)
                ·
                  refine ⟨522593680938646917919475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348395787292431278612983 522593680938646917919475)
                  ·
                    refine ⟨783890521407970376879213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522593680938646917919475 783890521407970376879213)
                    ·
                      refine ⟨293958945527988891329705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783890521407970376879213 293958945527988891329705)
                      ·
                        rfl

theorem cell23_572483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_572483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572483 prefixEnd_572483 := by exact prefixLift 572483
  have htrace : WordTrace (prefixWord ++ tailWord_572483) baseStart_572483 baseEnd_572483 := by
    simpa [prefixWord, tailWord_572483, baseEnd_572483] using wordTrace_append hprefix tailTrace_572483
  have hstable : (prefixWord ++ tailWord_572483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572483).length < 2 ^ (prefixWord ++ tailWord_572483).sum := by decide
  have hdescent : baseEnd_572483 < baseStart_572483 := by decide
  rcases family_descends (prefixWord ++ tailWord_572483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572492 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_572492 : Nat := 118140960795 + 572492 * 2 ^ 59
def prefixEnd_572492 : Nat := 4983230072969 + 3 ^ 40 * 572492 * 2
def baseEnd_572492 : Nat := 293963566853879356117163

theorem tailTrace_572492 : CollatzResearch.WordTrace tailWord_572492 prefixEnd_572492 293963566853879356117163 := by
  unfold tailWord_572492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440249320983366347267865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13920332427977821796357153 10440249320983366347267865)
  ·
    refine ⟨7830186990737524760450899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10440249320983366347267865 7830186990737524760450899)
    ·
      refine ⟨11745280486106287140676349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7830186990737524760450899 11745280486106287140676349)
      ·
        refine ⟨4404480182289857677753631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11745280486106287140676349 4404480182289857677753631)
        ·
          refine ⟨6606720273434786516630447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404480182289857677753631 6606720273434786516630447)
          ·
            refine ⟨9910080410152179774945671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6606720273434786516630447 9910080410152179774945671)
            ·
              refine ⟨14865120615228269662418507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9910080410152179774945671 14865120615228269662418507)
              ·
                refine ⟨22297680922842404493627761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14865120615228269662418507 22297680922842404493627761)
                ·
                  refine ⟨16723260692131803370220821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22297680922842404493627761 16723260692131803370220821)
                  ·
                    refine ⟨783902844943678282979101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16723260692131803370220821 783902844943678282979101)
                    ·
                      refine ⟨293963566853879356117163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783902844943678282979101 293963566853879356117163)
                      ·
                        rfl

theorem cell23_572492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_572492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572492 prefixEnd_572492 := by exact prefixLift 572492
  have htrace : WordTrace (prefixWord ++ tailWord_572492) baseStart_572492 baseEnd_572492 := by
    simpa [prefixWord, tailWord_572492, baseEnd_572492] using wordTrace_append hprefix tailTrace_572492
  have hstable : (prefixWord ++ tailWord_572492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572492).length < 2 ^ (prefixWord ++ tailWord_572492).sum := by decide
  have hdescent : baseEnd_572492 < baseStart_572492 := by decide
  rcases family_descends (prefixWord ++ tailWord_572492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572510 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_572510 : Nat := 118140960795 + 572510 * 2 ^ 59
def prefixEnd_572510 : Nat := 4983230072969 + 3 ^ 40 * 572510 * 2
def baseEnd_572510 : Nat := 293972809505660285692081

theorem tailTrace_572510 : CollatzResearch.WordTrace tailWord_572510 prefixEnd_572510 293972809505660285692081 := by
  unfold tailWord_572510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610144394487690221086373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13920770103934347845793989 2610144394487690221086373)
  ·
    refine ⟨489402073966441916453695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2610144394487690221086373 489402073966441916453695)
    ·
      refine ⟨734103110949662874680543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489402073966441916453695 734103110949662874680543)
      ·
        refine ⟨1101154666424494312020815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734103110949662874680543 1101154666424494312020815)
        ·
          refine ⟨1651731999636741468031223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101154666424494312020815 1651731999636741468031223)
          ·
            refine ⟨2477597999455112202046835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651731999636741468031223 2477597999455112202046835)
            ·
              refine ⟨3716396999182668303070253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477597999455112202046835 3716396999182668303070253)
              ·
                refine ⟨1393648874693500613651345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3716396999182668303070253 1393648874693500613651345)
                ·
                  refine ⟨1045236656020125460238509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393648874693500613651345 1045236656020125460238509)
                  ·
                    refine ⟨391963746007547047589441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1045236656020125460238509 391963746007547047589441)
                    ·
                      refine ⟨293972809505660285692081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 391963746007547047589441 293972809505660285692081)
                      ·
                        rfl

theorem cell23_572510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_572510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572510 prefixEnd_572510 := by exact prefixLift 572510
  have htrace : WordTrace (prefixWord ++ tailWord_572510) baseStart_572510 baseEnd_572510 := by
    simpa [prefixWord, tailWord_572510, baseEnd_572510] using wordTrace_append hprefix tailTrace_572510
  have hstable : (prefixWord ++ tailWord_572510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572510).length < 2 ^ (prefixWord ++ tailWord_572510).sum := by decide
  have hdescent : baseEnd_572510 < baseStart_572510 := by decide
  rcases family_descends (prefixWord ++ tailWord_572510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572519 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_572519 : Nat := 118140960795 + 572519 * 2 ^ 59
def prefixEnd_572519 : Nat := 4983230072969 + 3 ^ 40 * 572519 * 2
def baseEnd_572519 : Nat := 293977430831550750479539

theorem tailTrace_572519 : CollatzResearch.WordTrace tailWord_572519 prefixEnd_572519 293977430831550750479539 := by
  unfold tailWord_572519
  simp only [CollatzResearch.WordTrace]
  refine ⟨20881483412868916305768611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13920988941912610870512407 20881483412868916305768611)
  ·
    refine ⟨31322225119303374458652917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20881483412868916305768611 31322225119303374458652917)
    ·
      refine ⟨2936458604934691355498711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31322225119303374458652917 2936458604934691355498711)
      ·
        refine ⟨4404687907402037033248067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936458604934691355498711 4404687907402037033248067)
        ·
          refine ⟨6607031861103055549872101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404687907402037033248067 6607031861103055549872101)
          ·
            refine ⟨1238818473956822915601019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6607031861103055549872101 1238818473956822915601019)
            ·
              refine ⟨1858227710935234373401529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238818473956822915601019 1858227710935234373401529)
              ·
                refine ⟨1393670783201425780051147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858227710935234373401529 1393670783201425780051147)
                ·
                  refine ⟨2090506174802138670076721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393670783201425780051147 2090506174802138670076721)
                  ·
                    refine ⟨1567879631101604002557541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2090506174802138670076721 1567879631101604002557541)
                    ·
                      refine ⟨293977430831550750479539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1567879631101604002557541 293977430831550750479539)
                      ·
                        rfl

theorem cell23_572519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_572519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572519 prefixEnd_572519 := by exact prefixLift 572519
  have htrace : WordTrace (prefixWord ++ tailWord_572519) baseStart_572519 baseEnd_572519 := by
    simpa [prefixWord, tailWord_572519, baseEnd_572519] using wordTrace_append hprefix tailTrace_572519
  have hstable : (prefixWord ++ tailWord_572519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572519).length < 2 ^ (prefixWord ++ tailWord_572519).sum := by decide
  have hdescent : baseEnd_572519 < baseStart_572519 := by decide
  rcases family_descends (prefixWord ++ tailWord_572519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572526 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_572526 : Nat := 118140960795 + 572526 * 2 ^ 59
def prefixEnd_572526 : Nat := 4983230072969 + 3 ^ 40 * 572526 * 2
def baseEnd_572526 : Nat := 293981025196132223092007

theorem tailTrace_572526 : CollatzResearch.WordTrace tailWord_572526 prefixEnd_572526 293981025196132223092007 := by
  unfold tailWord_572526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610217340480444562659179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13921159149229037667515621 2610217340480444562659179)
  ·
    refine ⟨3915326010720666843988769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610217340480444562659179 3915326010720666843988769)
    ·
      refine ⟨2936494508040500132991577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3915326010720666843988769 2936494508040500132991577)
      ·
        refine ⟨2202370881030375099743683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2936494508040500132991577 2202370881030375099743683)
        ·
          refine ⟨3303556321545562649615525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202370881030375099743683 3303556321545562649615525)
          ·
            refine ⟨619416810289792996802911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3303556321545562649615525 619416810289792996802911)
            ·
              refine ⟨929125215434689495204367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619416810289792996802911 929125215434689495204367)
              ·
                refine ⟨1393687823152034242806551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929125215434689495204367 1393687823152034242806551)
                ·
                  refine ⟨2090531734728051364209827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393687823152034242806551 2090531734728051364209827)
                  ·
                    refine ⟨3135797602092077046314741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090531734728051364209827 3135797602092077046314741)
                    ·
                      refine ⟨293981025196132223092007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3135797602092077046314741 293981025196132223092007)
                      ·
                        rfl

theorem cell23_572526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_572526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572526 prefixEnd_572526 := by exact prefixLift 572526
  have htrace : WordTrace (prefixWord ++ tailWord_572526) baseStart_572526 baseEnd_572526 := by
    simpa [prefixWord, tailWord_572526, baseEnd_572526] using wordTrace_append hprefix tailTrace_572526
  have hstable : (prefixWord ++ tailWord_572526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572526).length < 2 ^ (prefixWord ++ tailWord_572526).sum := by decide
  have hdescent : baseEnd_572526 < baseStart_572526 := by decide
  rcases family_descends (prefixWord ++ tailWord_572526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572539 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 3]
def baseStart_572539 : Nat := 118140960795 + 572539 * 2 ^ 59
def prefixEnd_572539 : Nat := 4983230072969 + 3 ^ 40 * 572539 * 2
def baseEnd_572539 : Nat := 293987700444640672229447

theorem tailTrace_572539 : CollatzResearch.WordTrace tailWord_572539 prefixEnd_572539 293987700444640672229447 := by
  unfold tailWord_572539
  simp only [CollatzResearch.WordTrace]
  refine ⟨20882212872796459721496671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13921475248530973147664447 20882212872796459721496671)
  ·
    refine ⟨31323319309194689582245007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20882212872796459721496671 31323319309194689582245007)
    ·
      refine ⟨46984978963792034373367511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31323319309194689582245007 46984978963792034373367511)
      ·
        refine ⟨70477468445688051560051267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46984978963792034373367511 70477468445688051560051267)
        ·
          refine ⟨105716202668532077340076901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70477468445688051560051267 105716202668532077340076901)
          ·
            refine ⟨19821788000349764501264419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105716202668532077340076901 19821788000349764501264419)
            ·
              refine ⟨29732682000524646751896629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19821788000349764501264419 29732682000524646751896629)
              ·
                refine ⟨2787438937549185632990309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29732682000524646751896629 2787438937549185632990309)
                ·
                  refine ⟨522644800790472306185683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2787438937549185632990309 522644800790472306185683)
                  ·
                    refine ⟨783967201185708459278525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522644800790472306185683 783967201185708459278525)
                    ·
                      refine ⟨293987700444640672229447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 783967201185708459278525 293987700444640672229447)
                      ·
                        rfl

theorem cell23_572539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 1, 3].length) (baseStart_572539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572539 prefixEnd_572539 := by exact prefixLift 572539
  have htrace : WordTrace (prefixWord ++ tailWord_572539) baseStart_572539 baseEnd_572539 := by
    simpa [prefixWord, tailWord_572539, baseEnd_572539] using wordTrace_append hprefix tailTrace_572539
  have hstable : (prefixWord ++ tailWord_572539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572539).length < 2 ^ (prefixWord ++ tailWord_572539).sum := by decide
  have hdescent : baseEnd_572539 < baseStart_572539 := by decide
  rcases family_descends (prefixWord ++ tailWord_572539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572592 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_572592 : Nat := 118140960795 + 572592 * 2 ^ 59
def prefixEnd_572592 : Nat := 4983230072969 + 3 ^ 40 * 572592 * 2
def baseEnd_572592 : Nat := 294014914919328964866703

theorem tailTrace_572592 : CollatzResearch.WordTrace tailWord_572592 prefixEnd_572592 294014914919328964866703 := by
  unfold tailWord_572592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10442072970802224886588015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13922763961069633182117353 10442072970802224886588015)
  ·
    refine ⟨15663109456203337329882023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10442072970802224886588015 15663109456203337329882023)
    ·
      refine ⟨23494664184305005994823035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15663109456203337329882023 23494664184305005994823035)
      ·
        refine ⟨35241996276457508992234553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23494664184305005994823035 35241996276457508992234553)
        ·
          refine ⟨26431497207343131744175915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35241996276457508992234553 26431497207343131744175915)
          ·
            refine ⟨39647245811014697616263873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26431497207343131744175915 39647245811014697616263873)
            ·
              refine ⟨29735434358261023212197905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39647245811014697616263873 29735434358261023212197905)
              ·
                refine ⟨22301575768695767409148429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29735434358261023212197905 22301575768695767409148429)
                ·
                  refine ⟨8363090913260912778430661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22301575768695767409148429 8363090913260912778430661)
                  ·
                    refine ⟨1568079546236421145955749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8363090913260912778430661 1568079546236421145955749)
                    ·
                      refine ⟨294014914919328964866703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1568079546236421145955749 294014914919328964866703)
                      ·
                        rfl

theorem cell23_572592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_572592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572592 prefixEnd_572592 := by exact prefixLift 572592
  have htrace : WordTrace (prefixWord ++ tailWord_572592) baseStart_572592 baseEnd_572592 := by
    simpa [prefixWord, tailWord_572592, baseEnd_572592] using wordTrace_append hprefix tailTrace_572592
  have hstable : (prefixWord ++ tailWord_572592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572592).length < 2 ^ (prefixWord ++ tailWord_572592).sum := by decide
  have hdescent : baseEnd_572592 < baseStart_572592 := by decide
  rcases family_descends (prefixWord ++ tailWord_572592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572659 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5]
def baseStart_572659 : Nat := 118140960795 + 572659 * 2 ^ 59
def prefixEnd_572659 : Nat := 4983230072969 + 3 ^ 40 * 572659 * 2
def baseEnd_572659 : Nat := 294049318123180202728895

theorem tailTrace_572659 : CollatzResearch.WordTrace tailWord_572659 prefixEnd_572659 294049318123180202728895 := by
  unfold tailWord_572659
  simp only [CollatzResearch.WordTrace]
  refine ⟨20886589632361720215865031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13924393088241146810576687 20886589632361720215865031)
  ·
    refine ⟨31329884448542580323797547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20886589632361720215865031 31329884448542580323797547)
    ·
      refine ⟨46994826672813870485696321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31329884448542580323797547 46994826672813870485696321)
      ·
        refine ⟨35246120004610402864272241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46994826672813870485696321 35246120004610402864272241)
        ·
          refine ⟨26434590003457802148204181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35246120004610402864272241 26434590003457802148204181)
          ·
            refine ⟨1239121406412084475697071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26434590003457802148204181 1239121406412084475697071)
            ·
              refine ⟨1858682109618126713545607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239121406412084475697071 1858682109618126713545607)
              ·
                refine ⟨2788023164427190070318411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858682109618126713545607 2788023164427190070318411)
                ·
                  refine ⟨4182034746640785105477617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788023164427190070318411 4182034746640785105477617)
                  ·
                    refine ⟨3136526059980588829108213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182034746640785105477617 3136526059980588829108213)
                    ·
                      refine ⟨294049318123180202728895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3136526059980588829108213 294049318123180202728895)
                      ·
                        rfl

theorem cell23_572659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_572659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572659 prefixEnd_572659 := by exact prefixLift 572659
  have htrace : WordTrace (prefixWord ++ tailWord_572659) baseStart_572659 baseEnd_572659 := by
    simpa [prefixWord, tailWord_572659, baseEnd_572659] using wordTrace_append hprefix tailTrace_572659
  have hstable : (prefixWord ++ tailWord_572659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572659).length < 2 ^ (prefixWord ++ tailWord_572659).sum := by decide
  have hdescent : baseEnd_572659 < baseStart_572659 := by decide
  rcases family_descends (prefixWord ++ tailWord_572659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572686 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_572686 : Nat := 118140960795 + 572686 * 2 ^ 59
def prefixEnd_572686 : Nat := 4983230072969 + 3 ^ 40 * 572686 * 2
def baseEnd_572686 : Nat := 294063182100851597091271

theorem tailTrace_572686 : CollatzResearch.WordTrace tailWord_572686 prefixEnd_572686 294063182100851597091271 := by
  unfold tailWord_572686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610946800407987978387239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13925049602175935884731941 2610946800407987978387239)
  ·
    refine ⟨3916420200611981967580859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610946800407987978387239 3916420200611981967580859)
    ·
      refine ⟨5874630300917972951371289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3916420200611981967580859 5874630300917972951371289)
      ·
        refine ⟨4405972725688479713528467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5874630300917972951371289 4405972725688479713528467)
        ·
          refine ⟨6608959088532719570292701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405972725688479713528467 6608959088532719570292701)
          ·
            refine ⟨2478359658199769838859763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6608959088532719570292701 2478359658199769838859763)
            ·
              refine ⟨3717539487299654758289645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478359658199769838859763 3717539487299654758289645)
              ·
                refine ⟨1394077307737370534358617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3717539487299654758289645 1394077307737370534358617)
                ·
                  refine ⟨1045557980803027900768963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394077307737370534358617 1045557980803027900768963)
                  ·
                    refine ⟨1568336971204541851153445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045557980803027900768963 1568336971204541851153445)
                    ·
                      refine ⟨294063182100851597091271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1568336971204541851153445 294063182100851597091271)
                      ·
                        rfl

theorem cell23_572686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_572686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572686 prefixEnd_572686 := by exact prefixLift 572686
  have htrace : WordTrace (prefixWord ++ tailWord_572686) baseStart_572686 baseEnd_572686 := by
    simpa [prefixWord, tailWord_572686, baseEnd_572686] using wordTrace_append hprefix tailTrace_572686
  have hstable : (prefixWord ++ tailWord_572686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572686).length < 2 ^ (prefixWord ++ tailWord_572686).sum := by decide
  have hdescent : baseEnd_572686 < baseStart_572686 := by decide
  rcases family_descends (prefixWord ++ tailWord_572686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572719 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_572719 : Nat := 118140960795 + 572719 * 2 ^ 59
def prefixEnd_572719 : Nat := 4983230072969 + 3 ^ 40 * 572719 * 2
def baseEnd_572719 : Nat := 294080126962449967978619

theorem tailTrace_572719 : CollatzResearch.WordTrace tailWord_572719 prefixEnd_572719 294080126962449967978619 := by
  unfold tailWord_572719
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888778012144350463049211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13925852008096233642032807 20888778012144350463049211)
  ·
    refine ⟨31333167018216525694573817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20888778012144350463049211 31333167018216525694573817)
    ·
      refine ⟨23499875263662394270930363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31333167018216525694573817 23499875263662394270930363)
      ·
        refine ⟨35249812895493591406395545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23499875263662394270930363 35249812895493591406395545)
        ·
          refine ⟨26437359671620193554796659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35249812895493591406395545 26437359671620193554796659)
          ·
            refine ⟨39656039507430290332194989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26437359671620193554796659 39656039507430290332194989)
            ·
              refine ⟨14871014815286358874573121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39656039507430290332194989 14871014815286358874573121)
              ·
                refine ⟨11153261111464769155929841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14871014815286358874573121 11153261111464769155929841)
                ·
                  refine ⟨8364945833598576866947381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11153261111464769155929841 8364945833598576866947381)
                  ·
                    refine ⟨784213671899866581276317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8364945833598576866947381 784213671899866581276317)
                    ·
                      refine ⟨294080126962449967978619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 784213671899866581276317 294080126962449967978619)
                      ·
                        rfl

theorem cell23_572719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_572719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572719 prefixEnd_572719 := by exact prefixLift 572719
  have htrace : WordTrace (prefixWord ++ tailWord_572719) baseStart_572719 baseEnd_572719 := by
    simpa [prefixWord, tailWord_572719, baseEnd_572719] using wordTrace_append hprefix tailTrace_572719
  have hstable : (prefixWord ++ tailWord_572719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572719).length < 2 ^ (prefixWord ++ tailWord_572719).sum := by decide
  have hdescent : baseEnd_572719 < baseStart_572719 := by decide
  rcases family_descends (prefixWord ++ tailWord_572719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572740 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_572740 : Nat := 118140960795 + 572740 * 2 ^ 59
def prefixEnd_572740 : Nat := 4983230072969 + 3 ^ 40 * 572740 * 2
def baseEnd_572740 : Nat := 294090910056194385816023

theorem tailTrace_572740 : CollatzResearch.WordTrace tailWord_572740 prefixEnd_572740 294090910056194385816023 := by
  unfold tailWord_572740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444771972534135524781837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13926362630045514033042449 10444771972534135524781837)
  ·
    refine ⟨3916789489700300821793189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10444771972534135524781837 3916789489700300821793189)
    ·
      refine ⟨734398029318806404086223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3916789489700300821793189 734398029318806404086223)
      ·
        refine ⟨1101597043978209606129335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734398029318806404086223 1101597043978209606129335)
        ·
          refine ⟨1652395565967314409194003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101597043978209606129335 1652395565967314409194003)
          ·
            refine ⟨2478593348950971613791005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652395565967314409194003 2478593348950971613791005)
            ·
              refine ⟨929472505856614355171627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478593348950971613791005 929472505856614355171627)
              ·
                refine ⟨1394208758784921532757441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929472505856614355171627 1394208758784921532757441)
                ·
                  refine ⟨1045656569088691149568081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394208758784921532757441 1045656569088691149568081)
                  ·
                    refine ⟨784242426816518362176061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1045656569088691149568081 784242426816518362176061)
                    ·
                      refine ⟨294090910056194385816023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 784242426816518362176061 294090910056194385816023)
                      ·
                        rfl

theorem cell23_572740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_572740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572740 prefixEnd_572740 := by exact prefixLift 572740
  have htrace : WordTrace (prefixWord ++ tailWord_572740) baseStart_572740 baseEnd_572740 := by
    simpa [prefixWord, tailWord_572740, baseEnd_572740] using wordTrace_append hprefix tailTrace_572740
  have hstable : (prefixWord ++ tailWord_572740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572740).length < 2 ^ (prefixWord ++ tailWord_572740).sum := by decide
  have hdescent : baseEnd_572740 < baseStart_572740 := by decide
  rcases family_descends (prefixWord ++ tailWord_572740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572769 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_572769 : Nat := 118140960795 + 572769 * 2 ^ 59
def prefixEnd_572769 : Nat := 4983230072969 + 3 ^ 40 * 572769 * 2
def baseEnd_572769 : Nat := 98035266998391590784463

theorem tailTrace_572769 : CollatzResearch.WordTrace tailWord_572769 prefixEnd_572769 98035266998391590784463 := by
  unfold tailWord_572769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20890601661963209002369361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13927067774642139334912907 20890601661963209002369361)
  ·
    refine ⟨15667951246472406751777021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20890601661963209002369361 15667951246472406751777021)
    ·
      refine ⟨5875481717427152531916383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15667951246472406751777021 5875481717427152531916383)
      ·
        refine ⟨8813222576140728797874575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875481717427152531916383 8813222576140728797874575)
        ·
          refine ⟨13219833864211093196811863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8813222576140728797874575 13219833864211093196811863)
          ·
            refine ⟨19829750796316639795217795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13219833864211093196811863 19829750796316639795217795)
            ·
              refine ⟨29744626194474959692826693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19829750796316639795217795 29744626194474959692826693)
              ·
                refine ⟨5577117411464054942405005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29744626194474959692826693 5577117411464054942405005)
                ·
                  refine ⟨2091419029299020603401877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5577117411464054942405005 2091419029299020603401877)
                  ·
                    refine ⟨98035266998391590784463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2091419029299020603401877 98035266998391590784463)
                    ·
                      rfl

theorem cell23_572769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_572769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572769 prefixEnd_572769 := by exact prefixLift 572769
  have htrace : WordTrace (prefixWord ++ tailWord_572769) baseStart_572769 baseEnd_572769 := by
    simpa [prefixWord, tailWord_572769, baseEnd_572769] using wordTrace_append hprefix tailTrace_572769
  have hstable : (prefixWord ++ tailWord_572769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572769).length < 2 ^ (prefixWord ++ tailWord_572769).sum := by decide
  have hdescent : baseEnd_572769 < baseStart_572769 := by decide
  rcases family_descends (prefixWord ++ tailWord_572769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572770 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_572770 : Nat := 118140960795 + 572770 * 2 ^ 59
def prefixEnd_572770 : Nat := 4983230072969 + 3 ^ 40 * 572770 * 2
def baseEnd_572770 : Nat := 294106314475829268440885

theorem tailTrace_572770 : CollatzResearch.WordTrace tailWord_572770 prefixEnd_572770 294106314475829268440885 := by
  unfold tailWord_572770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222659533739896543288941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13927092089973057448770509 5222659533739896543288941)
  ·
    refine ⟨1958497325152461203733353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5222659533739896543288941 1958497325152461203733353)
    ·
      refine ⟨1468872993864345902800015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1958497325152461203733353 1468872993864345902800015)
      ·
        refine ⟨2203309490796518854200023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468872993864345902800015 2203309490796518854200023)
        ·
          refine ⟨3304964236194778281300035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203309490796518854200023 3304964236194778281300035)
          ·
            refine ⟨4957446354292167421950053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304964236194778281300035 4957446354292167421950053)
            ·
              refine ⟨929521191429781391615635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4957446354292167421950053 929521191429781391615635)
              ·
                refine ⟨1394281787144672087423453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929521191429781391615635 1394281787144672087423453)
                ·
                  refine ⟨522855670179252032783795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1394281787144672087423453 522855670179252032783795)
                  ·
                    refine ⟨784283505268878049175693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 522855670179252032783795 784283505268878049175693)
                    ·
                      refine ⟨294106314475829268440885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 784283505268878049175693 294106314475829268440885)
                      ·
                        rfl

theorem cell23_572770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_572770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572770 prefixEnd_572770 := by exact prefixLift 572770
  have htrace : WordTrace (prefixWord ++ tailWord_572770) baseStart_572770 baseEnd_572770 := by
    simpa [prefixWord, tailWord_572770, baseEnd_572770] using wordTrace_append hprefix tailTrace_572770
  have hstable : (prefixWord ++ tailWord_572770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572770).length < 2 ^ (prefixWord ++ tailWord_572770).sum := by decide
  have hdescent : baseEnd_572770 < baseStart_572770 := by decide
  rcases family_descends (prefixWord ++ tailWord_572770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572860 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_572860 : Nat := 118140960795 + 572860 * 2 ^ 59
def prefixEnd_572860 : Nat := 4983230072969 + 3 ^ 40 * 572860 * 2
def baseEnd_572860 : Nat := 294152527734733916315471

theorem tailTrace_572860 : CollatzResearch.WordTrace tailWord_572860 prefixEnd_572860 294152527734733916315471 := by
  unfold tailWord_572860
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446960352316765771966017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13929280469755687695954689 10446960352316765771966017)
  ·
    refine ⟨7835220264237574328974513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10446960352316765771966017 7835220264237574328974513)
    ·
      refine ⟨5876415198178180746730885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7835220264237574328974513 5876415198178180746730885)
      ·
        refine ⟨1101827849658408890012041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5876415198178180746730885 1101827849658408890012041)
        ·
          refine ⟨826370887243806667509031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101827849658408890012041 826370887243806667509031)
          ·
            refine ⟨1239556330865710001263547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826370887243806667509031 1239556330865710001263547)
            ·
              refine ⟨1859334496298565001895321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239556330865710001263547 1859334496298565001895321)
              ·
                refine ⟨1394500872223923751421491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859334496298565001895321 1394500872223923751421491)
                ·
                  refine ⟨2091751308335885627132237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394500872223923751421491 2091751308335885627132237)
                  ·
                    refine ⟨784406740625957110174589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091751308335885627132237 784406740625957110174589)
                    ·
                      refine ⟨294152527734733916315471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 784406740625957110174589 294152527734733916315471)
                      ·
                        rfl

theorem cell23_572860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_572860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572860 prefixEnd_572860 := by exact prefixLift 572860
  have htrace : WordTrace (prefixWord ++ tailWord_572860) baseStart_572860 baseEnd_572860 := by
    simpa [prefixWord, tailWord_572860, baseEnd_572860] using wordTrace_append hprefix tailTrace_572860
  have hstable : (prefixWord ++ tailWord_572860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572860).length < 2 ^ (prefixWord ++ tailWord_572860).sum := by decide
  have hdescent : baseEnd_572860 < baseStart_572860 := by decide
  rcases family_descends (prefixWord ++ tailWord_572860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572893 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_572893 : Nat := 118140960795 + 572893 * 2 ^ 59
def prefixEnd_572893 : Nat := 4983230072969 + 3 ^ 40 * 572893 * 2
def baseEnd_572893 : Nat := 98056490865444095734273

theorem tailTrace_572893 : CollatzResearch.WordTrace tailWord_572893 prefixEnd_572893 98056490865444095734273 := by
  unfold tailWord_572893
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895124313513978179883333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13930082875675985453255555 20895124313513978179883333)
  ·
    refine ⟨3917835808783870908728125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20895124313513978179883333 3917835808783870908728125)
    ·
      refine ⟨1469188428293951590773047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3917835808783870908728125 1469188428293951590773047)
      ·
        refine ⟨2203782642440927386159571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469188428293951590773047 2203782642440927386159571)
        ·
          refine ⟨3305673963661391079239357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203782642440927386159571 3305673963661391079239357)
          ·
            refine ⟨1239627736373021654714759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3305673963661391079239357 1239627736373021654714759)
            ·
              refine ⟨1859441604559532482072139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239627736373021654714759 1859441604559532482072139)
              ·
                refine ⟨2789162406839298723108209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859441604559532482072139 2789162406839298723108209)
                ·
                  refine ⟨2091871805129474042331157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789162406839298723108209 2091871805129474042331157)
                  ·
                    refine ⟨98056490865444095734273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2091871805129474042331157 98056490865444095734273)
                    ·
                      rfl

theorem cell23_572893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_572893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572893 prefixEnd_572893 := by exact prefixLift 572893
  have htrace : WordTrace (prefixWord ++ tailWord_572893) baseStart_572893 baseEnd_572893 := by
    simpa [prefixWord, tailWord_572893, baseEnd_572893] using wordTrace_append hprefix tailTrace_572893
  have hstable : (prefixWord ++ tailWord_572893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572893).length < 2 ^ (prefixWord ++ tailWord_572893).sum := by decide
  have hdescent : baseEnd_572893 < baseStart_572893 := by decide
  rcases family_descends (prefixWord ++ tailWord_572893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572917 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_572917 : Nat := 118140960795 + 572917 * 2 ^ 59
def prefixEnd_572917 : Nat := 4983230072969 + 3 ^ 40 * 572917 * 2
def baseEnd_572917 : Nat := 294181796132040193302709

theorem tailTrace_572917 : CollatzResearch.WordTrace tailWord_572917 prefixEnd_572917 294181796132040193302709 := by
  unfold tailWord_572917
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895999665427030278757005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13930666443618020185838003 20895999665427030278757005)
  ·
    refine ⟨7835999874535136354533877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20895999665427030278757005 7835999874535136354533877)
    ·
      refine ⟨734624988237669033237551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7835999874535136354533877 734624988237669033237551)
      ·
        refine ⟨1101937482356503549856327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734624988237669033237551 1101937482356503549856327)
        ·
          refine ⟨1652906223534755324784491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101937482356503549856327 1652906223534755324784491)
          ·
            refine ⟨2479359335302132987176737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652906223534755324784491 2479359335302132987176737)
            ·
              refine ⟨1859519501476599740382553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479359335302132987176737 1859519501476599740382553)
              ·
                refine ⟨1394639626107449805286915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859519501476599740382553 1394639626107449805286915)
                ·
                  refine ⟨2091959439161174707930373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394639626107449805286915 2091959439161174707930373)
                  ·
                    refine ⟨392242394842720257736945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2091959439161174707930373 392242394842720257736945)
                    ·
                      refine ⟨294181796132040193302709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392242394842720257736945 294181796132040193302709)
                      ·
                        rfl

theorem cell23_572917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_572917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572917 prefixEnd_572917 := by exact prefixLift 572917
  have htrace : WordTrace (prefixWord ++ tailWord_572917) baseStart_572917 baseEnd_572917 := by
    simpa [prefixWord, tailWord_572917, baseEnd_572917] using wordTrace_append hprefix tailTrace_572917
  have hstable : (prefixWord ++ tailWord_572917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572917).length < 2 ^ (prefixWord ++ tailWord_572917).sum := by decide
  have hdescent : baseEnd_572917 < baseStart_572917 := by decide
  rcases family_descends (prefixWord ++ tailWord_572917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572930 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_572930 : Nat := 118140960795 + 572930 * 2 ^ 59
def prefixEnd_572930 : Nat := 4983230072969 + 3 ^ 40 * 572930 * 2
def baseEnd_572930 : Nat := 294188471380548642440149

theorem tailTrace_572930 : CollatzResearch.WordTrace tailWord_572930 prefixEnd_572930 294188471380548642440149 := by
  unfold tailWord_572930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224118453594983374745061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13930982542919955665986829 5224118453594983374745061)
  ·
    refine ⟨979522210049059382764699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5224118453594983374745061 979522210049059382764699)
    ·
      refine ⟨1469283315073589074147049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979522210049059382764699 1469283315073589074147049)
      ·
        refine ⟨1101962486305191805610287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1469283315073589074147049 1101962486305191805610287)
        ·
          refine ⟨1652943729457787708415431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101962486305191805610287 1652943729457787708415431)
          ·
            refine ⟨2479415594186681562623147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652943729457787708415431 2479415594186681562623147)
            ·
              refine ⟨3719123391280022343934721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2479415594186681562623147 3719123391280022343934721)
              ·
                refine ⟨2789342543460016757951041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3719123391280022343934721 2789342543460016757951041)
                ·
                  refine ⟨2092006907595012568463281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789342543460016757951041 2092006907595012568463281)
                  ·
                    refine ⟨1569005180696259426347461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2092006907595012568463281 1569005180696259426347461)
                    ·
                      refine ⟨294188471380548642440149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1569005180696259426347461 294188471380548642440149)
                      ·
                        rfl

theorem cell23_572930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_572930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572930 prefixEnd_572930 := by exact prefixLift 572930
  have htrace : WordTrace (prefixWord ++ tailWord_572930) baseStart_572930 baseEnd_572930 := by
    simpa [prefixWord, tailWord_572930, baseEnd_572930] using wordTrace_append hprefix tailTrace_572930
  have hstable : (prefixWord ++ tailWord_572930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572930).length < 2 ^ (prefixWord ++ tailWord_572930).sum := by decide
  have hdescent : baseEnd_572930 < baseStart_572930 := by decide
  rcases family_descends (prefixWord ++ tailWord_572930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572976 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_572976 : Nat := 118140960795 + 572976 * 2 ^ 59
def prefixEnd_572976 : Nat := 4983230072969 + 3 ^ 40 * 572976 * 2
def baseEnd_572976 : Nat := 294212091490655462464937

theorem tailTrace_572976 : CollatzResearch.WordTrace tailWord_572976 prefixEnd_572976 294212091490655462464937 := by
  unfold tailWord_572976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449075786106641677577391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13932101048142188903436521 10449075786106641677577391)
  ·
    refine ⟨15673613679159962516366087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449075786106641677577391 15673613679159962516366087)
    ·
      refine ⟨23510420518739943774549131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15673613679159962516366087 23510420518739943774549131)
      ·
        refine ⟨35265630778109915661823697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23510420518739943774549131 35265630778109915661823697)
        ·
          refine ⟨26449223083582436746367773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35265630778109915661823697 26449223083582436746367773)
          ·
            refine ⟨9918458656343413779887915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26449223083582436746367773 9918458656343413779887915)
            ·
              refine ⟨14877687984515120669831873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918458656343413779887915 14877687984515120669831873)
              ·
                refine ⟨11158265988386340502373905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14877687984515120669831873 11158265988386340502373905)
                ·
                  refine ⟨8368699491289755376780429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11158265988386340502373905 8368699491289755376780429)
                  ·
                    refine ⟨3138262309233658266292661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8368699491289755376780429 3138262309233658266292661)
                    ·
                      refine ⟨294212091490655462464937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3138262309233658266292661 294212091490655462464937)
                      ·
                        rfl

theorem cell23_572976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_572976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_572976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_572976 prefixEnd_572976 := by exact prefixLift 572976
  have htrace : WordTrace (prefixWord ++ tailWord_572976) baseStart_572976 baseEnd_572976 := by
    simpa [prefixWord, tailWord_572976, baseEnd_572976] using wordTrace_append hprefix tailTrace_572976
  have hstable : (prefixWord ++ tailWord_572976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572976).length < 2 ^ (prefixWord ++ tailWord_572976).sum := by decide
  have hdescent : baseEnd_572976 < baseStart_572976 := by decide
  rcases family_descends (prefixWord ++ tailWord_572976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573050 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2]
def baseStart_573050 : Nat := 118140960795 + 573050 * 2 ^ 59
def prefixEnd_573050 : Nat := 4983230072969 + 3 ^ 40 * 573050 * 2
def baseEnd_573050 : Nat := 294250089059088172939597

theorem tailTrace_573050 : CollatzResearch.WordTrace tailWord_573050 prefixEnd_573050 294250089059088172939597 := by
  unfold tailWord_573050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225212643486298498337151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13933900382630129328899069 5225212643486298498337151)
  ·
    refine ⟨7837818965229447747505727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225212643486298498337151 7837818965229447747505727)
    ·
      refine ⟨11756728447844171621258591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837818965229447747505727 11756728447844171621258591)
      ·
        refine ⟨17635092671766257431887887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11756728447844171621258591 17635092671766257431887887)
        ·
          refine ⟨26452639007649386147831831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17635092671766257431887887 26452639007649386147831831)
          ·
            refine ⟨39678958511474079221747747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26452639007649386147831831 39678958511474079221747747)
            ·
              refine ⟨59518437767211118832621621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39678958511474079221747747 59518437767211118832621621)
              ·
                refine ⟨5579853540676042390558277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59518437767211118832621621 5579853540676042390558277)
                ·
                  refine ⟨1046222538876757948229677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5579853540676042390558277 1046222538876757948229677)
                  ·
                    refine ⟨392333452078784230586129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1046222538876757948229677 392333452078784230586129)
                    ·
                      refine ⟨294250089059088172939597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392333452078784230586129 294250089059088172939597)
                      ·
                        rfl

theorem cell23_573050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2].length) (baseStart_573050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573050 prefixEnd_573050 := by exact prefixLift 573050
  have htrace : WordTrace (prefixWord ++ tailWord_573050) baseStart_573050 baseEnd_573050 := by
    simpa [prefixWord, tailWord_573050, baseEnd_573050] using wordTrace_append hprefix tailTrace_573050
  have hstable : (prefixWord ++ tailWord_573050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573050).length < 2 ^ (prefixWord ++ tailWord_573050).sum := by decide
  have hdescent : baseEnd_573050 < baseStart_573050 := by decide
  rcases family_descends (prefixWord ++ tailWord_573050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573074 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_573074 : Nat := 118140960795 + 573074 * 2 ^ 59
def prefixEnd_573074 : Nat := 4983230072969 + 3 ^ 40 * 573074 * 2
def baseEnd_573074 : Nat := 294262412594796079039487

theorem tailTrace_573074 : CollatzResearch.WordTrace tailWord_573074 prefixEnd_573074 294262412594796079039487 := by
  unfold tailWord_573074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225431481464561523055569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13934483950572164061481517 5225431481464561523055569)
  ·
    refine ⟨3919073611098421142291677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5225431481464561523055569 3919073611098421142291677)
    ·
      refine ⟨1469652604161907928359379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3919073611098421142291677 1469652604161907928359379)
      ·
        refine ⟨2204478906242861892539069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469652604161907928359379 2204478906242861892539069)
        ·
          refine ⟨826679589841073209702151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2204478906242861892539069 826679589841073209702151)
          ·
            refine ⟨1240019384761609814553227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826679589841073209702151 1240019384761609814553227)
            ·
              refine ⟨1860029077142414721829841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240019384761609814553227 1860029077142414721829841)
              ·
                refine ⟨1395021807856811041372381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860029077142414721829841 1395021807856811041372381)
                ·
                  refine ⟨523133177946304140514643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1395021807856811041372381 523133177946304140514643)
                  ·
                    refine ⟨784699766919456210771965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523133177946304140514643 784699766919456210771965)
                    ·
                      refine ⟨294262412594796079039487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 784699766919456210771965 294262412594796079039487)
                      ·
                        rfl

theorem cell23_573074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_573074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573074 prefixEnd_573074 := by exact prefixLift 573074
  have htrace : WordTrace (prefixWord ++ tailWord_573074) baseStart_573074 baseEnd_573074 := by
    simpa [prefixWord, tailWord_573074, baseEnd_573074] using wordTrace_append hprefix tailTrace_573074
  have hstable : (prefixWord ++ tailWord_573074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573074).length < 2 ^ (prefixWord ++ tailWord_573074).sum := by decide
  have hdescent : baseEnd_573074 < baseStart_573074 := by decide
  rcases family_descends (prefixWord ++ tailWord_573074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573080 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_573080 : Nat := 118140960795 + 573080 * 2 ^ 59
def prefixEnd_573080 : Nat := 4983230072969 + 3 ^ 40 * 573080 * 2
def baseEnd_573080 : Nat := 294265493478723055564459

theorem tailTrace_573080 : CollatzResearch.WordTrace tailWord_573080 prefixEnd_573080 294265493478723055564459 := by
  unfold tailWord_573080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450972381918254558470347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13934629842557672744627129 10450972381918254558470347)
  ·
    refine ⟨15676458572877381837705521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10450972381918254558470347 15676458572877381837705521)
    ·
      refine ⟨11757343929658036378279141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15676458572877381837705521 11757343929658036378279141)
      ·
        refine ⟨2204501986810881820927339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11757343929658036378279141 2204501986810881820927339)
        ·
          refine ⟨3306752980216322731391009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204501986810881820927339 3306752980216322731391009)
          ·
            refine ⟨2480064735162242048543257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306752980216322731391009 2480064735162242048543257)
            ·
              refine ⟨1860048551371681536407443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480064735162242048543257 1860048551371681536407443)
              ·
                refine ⟨2790072827057522304611165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860048551371681536407443 2790072827057522304611165)
                ·
                  refine ⟨1046277310146570864229187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2790072827057522304611165 1046277310146570864229187)
                  ·
                    refine ⟨1569415965219856296343781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1046277310146570864229187 1569415965219856296343781)
                    ·
                      refine ⟨294265493478723055564459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1569415965219856296343781 294265493478723055564459)
                      ·
                        rfl

theorem cell23_573080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_573080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573080 prefixEnd_573080 := by exact prefixLift 573080
  have htrace : WordTrace (prefixWord ++ tailWord_573080) baseStart_573080 baseEnd_573080 := by
    simpa [prefixWord, tailWord_573080, baseEnd_573080] using wordTrace_append hprefix tailTrace_573080
  have hstable : (prefixWord ++ tailWord_573080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573080).length < 2 ^ (prefixWord ++ tailWord_573080).sum := by decide
  have hdescent : baseEnd_573080 < baseStart_573080 := by decide
  rcases family_descends (prefixWord ++ tailWord_573080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573114 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2]
def baseStart_573114 : Nat := 118140960795 + 573114 * 2 ^ 59
def prefixEnd_573114 : Nat := 4983230072969 + 3 ^ 40 * 573114 * 2
def baseEnd_573114 : Nat := 294282951820975922539303

theorem tailTrace_573114 : CollatzResearch.WordTrace tailWord_573114 prefixEnd_573114 294282951820975922539303 := by
  unfold tailWord_573114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225796211428333230919599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13935456563808888615785597 5225796211428333230919599)
  ·
    refine ⟨7838694317142499846379399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225796211428333230919599 7838694317142499846379399)
    ·
      refine ⟨11758041475713749769569099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7838694317142499846379399 11758041475713749769569099)
      ·
        refine ⟨17637062213570624654353649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11758041475713749769569099 17637062213570624654353649)
        ·
          refine ⟨13227796660177968490765237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17637062213570624654353649 13227796660177968490765237)
          ·
            refine ⟨1240105936891684546009241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13227796660177968490765237 1240105936891684546009241)
            ·
              refine ⟨930079452668763409506931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240105936891684546009241 930079452668763409506931)
              ·
                refine ⟨1395119179003145114260397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930079452668763409506931 1395119179003145114260397)
                ·
                  refine ⟨523169692126179417847649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1395119179003145114260397 523169692126179417847649)
                  ·
                    refine ⟨392377269094634563385737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523169692126179417847649 392377269094634563385737)
                    ·
                      refine ⟨294282951820975922539303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392377269094634563385737 294282951820975922539303)
                      ·
                        rfl

theorem cell23_573114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2].length) (baseStart_573114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573114 prefixEnd_573114 := by exact prefixLift 573114
  have htrace : WordTrace (prefixWord ++ tailWord_573114) baseStart_573114 baseEnd_573114 := by
    simpa [prefixWord, tailWord_573114, baseEnd_573114] using wordTrace_append hprefix tailTrace_573114
  have hstable : (prefixWord ++ tailWord_573114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573114).length < 2 ^ (prefixWord ++ tailWord_573114).sum := by decide
  have hdescent : baseEnd_573114 < baseStart_573114 := by decide
  rcases family_descends (prefixWord ++ tailWord_573114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573124 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_573124 : Nat := 118140960795 + 573124 * 2 ^ 59
def prefixEnd_573124 : Nat := 4983230072969 + 3 ^ 40 * 573124 * 2
def baseEnd_573124 : Nat := 98096028875840294471419

theorem tailTrace_573124 : CollatzResearch.WordTrace tailWord_573124 prefixEnd_573124 98096028875840294471419 := by
  unfold tailWord_573124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10451774787838552315771213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13935699717118069754361617 10451774787838552315771213)
  ·
    refine ⟨3919415545439457118414205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10451774787838552315771213 3919415545439457118414205)
    ·
      refine ⟨1469780829539796419405327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3919415545439457118414205 1469780829539796419405327)
      ·
        refine ⟨2204671244309694629107991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469780829539796419405327 2204671244309694629107991)
        ·
          refine ⟨3307006866464541943661987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204671244309694629107991 3307006866464541943661987)
          ·
            refine ⟨4960510299696812915492981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307006866464541943661987 4960510299696812915492981)
            ·
              refine ⟨465047840596576210827467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4960510299696812915492981 465047840596576210827467)
              ·
                refine ⟨697571760894864316241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465047840596576210827467 697571760894864316241201)
                ·
                  refine ⟨523178820671148237180901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697571760894864316241201 523178820671148237180901)
                  ·
                    refine ⟨98096028875840294471419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523178820671148237180901 98096028875840294471419)
                    ·
                      rfl

theorem cell23_573124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_573124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573124 prefixEnd_573124 := by exact prefixLift 573124
  have htrace : WordTrace (prefixWord ++ tailWord_573124) baseStart_573124 baseEnd_573124 := by
    simpa [prefixWord, tailWord_573124, baseEnd_573124] using wordTrace_append hprefix tailTrace_573124
  have hstable : (prefixWord ++ tailWord_573124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573124).length < 2 ^ (prefixWord ++ tailWord_573124).sum := by decide
  have hdescent : baseEnd_573124 < baseStart_573124 := by decide
  rcases family_descends (prefixWord ++ tailWord_573124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573142 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_573142 : Nat := 118140960795 + 573142 * 2 ^ 59
def prefixEnd_573142 : Nat := 4983230072969 + 3 ^ 40 * 573142 * 2
def baseEnd_573142 : Nat := 294297329279301812989175

theorem tailTrace_573142 : CollatzResearch.WordTrace tailWord_573142 prefixEnd_573142 294297329279301812989175 := by
  unfold tailWord_573142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306512880600743356606105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13936137393074595803798453 1306512880600743356606105)
  ·
    refine ⟨979884660450557517454579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1306512880600743356606105 979884660450557517454579)
    ·
      refine ⟨1469826990675836276181869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979884660450557517454579 1469826990675836276181869)
      ·
        refine ⟨551185121503438603568201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1469826990675836276181869 551185121503438603568201)
        ·
          refine ⟨413388841127578952676151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551185121503438603568201 413388841127578952676151)
          ·
            refine ⟨620083261691368429014227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413388841127578952676151 620083261691368429014227)
            ·
              refine ⟨930124892537052643521341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620083261691368429014227 930124892537052643521341)
              ·
                refine ⟨348796834701394741320503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930124892537052643521341 348796834701394741320503)
                ·
                  refine ⟨523195252052092111980755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348796834701394741320503 523195252052092111980755)
                  ·
                    refine ⟨784792878078138167971133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523195252052092111980755 784792878078138167971133)
                    ·
                      refine ⟨294297329279301812989175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 784792878078138167971133 294297329279301812989175)
                      ·
                        rfl

theorem cell23_573142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_573142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573142 prefixEnd_573142 := by exact prefixLift 573142
  have htrace : WordTrace (prefixWord ++ tailWord_573142) baseStart_573142 baseEnd_573142 := by
    simpa [prefixWord, tailWord_573142, baseEnd_573142] using wordTrace_append hprefix tailTrace_573142
  have hstable : (prefixWord ++ tailWord_573142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573142).length < 2 ^ (prefixWord ++ tailWord_573142).sum := by decide
  have hdescent : baseEnd_573142 < baseStart_573142 := by decide
  rcases family_descends (prefixWord ++ tailWord_573142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573143 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_573143 : Nat := 118140960795 + 573143 * 2 ^ 59
def prefixEnd_573143 : Nat := 4983230072969 + 3 ^ 40 * 573143 * 2
def baseEnd_573143 : Nat := 294297842759956309076669

theorem tailTrace_573143 : CollatzResearch.WordTrace tailWord_573143 prefixEnd_573143 294297842759956309076669 := by
  unfold tailWord_573143
  simp only [CollatzResearch.WordTrace]
  refine ⟨20904242562608270876484083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13936161708405513917656055 20904242562608270876484083)
  ·
    refine ⟨31356363843912406314726125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20904242562608270876484083 31356363843912406314726125)
    ·
      refine ⟨11758636441467152368022297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31356363843912406314726125 11758636441467152368022297)
      ·
        refine ⟨8818977331100364276016723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11758636441467152368022297 8818977331100364276016723)
        ·
          refine ⟨13228465996650546414025085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8818977331100364276016723 13228465996650546414025085)
          ·
            refine ⟨4960674748743954905259407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13228465996650546414025085 4960674748743954905259407)
            ·
              refine ⟨7441012123115932357889111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960674748743954905259407 7441012123115932357889111)
              ·
                refine ⟨11161518184673898536833667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441012123115932357889111 11161518184673898536833667)
                ·
                  refine ⟨16742277277010847805250501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161518184673898536833667 16742277277010847805250501)
                  ·
                    refine ⟨3139176989439533963484469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16742277277010847805250501 3139176989439533963484469)
                    ·
                      refine ⟨294297842759956309076669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3139176989439533963484469 294297842759956309076669)
                      ·
                        rfl

theorem cell23_573143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_573143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573143 prefixEnd_573143 := by exact prefixLift 573143
  have htrace : WordTrace (prefixWord ++ tailWord_573143) baseStart_573143 baseEnd_573143 := by
    simpa [prefixWord, tailWord_573143, baseEnd_573143] using wordTrace_append hprefix tailTrace_573143
  have hstable : (prefixWord ++ tailWord_573143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573143).length < 2 ^ (prefixWord ++ tailWord_573143).sum := by decide
  have hdescent : baseEnd_573143 < baseStart_573143 := by decide
  rcases family_descends (prefixWord ++ tailWord_573143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573163 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 4, 6]
def baseStart_573163 : Nat := 118140960795 + 573163 * 2 ^ 59
def prefixEnd_573163 : Nat := 4983230072969 + 3 ^ 40 * 573163 * 2
def baseEnd_573163 : Nat := 98102704124348743608859

theorem tailTrace_573163 : CollatzResearch.WordTrace tailWord_573163 prefixEnd_573163 98102704124348743608859 := by
  unfold tailWord_573163
  simp only [CollatzResearch.WordTrace]
  refine ⟨20904972022535814292212143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13936648015023876194808095 20904972022535814292212143)
  ·
    refine ⟨31357458033803721438318215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20904972022535814292212143 31357458033803721438318215)
    ·
      refine ⟨47036187050705582157477323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31357458033803721438318215 47036187050705582157477323)
      ·
        refine ⟨70554280576058373236215985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47036187050705582157477323 70554280576058373236215985)
        ·
          refine ⟨52915710432043779927161989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70554280576058373236215985 52915710432043779927161989)
          ·
            refine ⟨9921695706008208736342873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52915710432043779927161989 9921695706008208736342873)
            ·
              refine ⟨7441271779506156552257155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9921695706008208736342873 7441271779506156552257155)
              ·
                refine ⟨11161907669259234828385733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441271779506156552257155 11161907669259234828385733)
                ·
                  refine ⟨2092857687986106530322325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11161907669259234828385733 2092857687986106530322325)
                  ·
                    refine ⟨98102704124348743608859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2092857687986106530322325 98102704124348743608859)
                    ·
                      rfl

theorem cell23_573163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 6].length) (baseStart_573163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573163 prefixEnd_573163 := by exact prefixLift 573163
  have htrace : WordTrace (prefixWord ++ tailWord_573163) baseStart_573163 baseEnd_573163 := by
    simpa [prefixWord, tailWord_573163, baseEnd_573163] using wordTrace_append hprefix tailTrace_573163
  have hstable : (prefixWord ++ tailWord_573163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573163).length < 2 ^ (prefixWord ++ tailWord_573163).sum := by decide
  have hdescent : baseEnd_573163 < baseStart_573163 := by decide
  rcases family_descends (prefixWord ++ tailWord_573163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573170 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_573170 : Nat := 118140960795 + 573170 * 2 ^ 59
def prefixEnd_573170 : Nat := 4983230072969 + 3 ^ 40 * 573170 * 2
def baseEnd_573170 : Nat := 294311706737627703439045

theorem tailTrace_573170 : CollatzResearch.WordTrace tailWord_573170 prefixEnd_573170 294311706737627703439045 := by
  unfold tailWord_573170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5226306833377613621929241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13936818222340302991811309 5226306833377613621929241)
  ·
    refine ⟨3919730125033210216446931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5226306833377613621929241 3919730125033210216446931)
    ·
      refine ⟨5879595187549815324670397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919730125033210216446931 5879595187549815324670397)
      ·
        refine ⟨2204848195331180746751399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5879595187549815324670397 2204848195331180746751399)
        ·
          refine ⟨3307272292996771120127099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204848195331180746751399 3307272292996771120127099)
          ·
            refine ⟨4960908439495156680190649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307272292996771120127099 4960908439495156680190649)
            ·
              refine ⟨3720681329621367510142987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4960908439495156680190649 3720681329621367510142987)
              ·
                refine ⟨5581021994432051265214481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720681329621367510142987 5581021994432051265214481)
                ·
                  refine ⟨4185766495824038448910861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5581021994432051265214481 4185766495824038448910861)
                  ·
                    refine ⟨1569662435934014418341573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4185766495824038448910861 1569662435934014418341573)
                    ·
                      refine ⟨294311706737627703439045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1569662435934014418341573 294311706737627703439045)
                      ·
                        rfl

theorem cell23_573170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_573170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573170 prefixEnd_573170 := by exact prefixLift 573170
  have htrace : WordTrace (prefixWord ++ tailWord_573170) baseStart_573170 baseEnd_573170 := by
    simpa [prefixWord, tailWord_573170, baseEnd_573170] using wordTrace_append hprefix tailTrace_573170
  have hstable : (prefixWord ++ tailWord_573170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573170).length < 2 ^ (prefixWord ++ tailWord_573170).sum := by decide
  have hdescent : baseEnd_573170 < baseStart_573170 := by decide
  rcases family_descends (prefixWord ++ tailWord_573170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573193 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 9]
def baseStart_573193 : Nat := 118140960795 + 573193 * 2 ^ 59
def prefixEnd_573193 : Nat := 4983230072969 + 3 ^ 40 * 573193 * 2
def baseEnd_573193 : Nat := 32702612976964568161271

theorem tailTrace_573193 : CollatzResearch.WordTrace tailWord_573193 prefixEnd_573193 32702612976964568161271 := by
  unfold tailWord_573193
  simp only [CollatzResearch.WordTrace]
  refine ⟨20906066212427129415804233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13937377474951419610536155 20906066212427129415804233)
  ·
    refine ⟨15679549659320347061853175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20906066212427129415804233 15679549659320347061853175)
    ·
      refine ⟨23519324488980520592779763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15679549659320347061853175 23519324488980520592779763)
      ·
        refine ⟨35278986733470780889169645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23519324488980520592779763 35278986733470780889169645)
        ·
          refine ⟨13229620025051542833438617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35278986733470780889169645 13229620025051542833438617)
          ·
            refine ⟨9922215018788657125078963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13229620025051542833438617 9922215018788657125078963)
            ·
              refine ⟨14883322528182985687618445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9922215018788657125078963 14883322528182985687618445)
              ·
                refine ⟨5581245948068619632856917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14883322528182985687618445 5581245948068619632856917)
                ·
                  refine ⟨32702612976964568161271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5581245948068619632856917 32702612976964568161271)
                  ·
                    rfl

theorem cell23_573193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_573193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573193 prefixEnd_573193 := by exact prefixLift 573193
  have htrace : WordTrace (prefixWord ++ tailWord_573193) baseStart_573193 baseEnd_573193 := by
    simpa [prefixWord, tailWord_573193, baseEnd_573193] using wordTrace_append hprefix tailTrace_573193
  have hstable : (prefixWord ++ tailWord_573193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573193).length < 2 ^ (prefixWord ++ tailWord_573193).sum := by decide
  have hdescent : baseEnd_573193 < baseStart_573193 := by decide
  rcases family_descends (prefixWord ++ tailWord_573193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573203 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7]
def baseStart_573203 : Nat := 118140960795 + 573203 * 2 ^ 59
def prefixEnd_573203 : Nat := 4983230072969 + 3 ^ 40 * 573203 * 2
def baseEnd_573203 : Nat := 294328651599226074326393

theorem tailTrace_573203 : CollatzResearch.WordTrace tailWord_573203 prefixEnd_573203 294328651599226074326393 := by
  unfold tailWord_573203
  simp only [CollatzResearch.WordTrace]
  refine ⟨20906430942390901123668263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13937620628260600749112175 20906430942390901123668263)
  ·
    refine ⟨31359646413586351685502395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20906430942390901123668263 31359646413586351685502395)
    ·
      refine ⟨47039469620379527528253593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31359646413586351685502395 47039469620379527528253593)
      ·
        refine ⟨35279602215284645646190195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47039469620379527528253593 35279602215284645646190195)
        ·
          refine ⟨52919403322926968469285293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35279602215284645646190195 52919403322926968469285293)
          ·
            refine ⟨19844776246097613175981985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52919403322926968469285293 19844776246097613175981985)
            ·
              refine ⟨14883582184573209881986489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19844776246097613175981985 14883582184573209881986489)
              ·
                refine ⟨11162686638429907411489867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883582184573209881986489 11162686638429907411489867)
                ·
                  refine ⟨16744029957644861117234801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162686638429907411489867 16744029957644861117234801)
                  ·
                    refine ⟨12558022468233645837926101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16744029957644861117234801 12558022468233645837926101)
                    ·
                      refine ⟨294328651599226074326393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12558022468233645837926101 294328651599226074326393)
                      ·
                        rfl

theorem cell23_573203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_573203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573203 prefixEnd_573203 := by exact prefixLift 573203
  have htrace : WordTrace (prefixWord ++ tailWord_573203) baseStart_573203 baseEnd_573203 := by
    simpa [prefixWord, tailWord_573203, baseEnd_573203] using wordTrace_append hprefix tailTrace_573203
  have hstable : (prefixWord ++ tailWord_573203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573203).length < 2 ^ (prefixWord ++ tailWord_573203).sum := by decide
  have hdescent : baseEnd_573203 < baseStart_573203 := by decide
  rcases family_descends (prefixWord ++ tailWord_573203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573221 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_573221 : Nat := 118140960795 + 573221 * 2 ^ 59
def prefixEnd_573221 : Nat := 4983230072969 + 3 ^ 40 * 573221 * 2
def baseEnd_573221 : Nat := 294337894251007003901311

theorem tailTrace_573221 : CollatzResearch.WordTrace tailWord_573221 prefixEnd_573221 294337894251007003901311 := by
  unfold tailWord_573221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20907087456325690197823517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13938058304217126798549011 20907087456325690197823517)
  ·
    refine ⟨7840157796122133824183819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20907087456325690197823517 7840157796122133824183819)
    ·
      refine ⟨11760236694183200736275729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7840157796122133824183819 11760236694183200736275729)
      ·
        refine ⟨8820177520637400552206797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11760236694183200736275729 8820177520637400552206797)
        ·
          refine ⟨3307566570239025207077549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8820177520637400552206797 3307566570239025207077549)
          ·
            refine ⟨1240337463839634452654081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3307566570239025207077549 1240337463839634452654081)
            ·
              refine ⟨930253097879725839490561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240337463839634452654081 930253097879725839490561)
              ·
                refine ⟨697689823409794379617921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930253097879725839490561 697689823409794379617921)
                ·
                  refine ⟨523267367557345784713441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697689823409794379617921 523267367557345784713441)
                  ·
                    refine ⟨392450525668009338535081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523267367557345784713441 392450525668009338535081)
                    ·
                      refine ⟨294337894251007003901311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392450525668009338535081 294337894251007003901311)
                      ·
                        rfl

theorem cell23_573221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_573221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573221 prefixEnd_573221 := by exact prefixLift 573221
  have htrace : WordTrace (prefixWord ++ tailWord_573221) baseStart_573221 baseEnd_573221 := by
    simpa [prefixWord, tailWord_573221, baseEnd_573221] using wordTrace_append hprefix tailTrace_573221
  have hstable : (prefixWord ++ tailWord_573221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573221).length < 2 ^ (prefixWord ++ tailWord_573221).sum := by decide
  have hdescent : baseEnd_573221 < baseStart_573221 := by decide
  rcases family_descends (prefixWord ++ tailWord_573221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573238 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_573238 : Nat := 118140960795 + 573238 * 2 ^ 59
def prefixEnd_573238 : Nat := 4983230072969 + 3 ^ 40 * 573238 * 2
def baseEnd_573238 : Nat := 294346623422133437388733

theorem tailTrace_573238 : CollatzResearch.WordTrace tailWord_573238 prefixEnd_573238 294346623422133437388733 := by
  unfold tailWord_573238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306731718579006381324523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13938471664842734734128245 1306731718579006381324523)
  ·
    refine ⟨1960097577868509571986785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306731718579006381324523 1960097577868509571986785)
    ·
      refine ⟨1470073183401382178990089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960097577868509571986785 1470073183401382178990089)
      ·
        refine ⟨1102554887551036634242567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470073183401382178990089 1102554887551036634242567)
        ·
          refine ⟨1653832331326554951363851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102554887551036634242567 1653832331326554951363851)
          ·
            refine ⟨2480748496989832427045777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653832331326554951363851 2480748496989832427045777)
            ·
              refine ⟨1860561372742374320284333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2480748496989832427045777 1860561372742374320284333)
              ·
                refine ⟨697710514778390370106625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1860561372742374320284333 697710514778390370106625)
                ·
                  refine ⟨523282886083792777579969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 697710514778390370106625 523282886083792777579969)
                  ·
                    refine ⟨392462164562844583184977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523282886083792777579969 392462164562844583184977)
                    ·
                      refine ⟨294346623422133437388733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392462164562844583184977 294346623422133437388733)
                      ·
                        rfl

theorem cell23_573238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_573238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573238 prefixEnd_573238 := by exact prefixLift 573238
  have htrace : WordTrace (prefixWord ++ tailWord_573238) baseStart_573238 baseEnd_573238 := by
    simpa [prefixWord, tailWord_573238, baseEnd_573238] using wordTrace_append hprefix tailTrace_573238
  have hstable : (prefixWord ++ tailWord_573238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573238).length < 2 ^ (prefixWord ++ tailWord_573238).sum := by decide
  have hdescent : baseEnd_573238 < baseStart_573238 := by decide
  rcases family_descends (prefixWord ++ tailWord_573238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573261 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 5]
def baseStart_573261 : Nat := 118140960795 + 573261 * 2 ^ 59
def prefixEnd_573261 : Nat := 4983230072969 + 3 ^ 40 * 573261 * 2
def baseEnd_573261 : Nat := 32706492608576316377903

theorem tailTrace_573261 : CollatzResearch.WordTrace tailWord_573261 prefixEnd_573261 32706492608576316377903 := by
  unfold tailWord_573261
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908546376180777029279637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13939030917453851352853091 20908546376180777029279637)
  ·
    refine ⟨980088111383473923247483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20908546376180777029279637 980088111383473923247483)
    ·
      refine ⟨1470132167075210884871225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980088111383473923247483 1470132167075210884871225)
      ·
        refine ⟨1102599125306408163653419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470132167075210884871225 1102599125306408163653419)
        ·
          refine ⟨1653898687959612245480129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102599125306408163653419 1653898687959612245480129)
          ·
            refine ⟨1240424015969709184110097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653898687959612245480129 1240424015969709184110097)
            ·
              refine ⟨930318011977281888082573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240424015969709184110097 930318011977281888082573)
              ·
                refine ⟨348869254491480708030965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930318011977281888082573 348869254491480708030965)
                ·
                  refine ⟨32706492608576316377903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348869254491480708030965 32706492608576316377903)
                  ·
                    rfl

theorem cell23_573261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_573261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573261 prefixEnd_573261 := by exact prefixLift 573261
  have htrace : WordTrace (prefixWord ++ tailWord_573261) baseStart_573261 baseEnd_573261 := by
    simpa [prefixWord, tailWord_573261, baseEnd_573261] using wordTrace_append hprefix tailTrace_573261
  have hstable : (prefixWord ++ tailWord_573261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573261).length < 2 ^ (prefixWord ++ tailWord_573261).sum := by decide
  have hdescent : baseEnd_573261 < baseStart_573261 := by decide
  rcases family_descends (prefixWord ++ tailWord_573261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573338 : List Nat := [3, 1, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_573338 : Nat := 118140960795 + 573338 * 2 ^ 59
def prefixEnd_573338 : Nat := 4983230072969 + 3 ^ 40 * 573338 * 2
def baseEnd_573338 : Nat := 98132657162527682046091

theorem tailTrace_573338 : CollatzResearch.WordTrace tailWord_573338 prefixEnd_573338 98132657162527682046091 := by
  unfold tailWord_573338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227838699225454794958167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13940903197934546119888445 5227838699225454794958167)
  ·
    refine ⟨7841758048838182192437251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227838699225454794958167 7841758048838182192437251)
    ·
      refine ⟨11762637073257273288655877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7841758048838182192437251 11762637073257273288655877)
      ·
        refine ⟨2205494451235738741622977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11762637073257273288655877 2205494451235738741622977)
        ·
          refine ⟨1654120838426804056217233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2205494451235738741622977 1654120838426804056217233)
          ·
            refine ⟨1240590628820103042162925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654120838426804056217233 1240590628820103042162925)
            ·
              refine ⟨465221485807538640811097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1240590628820103042162925 465221485807538640811097)
              ·
                refine ⟨348916114355653980608323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465221485807538640811097 348916114355653980608323)
                ·
                  refine ⟨523374171533480970912485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348916114355653980608323 523374171533480970912485)
                  ·
                    refine ⟨98132657162527682046091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523374171533480970912485 98132657162527682046091)
                    ·
                      rfl

theorem cell23_573338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_573338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573338 prefixEnd_573338 := by exact prefixLift 573338
  have htrace : WordTrace (prefixWord ++ tailWord_573338) baseStart_573338 baseEnd_573338 := by
    simpa [prefixWord, tailWord_573338, baseEnd_573338] using wordTrace_append hprefix tailTrace_573338
  have hstable : (prefixWord ++ tailWord_573338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573338).length < 2 ^ (prefixWord ++ tailWord_573338).sum := by decide
  have hdescent : baseEnd_573338 < baseStart_573338 := by decide
  rcases family_descends (prefixWord ++ tailWord_573338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573351 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 6]
def baseStart_573351 : Nat := 118140960795 + 573351 * 2 ^ 59
def prefixEnd_573351 : Nat := 4983230072969 + 3 ^ 40 * 573351 * 2
def baseEnd_573351 : Nat := 32711627415121277252857

theorem tailTrace_573351 : CollatzResearch.WordTrace tailWord_573351 prefixEnd_573351 32711627415121277252857 := by
  unfold tailWord_573351
  simp only [CollatzResearch.WordTrace]
  refine ⟨20911828945854722400055907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13941219297236481600037271 20911828945854722400055907)
  ·
    refine ⟨31367743418782083600083861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20911828945854722400055907 31367743418782083600083861)
    ·
      refine ⟨1470362972755410168753931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31367743418782083600083861 1470362972755410168753931)
      ·
        refine ⟨2205544459133115253130897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470362972755410168753931 2205544459133115253130897)
        ·
          refine ⟨1654158344349836439848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2205544459133115253130897 1654158344349836439848173)
          ·
            refine ⟨620309379131188664943065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1654158344349836439848173 620309379131188664943065)
            ·
              refine ⟨465232034348391498707299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620309379131188664943065 465232034348391498707299)
              ·
                refine ⟨697848051522587248060949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465232034348391498707299 697848051522587248060949)
                ·
                  refine ⟨32711627415121277252857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 697848051522587248060949 32711627415121277252857)
                  ·
                    rfl

theorem cell23_573351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 6].length) (baseStart_573351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573351 prefixEnd_573351 := by exact prefixLift 573351
  have htrace : WordTrace (prefixWord ++ tailWord_573351) baseStart_573351 baseEnd_573351 := by
    simpa [prefixWord, tailWord_573351, baseEnd_573351] using wordTrace_append hprefix tailTrace_573351
  have hstable : (prefixWord ++ tailWord_573351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573351).length < 2 ^ (prefixWord ++ tailWord_573351).sum := by decide
  have hdescent : baseEnd_573351 < baseStart_573351 := by decide
  rcases family_descends (prefixWord ++ tailWord_573351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573360 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_573360 : Nat := 118140960795 + 573360 * 2 ^ 59
def prefixEnd_573360 : Nat := 4983230072969 + 3 ^ 40 * 573360 * 2
def baseEnd_573360 : Nat := 98136422687327320021057

theorem tailTrace_573360 : CollatzResearch.WordTrace tailWord_573360 prefixEnd_573360 98136422687327320021057 := by
  unfold tailWord_573360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456078601411058468566767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13941438135214744624755689 10456078601411058468566767)
  ·
    refine ⟨15684117902116587702850151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10456078601411058468566767 15684117902116587702850151)
    ·
      refine ⟨23526176853174881554275227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15684117902116587702850151 23526176853174881554275227)
      ·
        refine ⟨35289265279762322331412841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23526176853174881554275227 35289265279762322331412841)
        ·
          refine ⟨26466948959821741748559631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35289265279762322331412841 26466948959821741748559631)
          ·
            refine ⟨39700423439732612622839447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26466948959821741748559631 39700423439732612622839447)
            ·
              refine ⟨59550635159598918934259171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39700423439732612622839447 59550635159598918934259171)
              ·
                refine ⟨89325952739398378401388757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59550635159598918934259171 89325952739398378401388757)
                ·
                  refine ⟨2093577017329649493782549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89325952739398378401388757 2093577017329649493782549)
                  ·
                    refine ⟨98136422687327320021057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2093577017329649493782549 98136422687327320021057)
                    ·
                      rfl

theorem cell23_573360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_573360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573360 prefixEnd_573360 := by exact prefixLift 573360
  have htrace : WordTrace (prefixWord ++ tailWord_573360) baseStart_573360 baseEnd_573360 := by
    simpa [prefixWord, tailWord_573360, baseEnd_573360] using wordTrace_append hprefix tailTrace_573360
  have hstable : (prefixWord ++ tailWord_573360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573360).length < 2 ^ (prefixWord ++ tailWord_573360).sum := by decide
  have hdescent : baseEnd_573360 < baseStart_573360 := by decide
  rcases family_descends (prefixWord ++ tailWord_573360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573407 : List Nat := [1, 1, 2, 3, 4, 1, 3, 8]
def baseStart_573407 : Nat := 118140960795 + 573407 * 2 ^ 59
def prefixEnd_573407 : Nat := 4983230072969 + 3 ^ 40 * 573407 * 2
def baseEnd_573407 : Nat := 10904940801953454673165

theorem tailTrace_573407 : CollatzResearch.WordTrace tailWord_573407 prefixEnd_573407 10904940801953454673165 := by
  unfold tailWord_573407
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913871433651843964094475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13942580955767895976062983 20913871433651843964094475)
  ·
    refine ⟨31370807150477765946141713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20913871433651843964094475 31370807150477765946141713)
    ·
      refine ⟨23528105362858324459606285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31370807150477765946141713 23528105362858324459606285)
      ·
        refine ⟨8823039511071871672352357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23528105362858324459606285 8823039511071871672352357)
        ·
          refine ⟨1654319908325975938566067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8823039511071871672352357 1654319908325975938566067)
          ·
            refine ⟨2481479862488963907849101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654319908325975938566067 2481479862488963907849101)
            ·
              refine ⟨930554948433361465443413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2481479862488963907849101 930554948433361465443413)
              ·
                refine ⟨10904940801953454673165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 930554948433361465443413 10904940801953454673165)
                ·
                  rfl

theorem cell23_573407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 8].length) (baseStart_573407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573407 prefixEnd_573407 := by exact prefixLift 573407
  have htrace : WordTrace (prefixWord ++ tailWord_573407) baseStart_573407 baseEnd_573407 := by
    simpa [prefixWord, tailWord_573407, baseEnd_573407] using wordTrace_append hprefix tailTrace_573407
  have hstable : (prefixWord ++ tailWord_573407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573407).length < 2 ^ (prefixWord ++ tailWord_573407).sum := by decide
  have hdescent : baseEnd_573407 < baseStart_573407 := by decide
  rcases family_descends (prefixWord ++ tailWord_573407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573438 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_573438 : Nat := 118140960795 + 573438 * 2 ^ 59
def prefixEnd_573438 : Nat := 4983230072969 + 3 ^ 40 * 573438 * 2
def baseEnd_573438 : Nat := 294449319553032654887813

theorem tailTrace_573438 : CollatzResearch.WordTrace tailWord_573438 prefixEnd_573438 294449319553032654887813 := by
  unfold tailWord_573438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614375262067442032309121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13943334731026357505648645 2614375262067442032309121)
  ·
    refine ⟨1960781446550581524231841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2614375262067442032309121 1960781446550581524231841)
    ·
      refine ⟨1470586084912936143173881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960781446550581524231841 1470586084912936143173881)
      ·
        refine ⟨1102939563684702107380411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1470586084912936143173881 1102939563684702107380411)
        ·
          refine ⟨1654409345527053161070617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102939563684702107380411 1654409345527053161070617)
          ·
            refine ⟨1240807009145289870802963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654409345527053161070617 1240807009145289870802963)
            ·
              refine ⟨1861210513717934806204445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240807009145289870802963 1861210513717934806204445)
              ·
                refine ⟨697953942644225552326667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1861210513717934806204445 697953942644225552326667)
                ·
                  refine ⟨1046930913966338328490001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697953942644225552326667 1046930913966338328490001)
                  ·
                    refine ⟨785198185474753746367501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046930913966338328490001 785198185474753746367501)
                    ·
                      refine ⟨294449319553032654887813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 785198185474753746367501 294449319553032654887813)
                      ·
                        rfl

theorem cell23_573438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_573438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573438 prefixEnd_573438 := by exact prefixLift 573438
  have htrace : WordTrace (prefixWord ++ tailWord_573438) baseStart_573438 baseEnd_573438 := by
    simpa [prefixWord, tailWord_573438, baseEnd_573438] using wordTrace_append hprefix tailTrace_573438
  have hstable : (prefixWord ++ tailWord_573438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573438).length < 2 ^ (prefixWord ++ tailWord_573438).sum := by decide
  have hdescent : baseEnd_573438 < baseStart_573438 := by decide
  rcases family_descends (prefixWord ++ tailWord_573438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573487 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_573487 : Nat := 118140960795 + 573487 * 2 ^ 59
def prefixEnd_573487 : Nat := 4983230072969 + 3 ^ 40 * 573487 * 2
def baseEnd_573487 : Nat := 294474480105102963175087

theorem tailTrace_573487 : CollatzResearch.WordTrace tailWord_573487 prefixEnd_573487 294474480105102963175087 := by
  unfold tailWord_573487
  simp only [CollatzResearch.WordTrace]
  refine ⟨20916789273362017627006715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13944526182241345084671143 20916789273362017627006715)
  ·
    refine ⟨31375183910043026440510073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20916789273362017627006715 31375183910043026440510073)
    ·
      refine ⟨23531387932532269830382555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31375183910043026440510073 23531387932532269830382555)
      ·
        refine ⟨35297081898798404745573833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23531387932532269830382555 35297081898798404745573833)
        ·
          refine ⟨26472811424098803559180375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35297081898798404745573833 26472811424098803559180375)
          ·
            refine ⟨39709217136148205338770563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26472811424098803559180375 39709217136148205338770563)
            ·
              refine ⟨59563825704222308008155845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39709217136148205338770563 59563825704222308008155845)
              ·
                refine ⟨11168217319541682751529221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59563825704222308008155845 11168217319541682751529221)
                ·
                  refine ⟨2094040747414065515911729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11168217319541682751529221 2094040747414065515911729)
                  ·
                    refine ⟨1570530560560549136933797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2094040747414065515911729 1570530560560549136933797)
                    ·
                      refine ⟨294474480105102963175087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1570530560560549136933797 294474480105102963175087)
                      ·
                        rfl

theorem cell23_573487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_573487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573487 prefixEnd_573487 := by exact prefixLift 573487
  have htrace : WordTrace (prefixWord ++ tailWord_573487) baseStart_573487 baseEnd_573487 := by
    simpa [prefixWord, tailWord_573487, baseEnd_573487] using wordTrace_append hprefix tailTrace_573487
  have hstable : (prefixWord ++ tailWord_573487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573487).length < 2 ^ (prefixWord ++ tailWord_573487).sum := by decide
  have hdescent : baseEnd_573487 < baseStart_573487 := by decide
  rcases family_descends (prefixWord ++ tailWord_573487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573491 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 4, 2, 2]
def baseStart_573491 : Nat := 118140960795 + 573491 * 2 ^ 59
def prefixEnd_573491 : Nat := 4983230072969 + 3 ^ 40 * 573491 * 2
def baseEnd_573491 : Nat := 294476534027720947525069

theorem tailTrace_573491 : CollatzResearch.WordTrace tailWord_573491 prefixEnd_573491 294476534027720947525069 := by
  unfold tailWord_573491
  simp only [CollatzResearch.WordTrace]
  refine ⟨20916935165347526310152327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13944623443565017540101551 20916935165347526310152327)
  ·
    refine ⟨31375402748021289465228491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20916935165347526310152327 31375402748021289465228491)
    ·
      refine ⟨47063104122031934197842737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31375402748021289465228491 47063104122031934197842737)
      ·
        refine ⟨35297328091523950648382053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47063104122031934197842737 35297328091523950648382053)
        ·
          refine ⟨6618249017160740746571635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35297328091523950648382053 6618249017160740746571635)
          ·
            refine ⟨9927373525741111119857453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618249017160740746571635 9927373525741111119857453)
            ·
              refine ⟨3722765072152916669946545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9927373525741111119857453 3722765072152916669946545)
              ·
                refine ⟨2792073804114687502459909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722765072152916669946545 2792073804114687502459909)
                ·
                  refine ⟨523513838271503906711233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2792073804114687502459909 523513838271503906711233)
                  ·
                    refine ⟨392635378703627930033425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523513838271503906711233 392635378703627930033425)
                    ·
                      refine ⟨294476534027720947525069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392635378703627930033425 294476534027720947525069)
                      ·
                        rfl

theorem cell23_573491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 2, 2].length) (baseStart_573491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573491 prefixEnd_573491 := by exact prefixLift 573491
  have htrace : WordTrace (prefixWord ++ tailWord_573491) baseStart_573491 baseEnd_573491 := by
    simpa [prefixWord, tailWord_573491, baseEnd_573491] using wordTrace_append hprefix tailTrace_573491
  have hstable : (prefixWord ++ tailWord_573491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573491).length < 2 ^ (prefixWord ++ tailWord_573491).sum := by decide
  have hdescent : baseEnd_573491 < baseStart_573491 := by decide
  rcases family_descends (prefixWord ++ tailWord_573491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573524 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_573524 : Nat := 118140960795 + 573524 * 2 ^ 59
def prefixEnd_573524 : Nat := 4983230072969 + 3 ^ 40 * 573524 * 2
def baseEnd_573524 : Nat := 294493478889319318412417

theorem tailTrace_573524 : CollatzResearch.WordTrace tailWord_573524 prefixEnd_573524 294493478889319318412417 := by
  unfold tailWord_573524
  simp only [CollatzResearch.WordTrace]
  refine ⟨10459069387113986473051813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13945425849485315297402417 10459069387113986473051813)
  ·
    refine ⟨1961075510083872463697215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10459069387113986473051813 1961075510083872463697215)
    ·
      refine ⟨2941613265125808695545823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1961075510083872463697215 2941613265125808695545823)
      ·
        refine ⟨4412419897688713043318735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941613265125808695545823 4412419897688713043318735)
        ·
          refine ⟨6618629846533069564978103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412419897688713043318735 6618629846533069564978103)
          ·
            refine ⟨9927944769799604347467155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618629846533069564978103 9927944769799604347467155)
            ·
              refine ⟨14891917154699406521200733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9927944769799604347467155 14891917154699406521200733)
              ·
                refine ⟨5584468933012277445450275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14891917154699406521200733 5584468933012277445450275)
                ·
                  refine ⟨8376703399518416168175413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5584468933012277445450275 8376703399518416168175413)
                  ·
                    refine ⟨785315943704851515766445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8376703399518416168175413 785315943704851515766445)
                    ·
                      refine ⟨294493478889319318412417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 785315943704851515766445 294493478889319318412417)
                      ·
                        rfl

theorem cell23_573524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_573524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573524 prefixEnd_573524 := by exact prefixLift 573524
  have htrace : WordTrace (prefixWord ++ tailWord_573524) baseStart_573524 baseEnd_573524 := by
    simpa [prefixWord, tailWord_573524, baseEnd_573524] using wordTrace_append hprefix tailTrace_573524
  have hstable : (prefixWord ++ tailWord_573524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573524).length < 2 ^ (prefixWord ++ tailWord_573524).sum := by decide
  have hdescent : baseEnd_573524 < baseStart_573524 := by decide
  rcases family_descends (prefixWord ++ tailWord_573524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573525 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_573525 : Nat := 118140960795 + 573525 * 2 ^ 59
def prefixEnd_573525 : Nat := 4983230072969 + 3 ^ 40 * 573525 * 2
def baseEnd_573525 : Nat := 294493992369973814499913

theorem tailTrace_573525 : CollatzResearch.WordTrace tailWord_573525 prefixEnd_573525 294493992369973814499913 := by
  unfold tailWord_573525
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918175247224350116890029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13945450164816233411260019 20918175247224350116890029)
  ·
    refine ⟨7844315717709131293833761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20918175247224350116890029 7844315717709131293833761)
    ·
      refine ⟨5883236788281848470375321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7844315717709131293833761 5883236788281848470375321)
      ·
        refine ⟨4412427591211386352781491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5883236788281848470375321 4412427591211386352781491)
        ·
          refine ⟨6618641386817079529172237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412427591211386352781491 6618641386817079529172237)
          ·
            refine ⟨2481990520056404823439589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6618641386817079529172237 2481990520056404823439589)
            ·
              refine ⟨465373222510575904394923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2481990520056404823439589 465373222510575904394923)
              ·
                refine ⟨698059833765863856592385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465373222510575904394923 698059833765863856592385)
                ·
                  refine ⟨523544875324397892444289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698059833765863856592385 523544875324397892444289)
                  ·
                    refine ⟨392658656493298419333217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523544875324397892444289 392658656493298419333217)
                    ·
                      refine ⟨294493992369973814499913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392658656493298419333217 294493992369973814499913)
                      ·
                        rfl

theorem cell23_573525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_573525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573525 prefixEnd_573525 := by exact prefixLift 573525
  have htrace : WordTrace (prefixWord ++ tailWord_573525) baseStart_573525 baseEnd_573525 := by
    simpa [prefixWord, tailWord_573525, baseEnd_573525] using wordTrace_append hprefix tailTrace_573525
  have hstable : (prefixWord ++ tailWord_573525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573525).length < 2 ^ (prefixWord ++ tailWord_573525).sum := by decide
  have hdescent : baseEnd_573525 < baseStart_573525 := by decide
  rcases family_descends (prefixWord ++ tailWord_573525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573527 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 7]
def baseStart_573527 : Nat := 118140960795 + 573527 * 2 ^ 59
def prefixEnd_573527 : Nat := 4983230072969 + 3 ^ 40 * 573527 * 2
def baseEnd_573527 : Nat := 98165006443760935558301

theorem tailTrace_573527 : CollatzResearch.WordTrace tailWord_573527 prefixEnd_573527 98165006443760935558301 := by
  unfold tailWord_573527
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918248193217104458462835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13945498795478069638975223 20918248193217104458462835)
  ·
    refine ⟨31377372289825656687694253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20918248193217104458462835 31377372289825656687694253)
    ·
      refine ⟨11766514608684621257885345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31377372289825656687694253 11766514608684621257885345)
      ·
        refine ⟨8824885956513465943414009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11766514608684621257885345 8824885956513465943414009)
        ·
          refine ⟨6618664467385099457560507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8824885956513465943414009 6618664467385099457560507)
          ·
            refine ⟨9927996701077649186340761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618664467385099457560507 9927996701077649186340761)
            ·
              refine ⟨7445997525808236889755571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9927996701077649186340761 7445997525808236889755571)
              ·
                refine ⟨11168996288712355334633357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445997525808236889755571 11168996288712355334633357)
                ·
                  refine ⟨4188373608267133250487509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11168996288712355334633357 4188373608267133250487509)
                  ·
                    refine ⟨98165006443760935558301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4188373608267133250487509 98165006443760935558301)
                    ·
                      rfl

theorem cell23_573527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_573527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573527 prefixEnd_573527 := by exact prefixLift 573527
  have htrace : WordTrace (prefixWord ++ tailWord_573527) baseStart_573527 baseEnd_573527 := by
    simpa [prefixWord, tailWord_573527, baseEnd_573527] using wordTrace_append hprefix tailTrace_573527
  have hstable : (prefixWord ++ tailWord_573527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573527).length < 2 ^ (prefixWord ++ tailWord_573527).sum := by decide
  have hdescent : baseEnd_573527 < baseStart_573527 := by decide
  rcases family_descends (prefixWord ++ tailWord_573527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573537 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_573537 : Nat := 118140960795 + 573537 * 2 ^ 59
def prefixEnd_573537 : Nat := 4983230072969 + 3 ^ 40 * 573537 * 2
def baseEnd_573537 : Nat := 294500154137827767549857

theorem tailTrace_573537 : CollatzResearch.WordTrace tailWord_573537 prefixEnd_573537 294500154137827767549857 := by
  unfold tailWord_573537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918612923180876166326865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13945741948787250777551243 20918612923180876166326865)
  ·
    refine ⟨15688959692385657124745149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20918612923180876166326865 15688959692385657124745149)
    ·
      refine ⟨5883359884644621421779431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15688959692385657124745149 5883359884644621421779431)
      ·
        refine ⟨8825039826966932132669147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883359884644621421779431 8825039826966932132669147)
        ·
          refine ⟨13237559740450398199003721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8825039826966932132669147 13237559740450398199003721)
          ·
            refine ⟨9928169805337798649252791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13237559740450398199003721 9928169805337798649252791)
            ·
              refine ⟨14892254708006697973879187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9928169805337798649252791 14892254708006697973879187)
              ·
                refine ⟨22338382062010046960818781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14892254708006697973879187 22338382062010046960818781)
                ·
                  refine ⟨8376893273253767610307043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22338382062010046960818781 8376893273253767610307043)
                  ·
                    refine ⟨12565339909880651415460565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8376893273253767610307043 12565339909880651415460565)
                    ·
                      refine ⟨294500154137827767549857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12565339909880651415460565 294500154137827767549857)
                      ·
                        rfl

theorem cell23_573537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_573537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573537 prefixEnd_573537 := by exact prefixLift 573537
  have htrace : WordTrace (prefixWord ++ tailWord_573537) baseStart_573537 baseEnd_573537 := by
    simpa [prefixWord, tailWord_573537, baseEnd_573537] using wordTrace_append hprefix tailTrace_573537
  have hstable : (prefixWord ++ tailWord_573537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573537).length < 2 ^ (prefixWord ++ tailWord_573537).sum := by decide
  have hdescent : baseEnd_573537 < baseStart_573537 := by decide
  rcases family_descends (prefixWord ++ tailWord_573537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573554 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_573554 : Nat := 118140960795 + 573554 * 2 ^ 59
def prefixEnd_573554 : Nat := 4983230072969 + 3 ^ 40 * 573554 * 2
def baseEnd_573554 : Nat := 294508883308954201037279

theorem tailTrace_573554 : CollatzResearch.WordTrace tailWord_573554 prefixEnd_573554 294508883308954201037279 := by
  unfold tailWord_573554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229808241029822017423929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13946155309412858713130477 5229808241029822017423929)
  ·
    refine ⟨3922356180772366513067947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5229808241029822017423929 3922356180772366513067947)
    ·
      refine ⟨5883534271158549769601921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922356180772366513067947 5883534271158549769601921)
      ·
        refine ⟨4412650703368912327201441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5883534271158549769601921 4412650703368912327201441)
        ·
          refine ⟨3309488027526684245401081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4412650703368912327201441 3309488027526684245401081)
          ·
            refine ⟨2482116020645013184050811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3309488027526684245401081 2482116020645013184050811)
            ·
              refine ⟨3723174030967519776076217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482116020645013184050811 3723174030967519776076217)
              ·
                refine ⟨2792380523225639832057163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3723174030967519776076217 2792380523225639832057163)
                ·
                  refine ⟨4188570784838459748085745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792380523225639832057163 4188570784838459748085745)
                  ·
                    refine ⟨3141428088628844811064309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4188570784838459748085745 3141428088628844811064309)
                    ·
                      refine ⟨294508883308954201037279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3141428088628844811064309 294508883308954201037279)
                      ·
                        rfl

theorem cell23_573554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_573554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573554 prefixEnd_573554 := by exact prefixLift 573554
  have htrace : WordTrace (prefixWord ++ tailWord_573554) baseStart_573554 baseEnd_573554 := by
    simpa [prefixWord, tailWord_573554, baseEnd_573554] using wordTrace_append hprefix tailTrace_573554
  have hstable : (prefixWord ++ tailWord_573554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573554).length < 2 ^ (prefixWord ++ tailWord_573554).sum := by decide
  have hdescent : baseEnd_573554 < baseStart_573554 := by decide
  rcases family_descends (prefixWord ++ tailWord_573554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573584 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_573584 : Nat := 118140960795 + 573584 * 2 ^ 59
def prefixEnd_573584 : Nat := 4983230072969 + 3 ^ 40 * 573584 * 2
def baseEnd_573584 : Nat := 294524287728589083662141

theorem tailTrace_573584 : CollatzResearch.WordTrace tailWord_573584 prefixEnd_573584 294524287728589083662141 := by
  unfold tailWord_573584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10460163577005301596643903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13946884769340402128858537 10460163577005301596643903)
  ·
    refine ⟨15690245365507952394965855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10460163577005301596643903 15690245365507952394965855)
    ·
      refine ⟨23535368048261928592448783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15690245365507952394965855 23535368048261928592448783)
      ·
        refine ⟨35303052072392892888673175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23535368048261928592448783 35303052072392892888673175)
        ·
          refine ⟨52954578108589339333009763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35303052072392892888673175 52954578108589339333009763)
          ·
            refine ⟨79431867162884008999514645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52954578108589339333009763 79431867162884008999514645)
            ·
              refine ⟨3723368773260187921852249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79431867162884008999514645 3723368773260187921852249)
              ·
                refine ⟨2792526579945140941389187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3723368773260187921852249 2792526579945140941389187)
                ·
                  refine ⟨4188789869917711412083781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792526579945140941389187 4188789869917711412083781)
                  ·
                    refine ⟨785398100609570889765709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188789869917711412083781 785398100609570889765709)
                    ·
                      refine ⟨294524287728589083662141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 785398100609570889765709 294524287728589083662141)
                      ·
                        rfl

theorem cell23_573584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_573584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573584 prefixEnd_573584 := by exact prefixLift 573584
  have htrace : WordTrace (prefixWord ++ tailWord_573584) baseStart_573584 baseEnd_573584 := by
    simpa [prefixWord, tailWord_573584, baseEnd_573584] using wordTrace_append hprefix tailTrace_573584
  have hstable : (prefixWord ++ tailWord_573584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573584).length < 2 ^ (prefixWord ++ tailWord_573584).sum := by decide
  have hdescent : baseEnd_573584 < baseStart_573584 := by decide
  rcases family_descends (prefixWord ++ tailWord_573584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573587 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 10]
def baseStart_573587 : Nat := 118140960795 + 573587 * 2 ^ 59
def prefixEnd_573587 : Nat := 4983230072969 + 3 ^ 40 * 573587 * 2
def baseEnd_573587 : Nat := 32725092018950285769403

theorem tailTrace_573587 : CollatzResearch.WordTrace tailWord_573587 prefixEnd_573587 32725092018950285769403 := by
  unfold tailWord_573587
  simp only [CollatzResearch.WordTrace]
  refine ⟨20920436572999734705647015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13946957715333156470431343 20920436572999734705647015)
  ·
    refine ⟨31380654859499602058470523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20920436572999734705647015 31380654859499602058470523)
    ·
      refine ⟨47070982289249403087705785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31380654859499602058470523 47070982289249403087705785)
      ·
        refine ⟨35303236716937052315779339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47070982289249403087705785 35303236716937052315779339)
        ·
          refine ⟨52954855075405578473669009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35303236716937052315779339 52954855075405578473669009)
          ·
            refine ⟨39716141306554183855251757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52954855075405578473669009 39716141306554183855251757)
            ·
              refine ⟨14893552989957818945719409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39716141306554183855251757 14893552989957818945719409)
              ·
                refine ⟨11170164742468364209289557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14893552989957818945719409 11170164742468364209289557)
                ·
                  refine ⟨32725092018950285769403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 11170164742468364209289557 32725092018950285769403)
                  ·
                    rfl

theorem cell23_573587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 10].length) (baseStart_573587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573587 prefixEnd_573587 := by exact prefixLift 573587
  have htrace : WordTrace (prefixWord ++ tailWord_573587) baseStart_573587 baseEnd_573587 := by
    simpa [prefixWord, tailWord_573587, baseEnd_573587] using wordTrace_append hprefix tailTrace_573587
  have hstable : (prefixWord ++ tailWord_573587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573587).length < 2 ^ (prefixWord ++ tailWord_573587).sum := by decide
  have hdescent : baseEnd_573587 < baseStart_573587 := by decide
  rcases family_descends (prefixWord ++ tailWord_573587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573598 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_573598 : Nat := 118140960795 + 573598 * 2 ^ 59
def prefixEnd_573598 : Nat := 4983230072969 + 3 ^ 40 * 573598 * 2
def baseEnd_573598 : Nat := 294531476457752028887077

theorem tailTrace_573598 : CollatzResearch.WordTrace tailWord_573598 prefixEnd_573598 294531476457752028887077 := by
  unfold tailWord_573598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2615104721994985448037181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13947225183973255722864965 2615104721994985448037181)
  ·
    refine ⟨980664270748119543013943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2615104721994985448037181 980664270748119543013943)
    ·
      refine ⟨1470996406122179314520915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 980664270748119543013943 1470996406122179314520915)
      ·
        refine ⟨2206494609183268971781373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470996406122179314520915 2206494609183268971781373)
        ·
          refine ⟨827435478443725864418015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2206494609183268971781373 827435478443725864418015)
          ·
            refine ⟨1241153217665588796627023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827435478443725864418015 1241153217665588796627023)
            ·
              refine ⟨1861729826498383194940535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241153217665588796627023 1861729826498383194940535)
              ·
                refine ⟨2792594739747574792410803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861729826498383194940535 2792594739747574792410803)
                ·
                  refine ⟨4188892109621362188616205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792594739747574792410803 4188892109621362188616205)
                  ·
                    refine ⟨1570834541108010820731077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4188892109621362188616205 1570834541108010820731077)
                    ·
                      refine ⟨294531476457752028887077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1570834541108010820731077 294531476457752028887077)
                      ·
                        rfl

theorem cell23_573598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_573598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573598 prefixEnd_573598 := by exact prefixLift 573598
  have htrace : WordTrace (prefixWord ++ tailWord_573598) baseStart_573598 baseEnd_573598 := by
    simpa [prefixWord, tailWord_573598, baseEnd_573598] using wordTrace_append hprefix tailTrace_573598
  have hstable : (prefixWord ++ tailWord_573598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573598).length < 2 ^ (prefixWord ++ tailWord_573598).sum := by decide
  have hdescent : baseEnd_573598 < baseStart_573598 := by decide
  rcases family_descends (prefixWord ++ tailWord_573598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573601 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_573601 : Nat := 118140960795 + 573601 * 2 ^ 59
def prefixEnd_573601 : Nat := 4983230072969 + 3 ^ 40 * 573601 * 2
def baseEnd_573601 : Nat := 294533016899715517149563

theorem tailTrace_573601 : CollatzResearch.WordTrace tailWord_573601 prefixEnd_573601 294533016899715517149563 := by
  unfold tailWord_573601
  simp only [CollatzResearch.WordTrace]
  refine ⟨20920947194949015096656657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13947298129966010064437771 20920947194949015096656657)
  ·
    refine ⟨15690710396211761322492493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20920947194949015096656657 15690710396211761322492493)
    ·
      refine ⟨5884016398579410495934685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15690710396211761322492493 5884016398579410495934685)
      ·
        refine ⟨2206506149467278935975507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5884016398579410495934685 2206506149467278935975507)
        ·
          refine ⟨3309759224200918403963261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206506149467278935975507 3309759224200918403963261)
          ·
            refine ⟨1241159709075344401486223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3309759224200918403963261 1241159709075344401486223)
            ·
              refine ⟨1861739563613016602229335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241159709075344401486223 1861739563613016602229335)
              ·
                refine ⟨2792609345419524903344003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861739563613016602229335 2792609345419524903344003)
                ·
                  refine ⟨4188914018129287355016005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792609345419524903344003 4188914018129287355016005)
                  ·
                    refine ⟨785421378399241379065501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188914018129287355016005 785421378399241379065501)
                    ·
                      refine ⟨294533016899715517149563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 785421378399241379065501 294533016899715517149563)
                      ·
                        rfl

theorem cell23_573601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_573601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573601 prefixEnd_573601 := by exact prefixLift 573601
  have htrace : WordTrace (prefixWord ++ tailWord_573601) baseStart_573601 baseEnd_573601 := by
    simpa [prefixWord, tailWord_573601, baseEnd_573601] using wordTrace_append hprefix tailTrace_573601
  have hstable : (prefixWord ++ tailWord_573601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573601).length < 2 ^ (prefixWord ++ tailWord_573601).sum := by decide
  have hdescent : baseEnd_573601 < baseStart_573601 := by decide
  rcases family_descends (prefixWord ++ tailWord_573601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573641 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 6, 3, 2]
def baseStart_573641 : Nat := 118140960795 + 573641 * 2 ^ 59
def prefixEnd_573641 : Nat := 4983230072969 + 3 ^ 40 * 573641 * 2
def baseEnd_573641 : Nat := 294553556125895360649379

theorem tailTrace_573641 : CollatzResearch.WordTrace tailWord_573641 prefixEnd_573641 294553556125895360649379 := by
  unfold tailWord_573641
  simp only [CollatzResearch.WordTrace]
  refine ⟨20922406114804101928112777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13948270743202734618741851 20922406114804101928112777)
  ·
    refine ⟨15691804586103076446084583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20922406114804101928112777 15691804586103076446084583)
    ·
      refine ⟨23537706879154614669126875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15691804586103076446084583 23537706879154614669126875)
      ·
        refine ⟨35306560318731922003690313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23537706879154614669126875 35306560318731922003690313)
        ·
          refine ⟨26479920239048941502767735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35306560318731922003690313 26479920239048941502767735)
          ·
            refine ⟨39719880358573412254151603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26479920239048941502767735 39719880358573412254151603)
            ·
              refine ⟨59579820537860118381227405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39719880358573412254151603 59579820537860118381227405)
              ·
                refine ⟨22342432701697544392960277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59579820537860118381227405 22342432701697544392960277)
                ·
                  refine ⟨1047301532892072393420013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22342432701697544392960277 1047301532892072393420013)
                  ·
                    refine ⟨392738074834527147532505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1047301532892072393420013 392738074834527147532505)
                    ·
                      refine ⟨294553556125895360649379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392738074834527147532505 294553556125895360649379)
                      ·
                        rfl

theorem cell23_573641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 3, 2].length) (baseStart_573641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573641 prefixEnd_573641 := by exact prefixLift 573641
  have htrace : WordTrace (prefixWord ++ tailWord_573641) baseStart_573641 baseEnd_573641 := by
    simpa [prefixWord, tailWord_573641, baseEnd_573641] using wordTrace_append hprefix tailTrace_573641
  have hstable : (prefixWord ++ tailWord_573641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573641).length < 2 ^ (prefixWord ++ tailWord_573641).sum := by decide
  have hdescent : baseEnd_573641 < baseStart_573641 := by decide
  rcases family_descends (prefixWord ++ tailWord_573641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573664 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_573664 : Nat := 118140960795 + 573664 * 2 ^ 59
def prefixEnd_573664 : Nat := 4983230072969 + 3 ^ 40 * 573664 * 2
def baseEnd_573664 : Nat := 98188455393649590220591

theorem tailTrace_573664 : CollatzResearch.WordTrace tailWord_573664 prefixEnd_573664 98188455393649590220591 := by
  unfold tailWord_573664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461622496860388428100023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13948829995813851237466697 10461622496860388428100023)
  ·
    refine ⟨15692433745290582642150035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10461622496860388428100023 15692433745290582642150035)
    ·
      refine ⟨23538650617935873963225053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15692433745290582642150035 23538650617935873963225053)
      ·
        refine ⟨8826993981725952736209395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23538650617935873963225053 8826993981725952736209395)
        ·
          refine ⟨13240490972588929104314093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826993981725952736209395 13240490972588929104314093)
          ·
            refine ⟨4965184114720848414117785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13240490972588929104314093 4965184114720848414117785)
            ·
              refine ⟨3723888086040636310588339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4965184114720848414117785 3723888086040636310588339)
              ·
                refine ⟨5585832129060954465882509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723888086040636310588339 5585832129060954465882509)
                ·
                  refine ⟨2094687048397857924705941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5585832129060954465882509 2094687048397857924705941)
                  ·
                    refine ⟨98188455393649590220591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2094687048397857924705941 98188455393649590220591)
                    ·
                      rfl

theorem cell23_573664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_573664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573664 prefixEnd_573664 := by exact prefixLift 573664
  have htrace : WordTrace (prefixWord ++ tailWord_573664) baseStart_573664 baseEnd_573664 := by
    simpa [prefixWord, tailWord_573664, baseEnd_573664] using wordTrace_append hprefix tailTrace_573664
  have hstable : (prefixWord ++ tailWord_573664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573664).length < 2 ^ (prefixWord ++ tailWord_573664).sum := by decide
  have hdescent : baseEnd_573664 < baseStart_573664 := by decide
  rcases family_descends (prefixWord ++ tailWord_573664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573681 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_573681 : Nat := 118140960795 + 573681 * 2 ^ 59
def prefixEnd_573681 : Nat := 4983230072969 + 3 ^ 40 * 573681 * 2
def baseEnd_573681 : Nat := 98191365117358401383065

theorem tailTrace_573681 : CollatzResearch.WordTrace tailWord_573681 prefixEnd_573681 98191365117358401383065 := by
  unfold tailWord_573681
  simp only [CollatzResearch.WordTrace]
  refine ⟨20923865034659188759568897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13949243356439459173045931 20923865034659188759568897)
  ·
    refine ⟨15692898775994391569676673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20923865034659188759568897 15692898775994391569676673)
    ·
      refine ⟨11769674081995793677257505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15692898775994391569676673 11769674081995793677257505)
      ·
        refine ⟨8827255561496845257943129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11769674081995793677257505 8827255561496845257943129)
        ·
          refine ⟨6620441671122633943457347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8827255561496845257943129 6620441671122633943457347)
          ·
            refine ⟨9930662506683950915186021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620441671122633943457347 9930662506683950915186021)
            ·
              refine ⟨1861999220003240796597379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9930662506683950915186021 1861999220003240796597379)
              ·
                refine ⟨2792998830004861194896069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861999220003240796597379 2792998830004861194896069)
                ·
                  refine ⟨523687280625911474043013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2792998830004861194896069 523687280625911474043013)
                  ·
                    refine ⟨98191365117358401383065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 523687280625911474043013 98191365117358401383065)
                    ·
                      rfl

theorem cell23_573681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_573681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573681 prefixEnd_573681 := by exact prefixLift 573681
  have htrace : WordTrace (prefixWord ++ tailWord_573681) baseStart_573681 baseEnd_573681 := by
    simpa [prefixWord, tailWord_573681, baseEnd_573681] using wordTrace_append hprefix tailTrace_573681
  have hstable : (prefixWord ++ tailWord_573681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573681).length < 2 ^ (prefixWord ++ tailWord_573681).sum := by decide
  have hdescent : baseEnd_573681 < baseStart_573681 := by decide
  rcases family_descends (prefixWord ++ tailWord_573681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573725 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_573725 : Nat := 118140960795 + 573725 * 2 ^ 59
def prefixEnd_573725 : Nat := 4983230072969 + 3 ^ 40 * 573725 * 2
def baseEnd_573725 : Nat := 294596688500873031998993

theorem tailTrace_573725 : CollatzResearch.WordTrace tailWord_573725 prefixEnd_573725 294596688500873031998993 := by
  unfold tailWord_573725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20925469846499784274170629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13950313230999856182780419 20925469846499784274170629)
  ·
    refine ⟨3923525596218709551406993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20925469846499784274170629 3923525596218709551406993)
    ·
      refine ⟨2942644197164032163555245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3923525596218709551406993 2942644197164032163555245)
      ·
        refine ⟨1103491573936512061333217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2942644197164032163555245 1103491573936512061333217)
        ·
          refine ⟨827618680452384045999913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103491573936512061333217 827618680452384045999913)
          ·
            refine ⟨620714010339288034499935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827618680452384045999913 620714010339288034499935)
            ·
              refine ⟨931071015508932051749903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620714010339288034499935 931071015508932051749903)
              ·
                refine ⟨1396606523263398077624855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931071015508932051749903 1396606523263398077624855)
                ·
                  refine ⟨2094909784895097116437283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396606523263398077624855 2094909784895097116437283)
                  ·
                    refine ⟨3142364677342645674655925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094909784895097116437283 3142364677342645674655925)
                    ·
                      refine ⟨294596688500873031998993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3142364677342645674655925 294596688500873031998993)
                      ·
                        rfl

theorem cell23_573725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_573725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573725 prefixEnd_573725 := by exact prefixLift 573725
  have htrace : WordTrace (prefixWord ++ tailWord_573725) baseStart_573725 baseEnd_573725 := by
    simpa [prefixWord, tailWord_573725, baseEnd_573725] using wordTrace_append hprefix tailTrace_573725
  have hstable : (prefixWord ++ tailWord_573725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573725).length < 2 ^ (prefixWord ++ tailWord_573725).sum := by decide
  have hdescent : baseEnd_573725 < baseStart_573725 := by decide
  rcases family_descends (prefixWord ++ tailWord_573725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573791 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_573791 : Nat := 118140960795 + 573791 * 2 ^ 59
def prefixEnd_573791 : Nat := 4983230072969 + 3 ^ 40 * 573791 * 2
def baseEnd_573791 : Nat := 294630578224069773773689

theorem tailTrace_573791 : CollatzResearch.WordTrace tailWord_573791 prefixEnd_573791 294630578224069773773689 := by
  unfold tailWord_573791
  simp only [CollatzResearch.WordTrace]
  refine ⟨20927877064260677546073227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13951918042840451697382151 20927877064260677546073227)
  ·
    refine ⟨31391815596391016319109841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20927877064260677546073227 31391815596391016319109841)
    ·
      refine ⟨23543861697293262239332381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31391815596391016319109841 23543861697293262239332381)
      ·
        refine ⟨8828948136484973339749643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23543861697293262239332381 8828948136484973339749643)
        ·
          refine ⟨13243422204727460009624465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8828948136484973339749643 13243422204727460009624465)
          ·
            refine ⟨9932566653545595007218349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13243422204727460009624465 9932566653545595007218349)
            ·
              refine ⟨3724712495079598127706881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9932566653545595007218349 3724712495079598127706881)
              ·
                refine ⟨2793534371309698595780161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724712495079598127706881 2793534371309698595780161)
                ·
                  refine ⟨2095150778482273946835121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793534371309698595780161 2095150778482273946835121)
                  ·
                    refine ⟨1571363083861705460126341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095150778482273946835121 1571363083861705460126341)
                    ·
                      refine ⟨294630578224069773773689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1571363083861705460126341 294630578224069773773689)
                      ·
                        rfl

theorem cell23_573791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_573791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573791 prefixEnd_573791 := by exact prefixLift 573791
  have htrace : WordTrace (prefixWord ++ tailWord_573791) baseStart_573791 baseEnd_573791 := by
    simpa [prefixWord, tailWord_573791, baseEnd_573791] using wordTrace_append hprefix tailTrace_573791
  have hstable : (prefixWord ++ tailWord_573791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573791).length < 2 ^ (prefixWord ++ tailWord_573791).sum := by decide
  have hdescent : baseEnd_573791 < baseStart_573791 := by decide
  rcases family_descends (prefixWord ++ tailWord_573791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573795 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 4, 2, 2]
def baseStart_573795 : Nat := 118140960795 + 573795 * 2 ^ 59
def prefixEnd_573795 : Nat := 4983230072969 + 3 ^ 40 * 573795 * 2
def baseEnd_573795 : Nat := 294632632146687758123671

theorem tailTrace_573795 : CollatzResearch.WordTrace tailWord_573795 prefixEnd_573795 294632632146687758123671 := by
  unfold tailWord_573795
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928022956246186229218839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952015304164124152812559 20928022956246186229218839)
  ·
    refine ⟨31392034434369279343828259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20928022956246186229218839 31392034434369279343828259)
    ·
      refine ⟨47088051651553919015742389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31392034434369279343828259 47088051651553919015742389)
      ·
        refine ⟨4414504842333179907725849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47088051651553919015742389 4414504842333179907725849)
        ·
          refine ⟨3310878631749884930794387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4414504842333179907725849 3310878631749884930794387)
          ·
            refine ⟨4966317947624827396191581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310878631749884930794387 4966317947624827396191581)
            ·
              refine ⟨1862369230359310273571843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4966317947624827396191581 1862369230359310273571843)
              ·
                refine ⟨2793553845538965410357765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862369230359310273571843 2793553845538965410357765)
                ·
                  refine ⟨523791346038556014442081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2793553845538965410357765 523791346038556014442081)
                  ·
                    refine ⟨392843509528917010831561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 523791346038556014442081 392843509528917010831561)
                    ·
                      refine ⟨294632632146687758123671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392843509528917010831561 294632632146687758123671)
                      ·
                        rfl

theorem cell23_573795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_573795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573795 prefixEnd_573795 := by exact prefixLift 573795
  have htrace : WordTrace (prefixWord ++ tailWord_573795) baseStart_573795 baseEnd_573795 := by
    simpa [prefixWord, tailWord_573795, baseEnd_573795] using wordTrace_append hprefix tailTrace_573795
  have hstable : (prefixWord ++ tailWord_573795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573795).length < 2 ^ (prefixWord ++ tailWord_573795).sum := by decide
  have hdescent : baseEnd_573795 < baseStart_573795 := by decide
  rcases family_descends (prefixWord ++ tailWord_573795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573801 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 7]
def baseStart_573801 : Nat := 118140960795 + 573801 * 2 ^ 59
def prefixEnd_573801 : Nat := 4983230072969 + 3 ^ 40 * 573801 * 2
def baseEnd_573801 : Nat := 32737301447846081627627

theorem tailTrace_573801 : CollatzResearch.WordTrace tailWord_573801 prefixEnd_573801 32737301447846081627627 := by
  unfold tailWord_573801
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928241794224449253937257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952161196149632835958171 20928241794224449253937257)
  ·
    refine ⟨15696181345668336940452943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20928241794224449253937257 15696181345668336940452943)
    ·
      refine ⟨23544272018502505410679415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15696181345668336940452943 23544272018502505410679415)
      ·
        refine ⟨35316408027753758116019123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23544272018502505410679415 35316408027753758116019123)
        ·
          refine ⟨52974612041630637174028685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35316408027753758116019123 52974612041630637174028685)
          ·
            refine ⟨19865479515611488940260757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52974612041630637174028685 19865479515611488940260757)
            ·
              refine ⟨931194352294288544074723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19865479515611488940260757 931194352294288544074723)
              ·
                refine ⟨1396791528441432816112085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931194352294288544074723 1396791528441432816112085)
                ·
                  refine ⟨32737301447846081627627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1396791528441432816112085 32737301447846081627627)
                  ·
                    rfl

theorem cell23_573801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_573801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573801 prefixEnd_573801 := by exact prefixLift 573801
  have htrace : WordTrace (prefixWord ++ tailWord_573801) baseStart_573801 baseEnd_573801 := by
    simpa [prefixWord, tailWord_573801, baseEnd_573801] using wordTrace_append hprefix tailTrace_573801
  have hstable : (prefixWord ++ tailWord_573801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573801).length < 2 ^ (prefixWord ++ tailWord_573801).sum := by decide
  have hdescent : baseEnd_573801 < baseStart_573801 := by decide
  rcases family_descends (prefixWord ++ tailWord_573801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573831 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 7]
def baseStart_573831 : Nat := 118140960795 + 573831 * 2 ^ 59
def prefixEnd_573831 : Nat := 4983230072969 + 3 ^ 40 * 573831 * 2
def baseEnd_573831 : Nat := 98217039150083205757835

theorem tailTrace_573831 : CollatzResearch.WordTrace tailWord_573831 prefixEnd_573831 98217039150083205757835 := by
  unfold tailWord_573831
  simp only [CollatzResearch.WordTrace]
  refine ⟨20929335984115764377529347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952890656077176251686231 20929335984115764377529347)
  ·
    refine ⟨31394003976173646566294021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20929335984115764377529347 31394003976173646566294021)
    ·
      refine ⟨5886375745532558731180129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31394003976173646566294021 5886375745532558731180129)
      ·
        refine ⟨4414781809149419048385097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5886375745532558731180129 4414781809149419048385097)
        ·
          refine ⟨3311086356862064286288823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4414781809149419048385097 3311086356862064286288823)
          ·
            refine ⟨4966629535293096429433235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311086356862064286288823 4966629535293096429433235)
            ·
              refine ⟨7449944302939644644149853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966629535293096429433235 7449944302939644644149853)
              ·
                refine ⟨2793729113602366741556195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7449944302939644644149853 2793729113602366741556195)
                ·
                  refine ⟨4190593670403550112334293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793729113602366741556195 4190593670403550112334293)
                  ·
                    refine ⟨98217039150083205757835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4190593670403550112334293 98217039150083205757835)
                    ·
                      rfl

theorem cell23_573831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_573831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573831 prefixEnd_573831 := by exact prefixLift 573831
  have htrace : WordTrace (prefixWord ++ tailWord_573831) baseStart_573831 baseEnd_573831 := by
    simpa [prefixWord, tailWord_573831, baseEnd_573831] using wordTrace_append hprefix tailTrace_573831
  have hstable : (prefixWord ++ tailWord_573831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573831).length < 2 ^ (prefixWord ++ tailWord_573831).sum := by decide
  have hdescent : baseEnd_573831 < baseStart_573831 := by decide
  rcases family_descends (prefixWord ++ tailWord_573831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573835 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 5]
def baseStart_573835 : Nat := 118140960795 + 573835 * 2 ^ 59
def prefixEnd_573835 : Nat := 4983230072969 + 3 ^ 40 * 573835 * 2
def baseEnd_573835 : Nat := 32739241263651955735943

theorem tailTrace_573835 : CollatzResearch.WordTrace tailWord_573835 prefixEnd_573835 32739241263651955735943 := by
  unfold tailWord_573835
  simp only [CollatzResearch.WordTrace]
  refine ⟨20929481876101273060674959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952987917400848707116639 20929481876101273060674959)
  ·
    refine ⟨31394222814151909591012439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20929481876101273060674959 31394222814151909591012439)
    ·
      refine ⟨47091334221227864386518659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31394222814151909591012439 47091334221227864386518659)
      ·
        refine ⟨70637001331841796579777989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47091334221227864386518659 70637001331841796579777989)
        ·
          refine ⟨13244437749720336858708373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70637001331841796579777989 13244437749720336858708373)
          ·
            refine ⟨620833019518140790251955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13244437749720336858708373 620833019518140790251955)
            ·
              refine ⟨931249529277211185377933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620833019518140790251955 931249529277211185377933)
              ·
                refine ⟨349218573478954194516725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 931249529277211185377933 349218573478954194516725)
                ·
                  refine ⟨32739241263651955735943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 349218573478954194516725 32739241263651955735943)
                  ·
                    rfl

theorem cell23_573835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 5].length) (baseStart_573835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573835 prefixEnd_573835 := by exact prefixLift 573835
  have htrace : WordTrace (prefixWord ++ tailWord_573835) baseStart_573835 baseEnd_573835 := by
    simpa [prefixWord, tailWord_573835, baseEnd_573835] using wordTrace_append hprefix tailTrace_573835
  have hstable : (prefixWord ++ tailWord_573835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573835).length < 2 ^ (prefixWord ++ tailWord_573835).sum := by decide
  have hdescent : baseEnd_573835 < baseStart_573835 := by decide
  rcases family_descends (prefixWord ++ tailWord_573835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573848 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_573848 : Nat := 118140960795 + 573848 * 2 ^ 59
def prefixEnd_573848 : Nat := 4983230072969 + 3 ^ 40 * 573848 * 2
def baseEnd_573848 : Nat := 98219948873792016920309

theorem tailTrace_573848 : CollatzResearch.WordTrace tailWord_573848 prefixEnd_573848 98219948873792016920309 := by
  unfold tailWord_573848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464978012527088140449099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13953304016702784187265465 10464978012527088140449099)
  ·
    refine ⟨15697467018790632210673649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10464978012527088140449099 15697467018790632210673649)
    ·
      refine ⟨11773100264092974158005237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15697467018790632210673649 11773100264092974158005237)
      ·
        refine ⟨1103728149758716327312991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11773100264092974158005237 1103728149758716327312991)
        ·
          refine ⟨1655592224638074490969487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103728149758716327312991 1655592224638074490969487)
          ·
            refine ⟨2483388336957111736454231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655592224638074490969487 2483388336957111736454231)
            ·
              refine ⟨3725082505435667604681347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483388336957111736454231 3725082505435667604681347)
              ·
                refine ⟨5587623758153501407022021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725082505435667604681347 5587623758153501407022021)
                ·
                  refine ⟨1047679454653781513816629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5587623758153501407022021 1047679454653781513816629)
                  ·
                    refine ⟨98219948873792016920309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1047679454653781513816629 98219948873792016920309)
                    ·
                      rfl

theorem cell23_573848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_573848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573848 prefixEnd_573848 := by exact prefixLift 573848
  have htrace : WordTrace (prefixWord ++ tailWord_573848) baseStart_573848 baseEnd_573848 := by
    simpa [prefixWord, tailWord_573848, baseEnd_573848] using wordTrace_append hprefix tailTrace_573848
  have hstable : (prefixWord ++ tailWord_573848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573848).length < 2 ^ (prefixWord ++ tailWord_573848).sum := by decide
  have hdescent : baseEnd_573848 < baseStart_573848 := by decide
  rcases family_descends (prefixWord ++ tailWord_573848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573858 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_573858 : Nat := 118140960795 + 573858 * 2 ^ 59
def prefixEnd_573858 : Nat := 4983230072969 + 3 ^ 40 * 573858 * 2
def baseEnd_573858 : Nat := 294664981427921011635881

theorem tailTrace_573858 : CollatzResearch.WordTrace tailWord_573858 prefixEnd_573858 294664981427921011635881 := by
  unfold tailWord_573858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5232580188754486997190557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13953547170011965325841485 5232580188754486997190557)
  ·
    refine ⟨1962217570782932623946459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5232580188754486997190557 1962217570782932623946459)
    ·
      refine ⟨2943326356174398935919689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962217570782932623946459 2943326356174398935919689)
      ·
        refine ⟨2207494767130799201939767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2943326356174398935919689 2207494767130799201939767)
        ·
          refine ⟨3311242150696198802909651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207494767130799201939767 3311242150696198802909651)
          ·
            refine ⟨4966863226044298204364477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311242150696198802909651 4966863226044298204364477)
            ·
              refine ⟨1862573709766611826636679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4966863226044298204364477 1862573709766611826636679)
              ·
                refine ⟨2793860564649917739955019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862573709766611826636679 2793860564649917739955019)
                ·
                  refine ⟨4190790846974876609932529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793860564649917739955019 4190790846974876609932529)
                  ·
                    refine ⟨3143093135231157457449397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190790846974876609932529 3143093135231157457449397)
                    ·
                      refine ⟨294664981427921011635881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3143093135231157457449397 294664981427921011635881)
                      ·
                        rfl

theorem cell23_573858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_573858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573858 prefixEnd_573858 := by exact prefixLift 573858
  have htrace : WordTrace (prefixWord ++ tailWord_573858) baseStart_573858 baseEnd_573858 := by
    simpa [prefixWord, tailWord_573858, baseEnd_573858] using wordTrace_append hprefix tailTrace_573858
  have hstable : (prefixWord ++ tailWord_573858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573858).length < 2 ^ (prefixWord ++ tailWord_573858).sum := by decide
  have hdescent : baseEnd_573858 < baseStart_573858 := by decide
  rcases family_descends (prefixWord ++ tailWord_573858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573868 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_573868 : Nat := 118140960795 + 573868 * 2 ^ 59
def prefixEnd_573868 : Nat := 4983230072969 + 3 ^ 40 * 573868 * 2
def baseEnd_573868 : Nat := 294670116234465972510835

theorem tailTrace_573868 : CollatzResearch.WordTrace tailWord_573868 prefixEnd_573868 294670116234465972510835 := by
  unfold tailWord_573868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465342742490859848313129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13953790323321146464417505 10465342742490859848313129)
  ·
    refine ⟨7849007056868144886234847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10465342742490859848313129 7849007056868144886234847)
    ·
      refine ⟨11773510585302217329352271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7849007056868144886234847 11773510585302217329352271)
      ·
        refine ⟨17660265877953325994028407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773510585302217329352271 17660265877953325994028407)
        ·
          refine ⟨26490398816929988991042611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660265877953325994028407 26490398816929988991042611)
          ·
            refine ⟨39735598225394983486563917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26490398816929988991042611 39735598225394983486563917)
            ·
              refine ⟨14900849334523118807461469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39735598225394983486563917 14900849334523118807461469)
              ·
                refine ⟨5587818500446169552798051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14900849334523118807461469 5587818500446169552798051)
                ·
                  refine ⟨8381727750669254329197077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5587818500446169552798051 8381727750669254329197077)
                  ·
                    refine ⟨392893488312621296681113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8381727750669254329197077 392893488312621296681113)
                    ·
                      refine ⟨294670116234465972510835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 392893488312621296681113 294670116234465972510835)
                      ·
                        rfl

theorem cell23_573868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_573868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573868 prefixEnd_573868 := by exact prefixLift 573868
  have htrace : WordTrace (prefixWord ++ tailWord_573868) baseStart_573868 baseEnd_573868 := by
    simpa [prefixWord, tailWord_573868, baseEnd_573868] using wordTrace_append hprefix tailTrace_573868
  have hstable : (prefixWord ++ tailWord_573868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573868).length < 2 ^ (prefixWord ++ tailWord_573868).sum := by decide
  have hdescent : baseEnd_573868 < baseStart_573868 := by decide
  rcases family_descends (prefixWord ++ tailWord_573868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573885 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_573885 : Nat := 118140960795 + 573885 * 2 ^ 59
def prefixEnd_573885 : Nat := 4983230072969 + 3 ^ 40 * 573885 * 2
def baseEnd_573885 : Nat := 294678845405592405998257

theorem tailTrace_573885 : CollatzResearch.WordTrace tailWord_573885 prefixEnd_573885 294678845405592405998257 := by
  unfold tailWord_573885
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931305525920131599995109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13954203683946754399996739 20931305525920131599995109)
  ·
    refine ⟨3924619786110024674999083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20931305525920131599995109 3924619786110024674999083)
    ·
      refine ⟨5886929679165037012498625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924619786110024674999083 5886929679165037012498625)
      ·
        refine ⟨4415197259373777759373969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5886929679165037012498625 4415197259373777759373969)
        ·
          refine ⟨3311397944530333319530477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415197259373777759373969 3311397944530333319530477)
          ·
            refine ⟨1241774229198874994823929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3311397944530333319530477 1241774229198874994823929)
            ·
              refine ⟨931330671899156246117947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241774229198874994823929 931330671899156246117947)
              ·
                refine ⟨1396996007848734369176921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931330671899156246117947 1396996007848734369176921)
                ·
                  refine ⟨1047747005886550776882691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396996007848734369176921 1047747005886550776882691)
                  ·
                    refine ⟨1571620508829826165324037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047747005886550776882691 1571620508829826165324037)
                    ·
                      refine ⟨294678845405592405998257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1571620508829826165324037 294678845405592405998257)
                      ·
                        rfl

theorem cell23_573885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_573885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573885 prefixEnd_573885 := by exact prefixLift 573885
  have htrace : WordTrace (prefixWord ++ tailWord_573885) baseStart_573885 baseEnd_573885 := by
    simpa [prefixWord, tailWord_573885, baseEnd_573885] using wordTrace_append hprefix tailTrace_573885
  have hstable : (prefixWord ++ tailWord_573885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573885).length < 2 ^ (prefixWord ++ tailWord_573885).sum := by decide
  have hdescent : baseEnd_573885 < baseStart_573885 := by decide
  rcases family_descends (prefixWord ++ tailWord_573885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573931 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7]
def baseStart_573931 : Nat := 118140960795 + 573931 * 2 ^ 59
def prefixEnd_573931 : Nat := 4983230072969 + 3 ^ 40 * 573931 * 2
def baseEnd_573931 : Nat := 294702465515699226023045

theorem tailTrace_573931 : CollatzResearch.WordTrace tailWord_573931 prefixEnd_573931 294702465515699226023045 := by
  unfold tailWord_573931
  simp only [CollatzResearch.WordTrace]
  refine ⟨20932983283753481456169647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13955322189168987637446431 20932983283753481456169647)
  ·
    refine ⟨31399474925630222184254471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20932983283753481456169647 31399474925630222184254471)
    ·
      refine ⟨47099212388445333276381707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31399474925630222184254471 47099212388445333276381707)
      ·
        refine ⟨70648818582667999914572561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47099212388445333276381707 70648818582667999914572561)
        ·
          refine ⟨52986613937000999935929421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70648818582667999914572561 52986613937000999935929421)
          ·
            refine ⟨19869980226375374975973533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52986613937000999935929421 19869980226375374975973533)
            ·
              refine ⟨7451242584890765615990075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19869980226375374975973533 7451242584890765615990075)
              ·
                refine ⟨11176863877336148423985113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451242584890765615990075 11176863877336148423985113)
                ·
                  refine ⟨8382647908002111317988835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11176863877336148423985113 8382647908002111317988835)
                  ·
                    refine ⟨12573971862003166976983253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8382647908002111317988835 12573971862003166976983253)
                    ·
                      refine ⟨294702465515699226023045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12573971862003166976983253 294702465515699226023045)
                      ·
                        rfl

theorem cell23_573931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_573931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573931 prefixEnd_573931 := by exact prefixLift 573931
  have htrace : WordTrace (prefixWord ++ tailWord_573931) baseStart_573931 baseEnd_573931 := by
    simpa [prefixWord, tailWord_573931, baseEnd_573931] using wordTrace_append hprefix tailTrace_573931
  have hstable : (prefixWord ++ tailWord_573931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573931).length < 2 ^ (prefixWord ++ tailWord_573931).sum := by decide
  have hdescent : baseEnd_573931 < baseStart_573931 := by decide
  rcases family_descends (prefixWord ++ tailWord_573931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573978 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_573978 : Nat := 118140960795 + 573978 * 2 ^ 59
def prefixEnd_573978 : Nat := 4983230072969 + 3 ^ 40 * 573978 * 2
def baseEnd_573978 : Nat := 294726599106460542135329

theorem tailTrace_573978 : CollatzResearch.WordTrace tailWord_573978 prefixEnd_573978 294726599106460542135329 := by
  unfold tailWord_573978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233674378645802120782647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13956465009722138988753725 5233674378645802120782647)
  ·
    refine ⟨7850511567968703181173971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5233674378645802120782647 7850511567968703181173971)
    ·
      refine ⟨11775767351953054771760957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7850511567968703181173971 11775767351953054771760957)
      ·
        refine ⟨4415912756982395539410359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11775767351953054771760957 4415912756982395539410359)
        ·
          refine ⟨6623869135473593309115539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415912756982395539410359 6623869135473593309115539)
          ·
            refine ⟨9935803703210389963673309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623869135473593309115539 9935803703210389963673309)
            ·
              refine ⟨3725926388703896236377491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9935803703210389963673309 3725926388703896236377491)
              ·
                refine ⟨5588889583055844354566237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725926388703896236377491 5588889583055844354566237)
                ·
                  refine ⟨2095833593645941632962339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5588889583055844354566237 2095833593645941632962339)
                  ·
                    refine ⟨3143750390468912449443509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095833593645941632962339 3143750390468912449443509)
                    ·
                      refine ⟨294726599106460542135329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3143750390468912449443509 294726599106460542135329)
                      ·
                        rfl

theorem cell23_573978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_573978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573978 prefixEnd_573978 := by exact prefixLift 573978
  have htrace : WordTrace (prefixWord ++ tailWord_573978) baseStart_573978 baseEnd_573978 := by
    simpa [prefixWord, tailWord_573978, baseEnd_573978] using wordTrace_append hprefix tailTrace_573978
  have hstable : (prefixWord ++ tailWord_573978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573978).length < 2 ^ (prefixWord ++ tailWord_573978).sum := by decide
  have hdescent : baseEnd_573978 < baseStart_573978 := by decide
  rcases family_descends (prefixWord ++ tailWord_573978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573992 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_573992 : Nat := 118140960795 + 573992 * 2 ^ 59
def prefixEnd_573992 : Nat := 4983230072969 + 3 ^ 40 * 573992 * 2
def baseEnd_573992 : Nat := 294733787835623487360265

theorem tailTrace_573992 : CollatzResearch.WordTrace tailWord_573992 prefixEnd_573992 294733787835623487360265 := by
  unfold tailWord_573992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467604068266244437070115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13956805424354992582760153 10467604068266244437070115)
  ·
    refine ⟨15701406102399366655605173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10467604068266244437070115 15701406102399366655605173)
    ·
      refine ⟨1472006822099940623962985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15701406102399366655605173 1472006822099940623962985)
      ·
        refine ⟨1104005116574955467972239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1472006822099940623962985 1104005116574955467972239)
        ·
          refine ⟨1656007674862433201958359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104005116574955467972239 1656007674862433201958359)
          ·
            refine ⟨2484011512293649802937539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656007674862433201958359 2484011512293649802937539)
            ·
              refine ⟨3726017268440474704406309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484011512293649802937539 3726017268440474704406309)
              ·
                refine ⟨698628237832589007076183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3726017268440474704406309 698628237832589007076183)
                ·
                  refine ⟨1047942356748883510614275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698628237832589007076183 1047942356748883510614275)
                  ·
                    refine ⟨1571913535123325265921413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047942356748883510614275 1571913535123325265921413)
                    ·
                      refine ⟨294733787835623487360265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1571913535123325265921413 294733787835623487360265)
                      ·
                        rfl

theorem cell23_573992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_573992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_573992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_573992 prefixEnd_573992 := by exact prefixLift 573992
  have htrace : WordTrace (prefixWord ++ tailWord_573992) baseStart_573992 baseEnd_573992 := by
    simpa [prefixWord, tailWord_573992, baseEnd_573992] using wordTrace_append hprefix tailTrace_573992
  have hstable : (prefixWord ++ tailWord_573992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573992).length < 2 ^ (prefixWord ++ tailWord_573992).sum := by decide
  have hdescent : baseEnd_573992 < baseStart_573992 := by decide
  rcases family_descends (prefixWord ++ tailWord_573992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574012 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_574012 : Nat := 118140960795 + 574012 * 2 ^ 59
def prefixEnd_574012 : Nat := 4983230072969 + 3 ^ 40 * 574012 * 2
def baseEnd_574012 : Nat := 294744057448713409110173

theorem tailTrace_574012 : CollatzResearch.WordTrace tailWord_574012 prefixEnd_574012 294744057448713409110173 := by
  unfold tailWord_574012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467968798230016144934145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13957291730973354859912193 10467968798230016144934145)
  ·
    refine ⟨7850976598672512108700609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10467968798230016144934145 7850976598672512108700609)
    ·
      refine ⟨5888232449004384081525457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7850976598672512108700609 5888232449004384081525457)
      ·
        refine ⟨4416174336753288061144093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5888232449004384081525457 4416174336753288061144093)
        ·
          refine ⟨1656065376282483022929035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4416174336753288061144093 1656065376282483022929035)
          ·
            refine ⟨2484098064423724534393553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656065376282483022929035 2484098064423724534393553)
            ·
              refine ⟨1863073548317793400795165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484098064423724534393553 1863073548317793400795165)
              ·
                refine ⟨698652580619172525298187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863073548317793400795165 698652580619172525298187)
                ·
                  refine ⟨1047978870928758787947281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698652580619172525298187 1047978870928758787947281)
                  ·
                    refine ⟨785984153196569090960461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1047978870928758787947281 785984153196569090960461)
                    ·
                      refine ⟨294744057448713409110173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 785984153196569090960461 294744057448713409110173)
                      ·
                        rfl

theorem cell23_574012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_574012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574012 prefixEnd_574012 := by exact prefixLift 574012
  have htrace : WordTrace (prefixWord ++ tailWord_574012) baseStart_574012 baseEnd_574012 := by
    simpa [prefixWord, tailWord_574012, baseEnd_574012] using wordTrace_append hprefix tailTrace_574012
  have hstable : (prefixWord ++ tailWord_574012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574012).length < 2 ^ (prefixWord ++ tailWord_574012).sum := by decide
  have hdescent : baseEnd_574012 < baseStart_574012 := by decide
  rcases family_descends (prefixWord ++ tailWord_574012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574020 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_574020 : Nat := 118140960795 + 574020 * 2 ^ 59
def prefixEnd_574020 : Nat := 4983230072969 + 3 ^ 40 * 574020 * 2
def baseEnd_574020 : Nat := 294748165293949377810137

theorem tailTrace_574020 : CollatzResearch.WordTrace tailWord_574020 prefixEnd_574020 294748165293949377810137 := by
  unfold tailWord_574020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468114690215524828079757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13957486253620699770773009 10468114690215524828079757)
  ·
    refine ⟨3925543008830821810529909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10468114690215524828079757 3925543008830821810529909)
    ·
      refine ⟨368019657077889544737179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3925543008830821810529909 368019657077889544737179)
      ·
        refine ⟨552029485616834317105769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368019657077889544737179 552029485616834317105769)
        ·
          refine ⟨414022114212625737829327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552029485616834317105769 414022114212625737829327)
          ·
            refine ⟨621033171318938606743991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414022114212625737829327 621033171318938606743991)
            ·
              refine ⟨931549756978407910115987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621033171318938606743991 931549756978407910115987)
              ·
                refine ⟨1397324635467611865173981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931549756978407910115987 1397324635467611865173981)
                ·
                  refine ⟨523996738300354449440243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1397324635467611865173981 523996738300354449440243)
                  ·
                    refine ⟨785995107450531674160365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 523996738300354449440243 785995107450531674160365)
                    ·
                      refine ⟨294748165293949377810137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 785995107450531674160365 294748165293949377810137)
                      ·
                        rfl

theorem cell23_574020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_574020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574020 prefixEnd_574020 := by exact prefixLift 574020
  have htrace : WordTrace (prefixWord ++ tailWord_574020) baseStart_574020 baseEnd_574020 := by
    simpa [prefixWord, tailWord_574020, baseEnd_574020] using wordTrace_append hprefix tailTrace_574020
  have hstable : (prefixWord ++ tailWord_574020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574020).length < 2 ^ (prefixWord ++ tailWord_574020).sum := by decide
  have hdescent : baseEnd_574020 < baseStart_574020 := by decide
  rcases family_descends (prefixWord ++ tailWord_574020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574022 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_574022 : Nat := 118140960795 + 574022 * 2 ^ 59
def prefixEnd_574022 : Nat := 4983230072969 + 3 ^ 40 * 574022 * 2
def baseEnd_574022 : Nat := 294749192255258369985127

theorem tailTrace_574022 : CollatzResearch.WordTrace tailWord_574022 prefixEnd_574022 294749192255258369985127 := by
  unfold tailWord_574022
  simp only [CollatzResearch.WordTrace]
  refine ⟨654259447700743874929135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13957534884282535998488213 654259447700743874929135)
  ·
    refine ⟨981389171551115812393703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654259447700743874929135 981389171551115812393703)
    ·
      refine ⟨1472083757326673718590555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981389171551115812393703 1472083757326673718590555)
      ·
        refine ⟨2208125635990010577885833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472083757326673718590555 2208125635990010577885833)
        ·
          refine ⟨1656094226992507933414375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208125635990010577885833 1656094226992507933414375)
          ·
            refine ⟨2484141340488761900121563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656094226992507933414375 2484141340488761900121563)
            ·
              refine ⟨3726212010733142850182345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484141340488761900121563 3726212010733142850182345)
              ·
                refine ⟨2794659008049857137636759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3726212010733142850182345 2794659008049857137636759)
                ·
                  refine ⟨4191988512074785706455139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794659008049857137636759 4191988512074785706455139)
                  ·
                    refine ⟨6287982768112178559682709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4191988512074785706455139 6287982768112178559682709)
                    ·
                      refine ⟨294749192255258369985127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6287982768112178559682709 294749192255258369985127)
                      ·
                        rfl

theorem cell23_574022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_574022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574022 prefixEnd_574022 := by exact prefixLift 574022
  have htrace : WordTrace (prefixWord ++ tailWord_574022) baseStart_574022 baseEnd_574022 := by
    simpa [prefixWord, tailWord_574022, baseEnd_574022] using wordTrace_append hprefix tailTrace_574022
  have hstable : (prefixWord ++ tailWord_574022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574022).length < 2 ^ (prefixWord ++ tailWord_574022).sum := by decide
  have hdescent : baseEnd_574022 < baseStart_574022 := by decide
  rcases family_descends (prefixWord ++ tailWord_574022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574028 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_574028 : Nat := 118140960795 + 574028 * 2 ^ 59
def prefixEnd_574028 : Nat := 4983230072969 + 3 ^ 40 * 574028 * 2
def baseEnd_574028 : Nat := 98250757713061782170033

theorem tailTrace_574028 : CollatzResearch.WordTrace tailWord_574028 prefixEnd_574028 98250757713061782170033 := by
  unfold tailWord_574028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468260582201033511225369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13957680776268044681633825 10468260582201033511225369)
  ·
    refine ⟨7851195436650775133419027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10468260582201033511225369 7851195436650775133419027)
    ·
      refine ⟨11776793154976162700128541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851195436650775133419027 11776793154976162700128541)
      ·
        refine ⟨4416297433116061012548203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11776793154976162700128541 4416297433116061012548203)
        ·
          refine ⟨6624446149674091518822305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4416297433116061012548203 6624446149674091518822305)
          ·
            refine ⟨4968334612255568639116729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6624446149674091518822305 4968334612255568639116729)
            ·
              refine ⟨3726250959191676479337547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4968334612255568639116729 3726250959191676479337547)
              ·
                refine ⟨5589376438787514719006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3726250959191676479337547 5589376438787514719006321)
                ·
                  refine ⟨4192032329090636039254741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589376438787514719006321 4192032329090636039254741)
                  ·
                    refine ⟨98250757713061782170033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4192032329090636039254741 98250757713061782170033)
                    ·
                      rfl

theorem cell23_574028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_574028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574028 prefixEnd_574028 := by exact prefixLift 574028
  have htrace : WordTrace (prefixWord ++ tailWord_574028) baseStart_574028 baseEnd_574028 := by
    simpa [prefixWord, tailWord_574028, baseEnd_574028] using wordTrace_append hprefix tailTrace_574028
  have hstable : (prefixWord ++ tailWord_574028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574028).length < 2 ^ (prefixWord ++ tailWord_574028).sum := by decide
  have hdescent : baseEnd_574028 < baseStart_574028 := by decide
  rcases family_descends (prefixWord ++ tailWord_574028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574052 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_574052 : Nat := 118140960795 + 574052 * 2 ^ 59
def prefixEnd_574052 : Nat := 4983230072969 + 3 ^ 40 * 574052 * 2
def baseEnd_574052 : Nat := 294764596674893252609989

theorem tailTrace_574052 : CollatzResearch.WordTrace tailWord_574052 prefixEnd_574052 294764596674893252609989 := by
  unfold tailWord_574052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468698258157559560662205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13958264344210079414216273 10468698258157559560662205)
  ·
    refine ⟨3925761846809084835248327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10468698258157559560662205 3925761846809084835248327)
    ·
      refine ⟨5888642770213627252872491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925761846809084835248327 5888642770213627252872491)
      ·
        refine ⟨8832964155320440879308737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888642770213627252872491 8832964155320440879308737)
        ·
          refine ⟨6624723116490330659481553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8832964155320440879308737 6624723116490330659481553)
          ·
            refine ⟨4968542337367747994611165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6624723116490330659481553 4968542337367747994611165)
            ·
              refine ⟨1863203376512905497979187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4968542337367747994611165 1863203376512905497979187)
              ·
                refine ⟨2794805064769358246968781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863203376512905497979187 2794805064769358246968781)
                ·
                  refine ⟨1048051899288509342613293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2794805064769358246968781 1048051899288509342613293)
                  ·
                    refine ⟨393019462233191003479985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048051899288509342613293 393019462233191003479985)
                    ·
                      refine ⟨294764596674893252609989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393019462233191003479985 294764596674893252609989)
                      ·
                        rfl

theorem cell23_574052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_574052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574052 prefixEnd_574052 := by exact prefixLift 574052
  have htrace : WordTrace (prefixWord ++ tailWord_574052) baseStart_574052 baseEnd_574052 := by
    simpa [prefixWord, tailWord_574052, baseEnd_574052] using wordTrace_append hprefix tailTrace_574052
  have hstable : (prefixWord ++ tailWord_574052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574052).length < 2 ^ (prefixWord ++ tailWord_574052).sum := by decide
  have hdescent : baseEnd_574052 < baseStart_574052 := by decide
  rcases family_descends (prefixWord ++ tailWord_574052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574085 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_574085 : Nat := 118140960795 + 574085 * 2 ^ 59
def prefixEnd_574085 : Nat := 4983230072969 + 3 ^ 40 * 574085 * 2
def baseEnd_574085 : Nat := 294781541536491623497337

theorem tailTrace_574085 : CollatzResearch.WordTrace tailWord_574085 prefixEnd_574085 294781541536491623497337 := by
  unfold tailWord_574085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20938600125195565757275709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13959066750130377171517139 20938600125195565757275709)
  ·
    refine ⟨7851975046948337158978391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20938600125195565757275709 7851975046948337158978391)
    ·
      refine ⟨11777962570422505738467587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851975046948337158978391 11777962570422505738467587)
      ·
        refine ⟨17666943855633758607701381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11777962570422505738467587 17666943855633758607701381)
        ·
          refine ⟨3312551972931329738944009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17666943855633758607701381 3312551972931329738944009)
          ·
            refine ⟨2484413979698497304208007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3312551972931329738944009 2484413979698497304208007)
            ·
              refine ⟨3726620969547745956312011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484413979698497304208007 3726620969547745956312011)
              ·
                refine ⟨5589931454321618934468017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3726620969547745956312011 5589931454321618934468017)
                ·
                  refine ⟨4192448590741214200851013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589931454321618934468017 4192448590741214200851013)
                  ·
                    refine ⟨786084110763977662659565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4192448590741214200851013 786084110763977662659565)
                    ·
                      refine ⟨294781541536491623497337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 786084110763977662659565 294781541536491623497337)
                      ·
                        rfl

theorem cell23_574085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_574085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574085 prefixEnd_574085 := by exact prefixLift 574085
  have htrace : WordTrace (prefixWord ++ tailWord_574085) baseStart_574085 baseEnd_574085 := by
    simpa [prefixWord, tailWord_574085, baseEnd_574085] using wordTrace_append hprefix tailTrace_574085
  have hstable : (prefixWord ++ tailWord_574085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574085).length < 2 ^ (prefixWord ++ tailWord_574085).sum := by decide
  have hdescent : baseEnd_574085 < baseStart_574085 := by decide
  rcases family_descends (prefixWord ++ tailWord_574085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574133 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_574133 : Nat := 118140960795 + 574133 * 2 ^ 59
def prefixEnd_574133 : Nat := 4983230072969 + 3 ^ 40 * 574133 * 2
def baseEnd_574133 : Nat := 294806188607907435697117

theorem tailTrace_574133 : CollatzResearch.WordTrace tailWord_574133 prefixEnd_574133 294806188607907435697117 := by
  unfold tailWord_574133
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940350829021669955023053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13960233886014446636682035 20940350829021669955023053)
  ·
    refine ⟨7852631560883126233133645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20940350829021669955023053 7852631560883126233133645)
    ·
      refine ⟨2944736835331172337425117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7852631560883126233133645 2944736835331172337425117)
      ·
        refine ⟨1104276313249189626534419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2944736835331172337425117 1104276313249189626534419)
        ·
          refine ⟨1656414469873784439801629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104276313249189626534419 1656414469873784439801629)
          ·
            refine ⟨621155426202669164925611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1656414469873784439801629 621155426202669164925611)
            ·
              refine ⟨931733139304003747388417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621155426202669164925611 931733139304003747388417)
              ·
                refine ⟨698799854478002810541313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931733139304003747388417 698799854478002810541313)
                ·
                  refine ⟨524099890858502107905985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 698799854478002810541313 524099890858502107905985)
                  ·
                    refine ⟨393074918143876580929489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524099890858502107905985 393074918143876580929489)
                    ·
                      refine ⟨294806188607907435697117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393074918143876580929489 294806188607907435697117)
                      ·
                        rfl

theorem cell23_574133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_574133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574133 prefixEnd_574133 := by exact prefixLift 574133
  have htrace : WordTrace (prefixWord ++ tailWord_574133) baseStart_574133 baseEnd_574133 := by
    simpa [prefixWord, tailWord_574133, baseEnd_574133] using wordTrace_append hprefix tailTrace_574133
  have hstable : (prefixWord ++ tailWord_574133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574133).length < 2 ^ (prefixWord ++ tailWord_574133).sum := by decide
  have hdescent : baseEnd_574133 < baseStart_574133 := by decide
  rcases family_descends (prefixWord ++ tailWord_574133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574150 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_574150 : Nat := 118140960795 + 574150 * 2 ^ 59
def prefixEnd_574150 : Nat := 4983230072969 + 3 ^ 40 * 574150 * 2
def baseEnd_574150 : Nat := 294814917779033869184539

theorem tailTrace_574150 : CollatzResearch.WordTrace tailWord_574150 prefixEnd_574150 294814917779033869184539 := by
  unfold tailWord_574150
  simp only [CollatzResearch.WordTrace]
  refine ⟨654405339686252558074747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13960647246640054572261269 654405339686252558074747)
  ·
    refine ⟨981608009529378837112121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 654405339686252558074747 981608009529378837112121)
    ·
      refine ⟨736206007147034127834091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981608009529378837112121 736206007147034127834091)
      ·
        refine ⟨1104309010720551191751137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736206007147034127834091 1104309010720551191751137)
        ·
          refine ⟨828231758040413393813353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104309010720551191751137 828231758040413393813353)
          ·
            refine ⟨621173818530310045360015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828231758040413393813353 621173818530310045360015)
            ·
              refine ⟨931760727795465068040023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621173818530310045360015 931760727795465068040023)
              ·
                refine ⟨1397641091693197602060035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931760727795465068040023 1397641091693197602060035)
                ·
                  refine ⟨2096461637539796403090053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397641091693197602060035 2096461637539796403090053)
                  ·
                    refine ⟨393086557038711825579385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096461637539796403090053 393086557038711825579385)
                    ·
                      refine ⟨294814917779033869184539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393086557038711825579385 294814917779033869184539)
                      ·
                        rfl

theorem cell23_574150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_574150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574150 prefixEnd_574150 := by exact prefixLift 574150
  have htrace : WordTrace (prefixWord ++ tailWord_574150) baseStart_574150 baseEnd_574150 := by
    simpa [prefixWord, tailWord_574150, baseEnd_574150] using wordTrace_append hprefix tailTrace_574150
  have hstable : (prefixWord ++ tailWord_574150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574150).length < 2 ^ (prefixWord ++ tailWord_574150).sum := by decide
  have hdescent : baseEnd_574150 < baseStart_574150 := by decide
  rcases family_descends (prefixWord ++ tailWord_574150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574192 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3]
def baseStart_574192 : Nat := 118140960795 + 574192 * 2 ^ 59
def prefixEnd_574192 : Nat := 4983230072969 + 3 ^ 40 * 574192 * 2
def baseEnd_574192 : Nat := 294836483966522704859345

theorem tailTrace_574192 : CollatzResearch.WordTrace tailWord_574192 prefixEnd_574192 294836483966522704859345 := by
  unfold tailWord_574192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471251367903961515710415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13961668490538615354280553 10471251367903961515710415)
  ·
    refine ⟨15706877051855942273565623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10471251367903961515710415 15706877051855942273565623)
    ·
      refine ⟨23560315577783913410348435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15706877051855942273565623 23560315577783913410348435)
      ·
        refine ⟨35340473366675870115522653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23560315577783913410348435 35340473366675870115522653)
        ·
          refine ⟨13252677512503451293320995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35340473366675870115522653 13252677512503451293320995)
          ·
            refine ⟨19879016268755176939981493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13252677512503451293320995 19879016268755176939981493)
            ·
              refine ⟨1863657775195797838123265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19879016268755176939981493 1863657775195797838123265)
              ·
                refine ⟨1397743331396848378592449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863657775195797838123265 1397743331396848378592449)
                ·
                  refine ⟨1048307498547636283944337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1397743331396848378592449 1048307498547636283944337)
                  ·
                    refine ⟨786230623910727212958253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1048307498547636283944337 786230623910727212958253)
                    ·
                      refine ⟨294836483966522704859345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 786230623910727212958253 294836483966522704859345)
                      ·
                        rfl

theorem cell23_574192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_574192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574192 prefixEnd_574192 := by exact prefixLift 574192
  have htrace : WordTrace (prefixWord ++ tailWord_574192) baseStart_574192 baseEnd_574192 := by
    simpa [prefixWord, tailWord_574192, baseEnd_574192] using wordTrace_append hprefix tailTrace_574192
  have hstable : (prefixWord ++ tailWord_574192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574192).length < 2 ^ (prefixWord ++ tailWord_574192).sum := by decide
  have hdescent : baseEnd_574192 < baseStart_574192 := by decide
  rcases family_descends (prefixWord ++ tailWord_574192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574195 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 6]
def baseStart_574195 : Nat := 118140960795 + 574195 * 2 ^ 59
def prefixEnd_574195 : Nat := 4983230072969 + 3 ^ 40 * 574195 * 2
def baseEnd_574195 : Nat := 32759780489831799235759

theorem tailTrace_574195 : CollatzResearch.WordTrace tailWord_574195 prefixEnd_574195 32759780489831799235759 := by
  unfold tailWord_574195
  simp only [CollatzResearch.WordTrace]
  refine ⟨20942612154797054543780039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13961741436531369695853359 20942612154797054543780039)
  ·
    refine ⟨31413918232195581815670059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20942612154797054543780039 31413918232195581815670059)
    ·
      refine ⟨47120877348293372723505089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31413918232195581815670059 47120877348293372723505089)
      ·
        refine ⟨35340658011220029542628817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47120877348293372723505089 35340658011220029542628817)
        ·
          refine ⟨26505493508415022156971613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35340658011220029542628817 26505493508415022156971613)
          ·
            refine ⟨9939560065655633308864355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26505493508415022156971613 9939560065655633308864355)
            ·
              refine ⟨14909340098483449963296533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9939560065655633308864355 14909340098483449963296533)
              ·
                refine ⟨698875317116411717029525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14909340098483449963296533 698875317116411717029525)
                ·
                  refine ⟨32759780489831799235759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 698875317116411717029525 32759780489831799235759)
                  ·
                    rfl

theorem cell23_574195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 6].length) (baseStart_574195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574195 prefixEnd_574195 := by exact prefixLift 574195
  have htrace : WordTrace (prefixWord ++ tailWord_574195) baseStart_574195 baseEnd_574195 := by
    simpa [prefixWord, tailWord_574195, baseEnd_574195] using wordTrace_append hprefix tailTrace_574195
  have hstable : (prefixWord ++ tailWord_574195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574195).length < 2 ^ (prefixWord ++ tailWord_574195).sum := by decide
  have hdescent : baseEnd_574195 < baseStart_574195 := by decide
  rcases family_descends (prefixWord ++ tailWord_574195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574196 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_574196 : Nat := 118140960795 + 574196 * 2 ^ 59
def prefixEnd_574196 : Nat := 4983230072969 + 3 ^ 40 * 574196 * 2
def baseEnd_574196 : Nat := 294838537889140689209327

theorem tailTrace_574196 : CollatzResearch.WordTrace tailWord_574196 prefixEnd_574196 294838537889140689209327 := by
  unfold tailWord_574196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471324313896715857283221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13961765751862287809710961 10471324313896715857283221)
  ·
    refine ⟨490843327213908555810151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10471324313896715857283221 490843327213908555810151)
    ·
      refine ⟨736264990820862833715227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490843327213908555810151 736264990820862833715227)
      ·
        refine ⟨1104397486231294250572841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736264990820862833715227 1104397486231294250572841)
        ·
          refine ⟨828298114673470687929631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104397486231294250572841 828298114673470687929631)
          ·
            refine ⟨1242447172010206031894447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828298114673470687929631 1242447172010206031894447)
            ·
              refine ⟨1863670758015309047841671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242447172010206031894447 1863670758015309047841671)
              ·
                refine ⟨2795506137022963571762507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863670758015309047841671 2795506137022963571762507)
                ·
                  refine ⟨4193259205534445357643761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795506137022963571762507 4193259205534445357643761)
                  ·
                    refine ⟨3144944404150834018232821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4193259205534445357643761 3144944404150834018232821)
                    ·
                      refine ⟨294838537889140689209327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3144944404150834018232821 294838537889140689209327)
                      ·
                        rfl

theorem cell23_574196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_574196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574196 prefixEnd_574196 := by exact prefixLift 574196
  have htrace : WordTrace (prefixWord ++ tailWord_574196) baseStart_574196 baseEnd_574196 := by
    simpa [prefixWord, tailWord_574196, baseEnd_574196] using wordTrace_append hprefix tailTrace_574196
  have hstable : (prefixWord ++ tailWord_574196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574196).length < 2 ^ (prefixWord ++ tailWord_574196).sum := by decide
  have hdescent : baseEnd_574196 < baseStart_574196 := by decide
  rcases family_descends (prefixWord ++ tailWord_574196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574212 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 6]
def baseStart_574212 : Nat := 118140960795 + 574212 * 2 ^ 59
def prefixEnd_574212 : Nat := 4983230072969 + 3 ^ 40 * 574212 * 2
def baseEnd_574212 : Nat := 32760750397734736289917

theorem tailTrace_574212 : CollatzResearch.WordTrace tailWord_574212 prefixEnd_574212 32760750397734736289917 := by
  unfold tailWord_574212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10471616097867733223574445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13962154797156977631432593 10471616097867733223574445)
  ·
    refine ⟨3926856036700399958840417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10471616097867733223574445 3926856036700399958840417)
    ·
      refine ⟨2945142027525299969130313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3926856036700399958840417 2945142027525299969130313)
      ·
        refine ⟨2208856520643974976847735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2945142027525299969130313 2208856520643974976847735)
        ·
          refine ⟨3313284780965962465271603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208856520643974976847735 3313284780965962465271603)
          ·
            refine ⟨4969927171448943697907405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313284780965962465271603 4969927171448943697907405)
            ·
              refine ⟨1863722689293353886715277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4969927171448943697907405 1863722689293353886715277)
              ·
                refine ⟨698896008485007707518229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863722689293353886715277 698896008485007707518229)
                ·
                  refine ⟨32760750397734736289917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 698896008485007707518229 32760750397734736289917)
                  ·
                    rfl

theorem cell23_574212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_574212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574212 prefixEnd_574212 := by exact prefixLift 574212
  have htrace : WordTrace (prefixWord ++ tailWord_574212) baseStart_574212 baseEnd_574212 := by
    simpa [prefixWord, tailWord_574212, baseEnd_574212] using wordTrace_append hprefix tailTrace_574212
  have hstable : (prefixWord ++ tailWord_574212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574212).length < 2 ^ (prefixWord ++ tailWord_574212).sum := by decide
  have hdescent : baseEnd_574212 < baseStart_574212 := by decide
  rcases family_descends (prefixWord ++ tailWord_574212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574273 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_574273 : Nat := 118140960795 + 574273 * 2 ^ 59
def prefixEnd_574273 : Nat := 4983230072969 + 3 ^ 40 * 574273 * 2
def baseEnd_574273 : Nat := 294878075899536887946473

theorem tailTrace_574273 : CollatzResearch.WordTrace tailWord_574273 prefixEnd_574273 294878075899536887946473 := by
  unfold tailWord_574273
  simp only [CollatzResearch.WordTrace]
  refine ⟨20945457048514473865119473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13963638032342982576746315 20945457048514473865119473)
  ·
    refine ⟨15709092786385855398839605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20945457048514473865119473 15709092786385855398839605)
    ·
      refine ⟨1472727448723673943641213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15709092786385855398839605 1472727448723673943641213)
      ·
        refine ⟨552272793271377728865455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1472727448723673943641213 552272793271377728865455)
        ·
          refine ⟨828409189907066593298183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552272793271377728865455 828409189907066593298183)
          ·
            refine ⟨1242613784860599889947275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828409189907066593298183 1242613784860599889947275)
            ·
              refine ⟨1863920677290899834920913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242613784860599889947275 1863920677290899834920913)
              ·
                refine ⟨1397940507968174876190685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863920677290899834920913 1397940507968174876190685)
                ·
                  refine ⟨524227690488065578571507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1397940507968174876190685 524227690488065578571507)
                  ·
                    refine ⟨786341535732098367857261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524227690488065578571507 786341535732098367857261)
                    ·
                      refine ⟨294878075899536887946473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 786341535732098367857261 294878075899536887946473)
                      ·
                        rfl

theorem cell23_574273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_574273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574273 prefixEnd_574273 := by exact prefixLift 574273
  have htrace : WordTrace (prefixWord ++ tailWord_574273) baseStart_574273 baseEnd_574273 := by
    simpa [prefixWord, tailWord_574273, baseEnd_574273] using wordTrace_append hprefix tailTrace_574273
  have hstable : (prefixWord ++ tailWord_574273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574273).length < 2 ^ (prefixWord ++ tailWord_574273).sum := by decide
  have hdescent : baseEnd_574273 < baseStart_574273 := by decide
  rcases family_descends (prefixWord ++ tailWord_574273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574306 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_574306 : Nat := 118140960795 + 574306 * 2 ^ 59
def prefixEnd_574306 : Nat := 4983230072969 + 3 ^ 40 * 574306 * 2
def baseEnd_574306 : Nat := 98298340253711752944607

theorem tailTrace_574306 : CollatzResearch.WordTrace tailWord_574306 prefixEnd_574306 98298340253711752944607 := by
  unfold tailWord_574306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236665164348730125267693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13964440438263280334047181 5236665164348730125267693)
  ·
    refine ⟨1963749436630773796975385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5236665164348730125267693 1963749436630773796975385)
    ·
      refine ⟨1472812077473080347731539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1963749436630773796975385 1472812077473080347731539)
      ·
        refine ⟨2209218116209620521597309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472812077473080347731539 2209218116209620521597309)
        ·
          refine ⟨828456793578607695598991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2209218116209620521597309 828456793578607695598991)
          ·
            refine ⟨1242685190367911543398487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828456793578607695598991 1242685190367911543398487)
            ·
              refine ⟨1864027785551867315097731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242685190367911543398487 1864027785551867315097731)
              ·
                refine ⟨2796041678327800972646597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864027785551867315097731 2796041678327800972646597)
                ·
                  refine ⟨524257814686462682371237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2796041678327800972646597 524257814686462682371237)
                  ·
                    refine ⟨98298340253711752944607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524257814686462682371237 98298340253711752944607)
                    ·
                      rfl

theorem cell23_574306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_574306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574306 prefixEnd_574306 := by exact prefixLift 574306
  have htrace : WordTrace (prefixWord ++ tailWord_574306) baseStart_574306 baseEnd_574306 := by
    simpa [prefixWord, tailWord_574306, baseEnd_574306] using wordTrace_append hprefix tailTrace_574306
  have hstable : (prefixWord ++ tailWord_574306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574306).length < 2 ^ (prefixWord ++ tailWord_574306).sum := by decide
  have hdescent : baseEnd_574306 < baseStart_574306 := by decide
  rcases family_descends (prefixWord ++ tailWord_574306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574315 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 9]
def baseStart_574315 : Nat := 118140960795 + 574315 * 2 ^ 59
def prefixEnd_574315 : Nat := 4983230072969 + 3 ^ 40 * 574315 * 2
def baseEnd_574315 : Nat := 98299880695675241207093

theorem tailTrace_574315 : CollatzResearch.WordTrace tailWord_574315 prefixEnd_574315 98299880695675241207093 := by
  unfold tailWord_574315
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946988914362315038148399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13964659276241543358765599 20946988914362315038148399)
  ·
    refine ⟨31420483371543472557222599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20946988914362315038148399 31420483371543472557222599)
    ·
      refine ⟨47130725057315208835833899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31420483371543472557222599 47130725057315208835833899)
      ·
        refine ⟨70696087585972813253750849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47130725057315208835833899 70696087585972813253750849)
        ·
          refine ⟨53022065689479609940313137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70696087585972813253750849 53022065689479609940313137)
          ·
            refine ⟨39766549267109707455234853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53022065689479609940313137 39766549267109707455234853)
            ·
              refine ⟨7456227987583070147856535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39766549267109707455234853 7456227987583070147856535)
              ·
                refine ⟨11184341981374605221784803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7456227987583070147856535 11184341981374605221784803)
                ·
                  refine ⟨16776512972061907832677205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11184341981374605221784803 16776512972061907832677205)
                  ·
                    refine ⟨98299880695675241207093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16776512972061907832677205 98299880695675241207093)
                    ·
                      rfl

theorem cell23_574315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_574315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574315 prefixEnd_574315 := by exact prefixLift 574315
  have htrace : WordTrace (prefixWord ++ tailWord_574315) baseStart_574315 baseEnd_574315 := by
    simpa [prefixWord, tailWord_574315, baseEnd_574315] using wordTrace_append hprefix tailTrace_574315
  have hstable : (prefixWord ++ tailWord_574315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574315).length < 2 ^ (prefixWord ++ tailWord_574315).sum := by decide
  have hdescent : baseEnd_574315 < baseStart_574315 := by decide
  rcases family_descends (prefixWord ++ tailWord_574315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574326 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_574326 : Nat := 118140960795 + 574326 * 2 ^ 59
def prefixEnd_574326 : Nat := 4983230072969 + 3 ^ 40 * 574326 * 2
def baseEnd_574326 : Nat := 294905290374225180583729

theorem tailTrace_574326 : CollatzResearch.WordTrace tailWord_574326 prefixEnd_574326 294905290374225180583729 := by
  unfold tailWord_574326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309211882332653994799927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13964926744881642611199221 1309211882332653994799927)
  ·
    refine ⟨1963817823498980992199891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1309211882332653994799927 1963817823498980992199891)
    ·
      refine ⟨2945726735248471488299837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963817823498980992199891 2945726735248471488299837)
      ·
        refine ⟨1104647525718176808112439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2945726735248471488299837 1104647525718176808112439)
        ·
          refine ⟨1656971288577265212168659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104647525718176808112439 1656971288577265212168659)
          ·
            refine ⟨2485456932865897818252989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656971288577265212168659 2485456932865897818252989)
            ·
              refine ⟨932046349824711681844871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2485456932865897818252989 932046349824711681844871)
              ·
                refine ⟨1398069524737067522767307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932046349824711681844871 1398069524737067522767307)
                ·
                  refine ⟨2097104287105601284150961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398069524737067522767307 2097104287105601284150961)
                  ·
                    refine ⟨1572828215329200963113221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2097104287105601284150961 1572828215329200963113221)
                    ·
                      refine ⟨294905290374225180583729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1572828215329200963113221 294905290374225180583729)
                      ·
                        rfl

theorem cell23_574326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_574326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574326 prefixEnd_574326 := by exact prefixLift 574326
  have htrace : WordTrace (prefixWord ++ tailWord_574326) baseStart_574326 baseEnd_574326 := by
    simpa [prefixWord, tailWord_574326, baseEnd_574326] using wordTrace_append hprefix tailTrace_574326
  have hstable : (prefixWord ++ tailWord_574326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574326).length < 2 ^ (prefixWord ++ tailWord_574326).sum := by decide
  have hdescent : baseEnd_574326 < baseStart_574326 := by decide
  rcases family_descends (prefixWord ++ tailWord_574326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574329 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_574329 : Nat := 118140960795 + 574329 * 2 ^ 59
def prefixEnd_574329 : Nat := 4983230072969 + 3 ^ 40 * 574329 * 2
def baseEnd_574329 : Nat := 294906830816188668846215

theorem tailTrace_574329 : CollatzResearch.WordTrace tailWord_574329 prefixEnd_574329 294906830816188668846215 := by
  unfold tailWord_574329
  simp only [CollatzResearch.WordTrace]
  refine ⟨20947499536311595429158041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13964999690874396952772027 20947499536311595429158041)
  ·
    refine ⟨15710624652233696571868531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20947499536311595429158041 15710624652233696571868531)
    ·
      refine ⟨23565936978350544857802797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15710624652233696571868531 23565936978350544857802797)
      ·
        refine ⟨8837226366881454321676049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23565936978350544857802797 8837226366881454321676049)
        ·
          refine ⟨6627919775161090741257037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8837226366881454321676049 6627919775161090741257037)
          ·
            refine ⟨2485469915685409027971389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6627919775161090741257037 2485469915685409027971389)
            ·
              refine ⟨932051218382028385489271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2485469915685409027971389 932051218382028385489271)
              ·
                refine ⟨1398076827573042578233907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932051218382028385489271 1398076827573042578233907)
                ·
                  refine ⟨2097115241359563867350861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398076827573042578233907 2097115241359563867350861)
                  ·
                    refine ⟨786418215509836450256573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097115241359563867350861 786418215509836450256573)
                    ·
                      refine ⟨294906830816188668846215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 786418215509836450256573 294906830816188668846215)
                      ·
                        rfl

theorem cell23_574329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_574329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574329 prefixEnd_574329 := by exact prefixLift 574329
  have htrace : WordTrace (prefixWord ++ tailWord_574329) baseStart_574329 baseEnd_574329 := by
    simpa [prefixWord, tailWord_574329, baseEnd_574329] using wordTrace_append hprefix tailTrace_574329
  have hstable : (prefixWord ++ tailWord_574329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574329).length < 2 ^ (prefixWord ++ tailWord_574329).sum := by decide
  have hdescent : baseEnd_574329 < baseStart_574329 := by decide
  rcases family_descends (prefixWord ++ tailWord_574329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574346 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_574346 : Nat := 118140960795 + 574346 * 2 ^ 59
def prefixEnd_574346 : Nat := 4983230072969 + 3 ^ 40 * 574346 * 2
def baseEnd_574346 : Nat := 294915559987315102333637

theorem tailTrace_574346 : CollatzResearch.WordTrace tailWord_574346 prefixEnd_574346 294915559987315102333637 := by
  unfold tailWord_574346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237029894312501833131723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13965413051500004888351261 5237029894312501833131723)
  ·
    refine ⟨7855544841468752749697585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5237029894312501833131723 7855544841468752749697585)
    ·
      refine ⟨5891658631101564562273189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7855544841468752749697585 5891658631101564562273189)
      ·
        refine ⟨1104685993331543355426223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5891658631101564562273189 1104685993331543355426223)
        ·
          refine ⟨1657028989997315033139335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104685993331543355426223 1657028989997315033139335)
          ·
            refine ⟨2485543484995972549709003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657028989997315033139335 2485543484995972549709003)
            ·
              refine ⟨3728315227493958824563505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485543484995972549709003 3728315227493958824563505)
              ·
                refine ⟨2796236420620469118422629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728315227493958824563505 2796236420620469118422629)
                ·
                  refine ⟨524294328866337959704243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2796236420620469118422629 524294328866337959704243)
                  ·
                    refine ⟨786441493299506939556365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524294328866337959704243 786441493299506939556365)
                    ·
                      refine ⟨294915559987315102333637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 786441493299506939556365 294915559987315102333637)
                      ·
                        rfl

theorem cell23_574346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_574346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574346 prefixEnd_574346 := by exact prefixLift 574346
  have htrace : WordTrace (prefixWord ++ tailWord_574346) baseStart_574346 baseEnd_574346 := by
    simpa [prefixWord, tailWord_574346, baseEnd_574346] using wordTrace_append hprefix tailTrace_574346
  have hstable : (prefixWord ++ tailWord_574346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574346).length < 2 ^ (prefixWord ++ tailWord_574346).sum := by decide
  have hdescent : baseEnd_574346 < baseStart_574346 := by decide
  rcases family_descends (prefixWord ++ tailWord_574346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574372 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_574372 : Nat := 118140960795 + 574372 * 2 ^ 59
def prefixEnd_574372 : Nat := 4983230072969 + 3 ^ 40 * 574372 * 2
def baseEnd_574372 : Nat := 294928910484332000608517

theorem tailTrace_574372 : CollatzResearch.WordTrace tailWord_574372 prefixEnd_574372 294928910484332000608517 := by
  unfold tailWord_574372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10474533937577906886486685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13966045250103875848648913 10474533937577906886486685)
  ·
    refine ⟨3927950226591715082432507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10474533937577906886486685 3927950226591715082432507)
    ·
      refine ⟨5891925339887572623648761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3927950226591715082432507 5891925339887572623648761)
      ·
        refine ⟨4418944004915679467736571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5891925339887572623648761 4418944004915679467736571)
        ·
          refine ⟨6628416007373519201604857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418944004915679467736571 6628416007373519201604857)
          ·
            refine ⟨4971312005530139401203643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6628416007373519201604857 4971312005530139401203643)
            ·
              refine ⟨7456968008295209101805465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971312005530139401203643 7456968008295209101805465)
              ·
                refine ⟨5592726006221406826354099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7456968008295209101805465 5592726006221406826354099)
                ·
                  refine ⟨8389089009332110239531149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592726006221406826354099 8389089009332110239531149)
                  ·
                    refine ⟨3145908378499541339824181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8389089009332110239531149 3145908378499541339824181)
                    ·
                      refine ⟨294928910484332000608517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3145908378499541339824181 294928910484332000608517)
                      ·
                        rfl

theorem cell23_574372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_574372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574372 prefixEnd_574372 := by exact prefixLift 574372
  have htrace : WordTrace (prefixWord ++ tailWord_574372) baseStart_574372 baseEnd_574372 := by
    simpa [prefixWord, tailWord_574372, baseEnd_574372] using wordTrace_append hprefix tailTrace_574372
  have hstable : (prefixWord ++ tailWord_574372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574372).length < 2 ^ (prefixWord ++ tailWord_574372).sum := by decide
  have hdescent : baseEnd_574372 < baseStart_574372 := by decide
  rcases family_descends (prefixWord ++ tailWord_574372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574420 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_574420 : Nat := 118140960795 + 574420 * 2 ^ 59
def prefixEnd_574420 : Nat := 4983230072969 + 3 ^ 40 * 574420 * 2
def baseEnd_574420 : Nat := 294953557555747812808297

theorem tailTrace_574420 : CollatzResearch.WordTrace tailWord_574420 prefixEnd_574420 294953557555747812808297 := by
  unfold tailWord_574420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475409289490958985360357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13967212385987945313813809 10475409289490958985360357)
  ·
    refine ⟨1964139241779554809755067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10475409289490958985360357 1964139241779554809755067)
    ·
      refine ⟨2946208862669332214632601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1964139241779554809755067 2946208862669332214632601)
      ·
        refine ⟨2209656647001999160974451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2946208862669332214632601 2209656647001999160974451)
        ·
          refine ⟨3314484970502998741461677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209656647001999160974451 3314484970502998741461677)
          ·
            refine ⟨1242931863938624528048129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3314484970502998741461677 1242931863938624528048129)
            ·
              refine ⟨932198897953968396036097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242931863938624528048129 932198897953968396036097)
              ·
                refine ⟨699149173465476297027073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932198897953968396036097 699149173465476297027073)
                ·
                  refine ⟨524361880099107222770305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699149173465476297027073 524361880099107222770305)
                  ·
                    refine ⟨393271410074330417077729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524361880099107222770305 393271410074330417077729)
                    ·
                      refine ⟨294953557555747812808297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393271410074330417077729 294953557555747812808297)
                      ·
                        rfl

theorem cell23_574420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_574420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574420 prefixEnd_574420 := by exact prefixLift 574420
  have htrace : WordTrace (prefixWord ++ tailWord_574420) baseStart_574420 baseEnd_574420 := by
    simpa [prefixWord, tailWord_574420, baseEnd_574420] using wordTrace_append hprefix tailTrace_574420
  have hstable : (prefixWord ++ tailWord_574420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574420).length < 2 ^ (prefixWord ++ tailWord_574420).sum := by decide
  have hdescent : baseEnd_574420 < baseStart_574420 := by decide
  rcases family_descends (prefixWord ++ tailWord_574420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574426 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_574426 : Nat := 118140960795 + 574426 * 2 ^ 59
def prefixEnd_574426 : Nat := 4983230072969 + 3 ^ 40 * 574426 * 2
def baseEnd_574426 : Nat := 32772959826630532148141

theorem tailTrace_574426 : CollatzResearch.WordTrace tailWord_574426 prefixEnd_574426 32772959826630532148141 := by
  unfold tailWord_574426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5237759354240045248859783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13967358277973453996959421 5237759354240045248859783)
  ·
    refine ⟨7856639031360067873289675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5237759354240045248859783 7856639031360067873289675)
    ·
      refine ⟨11784958547040101809934513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7856639031360067873289675 11784958547040101809934513)
      ·
        refine ⟨8838718910280076357450885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11784958547040101809934513 8838718910280076357450885)
        ·
          refine ⟨1657259795677514317022041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8838718910280076357450885 1657259795677514317022041)
          ·
            refine ⟨1242944846758135737766531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657259795677514317022041 1242944846758135737766531)
            ·
              refine ⟨1864417270137203606649797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242944846758135737766531 1864417270137203606649797)
              ·
                refine ⟨349578238150725676246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1864417270137203606649797 349578238150725676246837)
                ·
                  refine ⟨32772959826630532148141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 349578238150725676246837 32772959826630532148141)
                  ·
                    rfl

theorem cell23_574426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_574426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574426 prefixEnd_574426 := by exact prefixLift 574426
  have htrace : WordTrace (prefixWord ++ tailWord_574426) baseStart_574426 baseEnd_574426 := by
    simpa [prefixWord, tailWord_574426, baseEnd_574426] using wordTrace_append hprefix tailTrace_574426
  have hstable : (prefixWord ++ tailWord_574426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574426).length < 2 ^ (prefixWord ++ tailWord_574426).sum := by decide
  have hdescent : baseEnd_574426 < baseStart_574426 := by decide
  rcases family_descends (prefixWord ++ tailWord_574426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574459 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 6, 2]
def baseStart_574459 : Nat := 118140960795 + 574459 * 2 ^ 59
def prefixEnd_574459 : Nat := 4983230072969 + 3 ^ 40 * 574459 * 2
def baseEnd_574459 : Nat := 294973583301273160220617

theorem tailTrace_574459 : CollatzResearch.WordTrace tailWord_574459 prefixEnd_574459 294973583301273160220617 := by
  unfold tailWord_574459
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952241025840627631390431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13968160683893751754260287 20952241025840627631390431)
  ·
    refine ⟨31428361538760941447085647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20952241025840627631390431 31428361538760941447085647)
    ·
      refine ⟨47142542308141412170628471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31428361538760941447085647 47142542308141412170628471)
      ·
        refine ⟨70713813462212118255942707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47142542308141412170628471 70713813462212118255942707)
        ·
          refine ⟨106070720193318177383914061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70713813462212118255942707 106070720193318177383914061)
          ·
            refine ⟨39776520072494316518967773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106070720193318177383914061 39776520072494316518967773)
            ·
              refine ⟨14916195027185368694612915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39776520072494316518967773 14916195027185368694612915)
              ·
                refine ⟨22374292540778053041919373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14916195027185368694612915 22374292540778053041919373)
                ·
                  refine ⟨8390359702791769890719765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22374292540778053041919373 8390359702791769890719765)
                  ·
                    refine ⟨393298111068364213627489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8390359702791769890719765 393298111068364213627489)
                    ·
                      refine ⟨294973583301273160220617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393298111068364213627489 294973583301273160220617)
                      ·
                        rfl

theorem cell23_574459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 6, 2].length) (baseStart_574459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574459 prefixEnd_574459 := by exact prefixLift 574459
  have htrace : WordTrace (prefixWord ++ tailWord_574459) baseStart_574459 baseEnd_574459 := by
    simpa [prefixWord, tailWord_574459, baseEnd_574459] using wordTrace_append hprefix tailTrace_574459
  have hstable : (prefixWord ++ tailWord_574459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574459).length < 2 ^ (prefixWord ++ tailWord_574459).sum := by decide
  have hdescent : baseEnd_574459 < baseStart_574459 := by decide
  rcases family_descends (prefixWord ++ tailWord_574459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574469 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_574469 : Nat := 118140960795 + 574469 * 2 ^ 59
def prefixEnd_574469 : Nat := 4983230072969 + 3 ^ 40 * 574469 * 2
def baseEnd_574469 : Nat := 98326239369272707031857

theorem tailTrace_574469 : CollatzResearch.WordTrace tailWord_574469 prefixEnd_574469 98326239369272707031857 := by
  unfold tailWord_574469
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952605755804399339254461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13968403837202932892836307 20952605755804399339254461)
  ·
    refine ⟨7857227158426649752220423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20952605755804399339254461 7857227158426649752220423)
    ·
      refine ⟨11785840737639974628330635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7857227158426649752220423 11785840737639974628330635)
      ·
        refine ⟨17678761106459961942495953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11785840737639974628330635 17678761106459961942495953)
        ·
          refine ⟨13259070829844971456871965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17678761106459961942495953 13259070829844971456871965)
          ·
            refine ⟨4972151561191864296326987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13259070829844971456871965 4972151561191864296326987)
            ·
              refine ⟨7458227341787796444490481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972151561191864296326987 7458227341787796444490481)
              ·
                refine ⟨5593670506340847333367861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7458227341787796444490481 5593670506340847333367861)
                ·
                  refine ⟨524406609969454437503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5593670506340847333367861 524406609969454437503237)
                  ·
                    refine ⟨98326239369272707031857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524406609969454437503237 98326239369272707031857)
                    ·
                      rfl

theorem cell23_574469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_574469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574469 prefixEnd_574469 := by exact prefixLift 574469
  have htrace : WordTrace (prefixWord ++ tailWord_574469) baseStart_574469 baseEnd_574469 := by
    simpa [prefixWord, tailWord_574469, baseEnd_574469] using wordTrace_append hprefix tailTrace_574469
  have hstable : (prefixWord ++ tailWord_574469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574469).length < 2 ^ (prefixWord ++ tailWord_574469).sum := by decide
  have hdescent : baseEnd_574469 < baseStart_574469 := by decide
  rcases family_descends (prefixWord ++ tailWord_574469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574476 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_574476 : Nat := 118140960795 + 574476 * 2 ^ 59
def prefixEnd_574476 : Nat := 4983230072969 + 3 ^ 40 * 574476 * 2
def baseEnd_574476 : Nat := 294982312472399593708039

theorem tailTrace_574476 : CollatzResearch.WordTrace tailWord_574476 prefixEnd_574476 294982312472399593708039 := by
  unfold tailWord_574476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10476430533389519767379641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13968574044519359689839521 10476430533389519767379641)
  ·
    refine ⟨7857322900042139825534731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10476430533389519767379641 7857322900042139825534731)
    ·
      refine ⟨11785984350063209738302097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7857322900042139825534731 11785984350063209738302097)
      ·
        refine ⟨8839488262547407303726573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11785984350063209738302097 8839488262547407303726573)
        ·
          refine ⟨3314808098455277738897465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8839488262547407303726573 3314808098455277738897465)
          ·
            refine ⟨2486106073841458304173099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3314808098455277738897465 2486106073841458304173099)
            ·
              refine ⟨3729159110762187456259649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486106073841458304173099 3729159110762187456259649)
              ·
                refine ⟨2796869333071640592194737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3729159110762187456259649 2796869333071640592194737)
                ·
                  refine ⟨2097651999803730444146053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2796869333071640592194737 2097651999803730444146053)
                  ·
                    refine ⟨393309749963199458277385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097651999803730444146053 393309749963199458277385)
                    ·
                      refine ⟨294982312472399593708039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393309749963199458277385 294982312472399593708039)
                      ·
                        rfl

theorem cell23_574476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_574476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574476 prefixEnd_574476 := by exact prefixLift 574476
  have htrace : WordTrace (prefixWord ++ tailWord_574476) baseStart_574476 baseEnd_574476 := by
    simpa [prefixWord, tailWord_574476, baseEnd_574476] using wordTrace_append hprefix tailTrace_574476
  have hstable : (prefixWord ++ tailWord_574476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574476).length < 2 ^ (prefixWord ++ tailWord_574476).sum := by decide
  have hdescent : baseEnd_574476 < baseStart_574476 := by decide
  rcases family_descends (prefixWord ++ tailWord_574476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574503 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 3, 4]
def baseStart_574503 : Nat := 118140960795 + 574503 * 2 ^ 59
def prefixEnd_574503 : Nat := 4983230072969 + 3 ^ 40 * 574503 * 2
def baseEnd_574503 : Nat := 98332058816690329356805

theorem tailTrace_574503 : CollatzResearch.WordTrace tailWord_574503 prefixEnd_574503 98332058816690329356805 := by
  unfold tailWord_574503
  simp only [CollatzResearch.WordTrace]
  refine ⟨20953845837681223145992163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13969230558454148763994775 20953845837681223145992163)
  ·
    refine ⟨31430768756521834718988245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20953845837681223145992163 31430768756521834718988245)
    ·
      refine ⟨736658642730980501226287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31430768756521834718988245 736658642730980501226287)
      ·
        refine ⟨1104987964096470751839431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736658642730980501226287 1104987964096470751839431)
        ·
          refine ⟨1657481946144706127759147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104987964096470751839431 1657481946144706127759147)
          ·
            refine ⟨2486222919217059191638721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657481946144706127759147 2486222919217059191638721)
            ·
              refine ⟨1864667189412794393729041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486222919217059191638721 1864667189412794393729041)
              ·
                refine ⟨1398500392059595795296781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864667189412794393729041 1398500392059595795296781)
                ·
                  refine ⟨524437647022348423236293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1398500392059595795296781 524437647022348423236293)
                  ·
                    refine ⟨98332058816690329356805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524437647022348423236293 98332058816690329356805)
                    ·
                      rfl

theorem cell23_574503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_574503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574503 prefixEnd_574503 := by exact prefixLift 574503
  have htrace : WordTrace (prefixWord ++ tailWord_574503) baseStart_574503 baseEnd_574503 := by
    simpa [prefixWord, tailWord_574503, baseEnd_574503] using wordTrace_append hprefix tailTrace_574503
  have hstable : (prefixWord ++ tailWord_574503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574503).length < 2 ^ (prefixWord ++ tailWord_574503).sum := by decide
  have hdescent : baseEnd_574503 < baseStart_574503 := by decide
  rcases family_descends (prefixWord ++ tailWord_574503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574516 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 8]
def baseStart_574516 : Nat := 118140960795 + 574516 * 2 ^ 59
def prefixEnd_574516 : Nat := 4983230072969 + 3 ^ 40 * 574516 * 2
def baseEnd_574516 : Nat := 32778094633175493023095

theorem tailTrace_574516 : CollatzResearch.WordTrace tailWord_574516 prefixEnd_574516 32778094633175493023095 := by
  unfold tailWord_574516
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477159993317063183107701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13969546657756084244143601 10477159993317063183107701)
  ·
    refine ⟨982233749373474673416347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10477159993317063183107701 982233749373474673416347)
    ·
      refine ⟨1473350624060212010124521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982233749373474673416347 1473350624060212010124521)
      ·
        refine ⟨1105012968045159007593391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1473350624060212010124521 1105012968045159007593391)
        ·
          refine ⟨1657519452067738511390087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105012968045159007593391 1657519452067738511390087)
          ·
            refine ⟨2486279178101607767085131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657519452067738511390087 2486279178101607767085131)
            ·
              refine ⟨3729418767152411650627697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486279178101607767085131 3729418767152411650627697)
              ·
                refine ⟨2797064075364308737970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3729418767152411650627697 2797064075364308737970773)
                ·
                  refine ⟨32778094633175493023095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2797064075364308737970773 32778094633175493023095)
                  ·
                    rfl

theorem cell23_574516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_574516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574516 prefixEnd_574516 := by exact prefixLift 574516
  have htrace : WordTrace (prefixWord ++ tailWord_574516) baseStart_574516 baseEnd_574516 := by
    simpa [prefixWord, tailWord_574516, baseEnd_574516] using wordTrace_append hprefix tailTrace_574516
  have hstable : (prefixWord ++ tailWord_574516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574516).length < 2 ^ (prefixWord ++ tailWord_574516).sum := by decide
  have hdescent : baseEnd_574516 < baseStart_574516 := by decide
  rcases family_descends (prefixWord ++ tailWord_574516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574520 : List Nat := [2, 1, 2, 1, 5, 3, 1, 3, 1, 4]
def baseStart_574520 : Nat := 118140960795 + 574520 * 2 ^ 59
def prefixEnd_574520 : Nat := 4983230072969 + 3 ^ 40 * 574520 * 2
def baseEnd_574520 : Nat := 98334968540399140519279

theorem tailTrace_574520 : CollatzResearch.WordTrace tailWord_574520 prefixEnd_574520 98334968540399140519279 := by
  unfold tailWord_574520
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477232939309817524680507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13969643919079756699574009 10477232939309817524680507)
  ·
    refine ⟨15715849408964726287020761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10477232939309817524680507 15715849408964726287020761)
    ·
      refine ⟨11786887056723544715265571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15715849408964726287020761 11786887056723544715265571)
      ·
        refine ⟨17680330585085317072898357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11786887056723544715265571 17680330585085317072898357)
        ·
          refine ⟨1657530992351748475584221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17680330585085317072898357 1657530992351748475584221)
          ·
            refine ⟨621574122131905678344083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1657530992351748475584221 621574122131905678344083)
            ·
              refine ⟨932361183197858517516125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621574122131905678344083 932361183197858517516125)
              ·
                refine ⟨349635443699196944068547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932361183197858517516125 349635443699196944068547)
                ·
                  refine ⟨524453165548795416102821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349635443699196944068547 524453165548795416102821)
                  ·
                    refine ⟨98334968540399140519279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524453165548795416102821 98334968540399140519279)
                    ·
                      rfl

theorem cell23_574520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_574520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574520 prefixEnd_574520 := by exact prefixLift 574520
  have htrace : WordTrace (prefixWord ++ tailWord_574520) baseStart_574520 baseEnd_574520 := by
    simpa [prefixWord, tailWord_574520, baseEnd_574520] using wordTrace_append hprefix tailTrace_574520
  have hstable : (prefixWord ++ tailWord_574520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574520).length < 2 ^ (prefixWord ++ tailWord_574520).sum := by decide
  have hdescent : baseEnd_574520 < baseStart_574520 := by decide
  rcases family_descends (prefixWord ++ tailWord_574520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574550 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_574550 : Nat := 118140960795 + 574550 * 2 ^ 59
def prefixEnd_574550 : Nat := 4983230072969 + 3 ^ 40 * 574550 * 2
def baseEnd_574550 : Nat := 32780034448981367131411

theorem tailTrace_574550 : CollatzResearch.WordTrace tailWord_574550 prefixEnd_574550 32780034448981367131411 := by
  unfold tailWord_574550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309722504281934385809569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13970373379007300115302069 1309722504281934385809569)
  ·
    refine ⟨982291878211450789357177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1309722504281934385809569 982291878211450789357177)
    ·
      refine ⟨736718908658588092017883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 982291878211450789357177 736718908658588092017883)
      ·
        refine ⟨1105078362987882138026825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736718908658588092017883 1105078362987882138026825)
        ·
          refine ⟨828808772240911603520119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105078362987882138026825 828808772240911603520119)
          ·
            refine ⟨1243213158361367405280179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828808772240911603520119 1243213158361367405280179)
            ·
              refine ⟨1864819737542051107920269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243213158361367405280179 1864819737542051107920269)
              ·
                refine ⟨699307401578269165470101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1864819737542051107920269 699307401578269165470101)
                ·
                  refine ⟨32780034448981367131411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 699307401578269165470101 32780034448981367131411)
                  ·
                    rfl

theorem cell23_574550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_574550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574550 prefixEnd_574550 := by exact prefixLift 574550
  have htrace : WordTrace (prefixWord ++ tailWord_574550) baseStart_574550 baseEnd_574550 := by
    simpa [prefixWord, tailWord_574550, baseEnd_574550] using wordTrace_append hprefix tailTrace_574550
  have hstable : (prefixWord ++ tailWord_574550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574550).length < 2 ^ (prefixWord ++ tailWord_574550).sum := by decide
  have hdescent : baseEnd_574550 < baseStart_574550 := by decide
  rcases family_descends (prefixWord ++ tailWord_574550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574559 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 1, 6]
def baseStart_574559 : Nat := 118140960795 + 574559 * 2 ^ 59
def prefixEnd_574559 : Nat := 4983230072969 + 3 ^ 40 * 574559 * 2
def baseEnd_574559 : Nat := 98341643788907589656719

theorem tailTrace_574559 : CollatzResearch.WordTrace tailWord_574559 prefixEnd_574559 98341643788907589656719 := by
  unfold tailWord_574559
  simp only [CollatzResearch.WordTrace]
  refine ⟨20955888325478344710030731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13970592216985563140020487 20955888325478344710030731)
  ·
    refine ⟨31433832488217517065046097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20955888325478344710030731 31433832488217517065046097)
    ·
      refine ⟨23575374366163137798784573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31433832488217517065046097 23575374366163137798784573)
      ·
        refine ⟨8840765387311176674544215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23575374366163137798784573 8840765387311176674544215)
        ·
          refine ⟨13261148080966765011816323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8840765387311176674544215 13261148080966765011816323)
          ·
            refine ⟨19891722121450147517724485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13261148080966765011816323 19891722121450147517724485)
            ·
              refine ⟨3729697897771902659573341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19891722121450147517724485 3729697897771902659573341)
              ·
                refine ⟨1398636711664463497340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3729697897771902659573341 1398636711664463497340003)
                ·
                  refine ⟨2097955067496695246010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398636711664463497340003 2097955067496695246010005)
                  ·
                    refine ⟨98341643788907589656719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2097955067496695246010005 98341643788907589656719)
                    ·
                      rfl

theorem cell23_574559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_574559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574559 prefixEnd_574559 := by exact prefixLift 574559
  have htrace : WordTrace (prefixWord ++ tailWord_574559) baseStart_574559 baseEnd_574559 := by
    simpa [prefixWord, tailWord_574559, baseEnd_574559] using wordTrace_append hprefix tailTrace_574559
  have hstable : (prefixWord ++ tailWord_574559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574559).length < 2 ^ (prefixWord ++ tailWord_574559).sum := by decide
  have hdescent : baseEnd_574559 < baseStart_574559 := by decide
  rcases family_descends (prefixWord ++ tailWord_574559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574570 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_574570 : Nat := 118140960795 + 574570 * 2 ^ 59
def prefixEnd_574570 : Nat := 4983230072969 + 3 ^ 40 * 574570 * 2
def baseEnd_574570 : Nat := 295030579653922225932607

theorem tailTrace_574570 : CollatzResearch.WordTrace tailWord_574570 prefixEnd_574570 295030579653922225932607 := by
  unfold tailWord_574570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239072382109623397170291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13970859685625662392454109 5239072382109623397170291)
  ·
    refine ⟨7858608573164435095755437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239072382109623397170291 7858608573164435095755437)
    ·
      refine ⟨2946978214936663160908289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7858608573164435095755437 2946978214936663160908289)
      ·
        refine ⟨2210233661202497370681217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2946978214936663160908289 2210233661202497370681217)
        ·
          refine ⟨1657675245901873028010913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210233661202497370681217 1657675245901873028010913)
          ·
            refine ⟨1243256434426404771008185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657675245901873028010913 1243256434426404771008185)
            ·
              refine ⟨932442325819803578256139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243256434426404771008185 932442325819803578256139)
              ·
                refine ⟨1398663488729705367384209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932442325819803578256139 1398663488729705367384209)
                ·
                  refine ⟨1048997616547279025538157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1398663488729705367384209 1048997616547279025538157)
                  ·
                    refine ⟨393374106205229634576809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1048997616547279025538157 393374106205229634576809)
                    ·
                      refine ⟨295030579653922225932607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393374106205229634576809 295030579653922225932607)
                      ·
                        rfl

theorem cell23_574570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_574570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574570 prefixEnd_574570 := by exact prefixLift 574570
  have htrace : WordTrace (prefixWord ++ tailWord_574570) baseStart_574570 baseEnd_574570 := by
    simpa [prefixWord, tailWord_574570, baseEnd_574570] using wordTrace_append hprefix tailTrace_574570
  have hstable : (prefixWord ++ tailWord_574570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574570).length < 2 ^ (prefixWord ++ tailWord_574570).sum := by decide
  have hdescent : baseEnd_574570 < baseStart_574570 := by decide
  rcases family_descends (prefixWord ++ tailWord_574570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574583 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_574583 : Nat := 118140960795 + 574583 * 2 ^ 59
def prefixEnd_574583 : Nat := 4983230072969 + 3 ^ 40 * 574583 * 2
def baseEnd_574583 : Nat := 295037254902430675070047

theorem tailTrace_574583 : CollatzResearch.WordTrace tailWord_574583 prefixEnd_574583 295037254902430675070047 := by
  unfold tailWord_574583
  simp only [CollatzResearch.WordTrace]
  refine ⟨20956763677391396808904403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13971175784927597872602935 20956763677391396808904403)
  ·
    refine ⟨31435145516087095213356605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20956763677391396808904403 31435145516087095213356605)
    ·
      refine ⟨11788179568532660705008727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31435145516087095213356605 11788179568532660705008727)
      ·
        refine ⟨17682269352798991057513091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788179568532660705008727 17682269352798991057513091)
        ·
          refine ⟨26523404029198486586269637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17682269352798991057513091 26523404029198486586269637)
          ·
            refine ⟨4973138255474716234925557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26523404029198486586269637 4973138255474716234925557)
            ·
              refine ⟨466231711450754647024271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4973138255474716234925557 466231711450754647024271)
              ·
                refine ⟨699347567176131970536407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466231711450754647024271 699347567176131970536407)
                ·
                  refine ⟨1049021350764197955804611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699347567176131970536407 1049021350764197955804611)
                  ·
                    refine ⟨1573532026146296933706917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1049021350764197955804611 1573532026146296933706917)
                    ·
                      refine ⟨295037254902430675070047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1573532026146296933706917 295037254902430675070047)
                      ·
                        rfl

theorem cell23_574583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_574583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574583 prefixEnd_574583 := by exact prefixLift 574583
  have htrace : WordTrace (prefixWord ++ tailWord_574583) baseStart_574583 baseEnd_574583 := by
    simpa [prefixWord, tailWord_574583, baseEnd_574583] using wordTrace_append hprefix tailTrace_574583
  have hstable : (prefixWord ++ tailWord_574583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574583).length < 2 ^ (prefixWord ++ tailWord_574583).sum := by decide
  have hdescent : baseEnd_574583 < baseStart_574583 := by decide
  rcases family_descends (prefixWord ++ tailWord_574583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574593 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_574593 : Nat := 118140960795 + 574593 * 2 ^ 59
def prefixEnd_574593 : Nat := 4983230072969 + 3 ^ 40 * 574593 * 2
def baseEnd_574593 : Nat := 98347463236325211981667

theorem tailTrace_574593 : CollatzResearch.WordTrace tailWord_574593 prefixEnd_574593 98347463236325211981667 := by
  unfold tailWord_574593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20957128407355168516768433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13971418938236779011178955 20957128407355168516768433)
  ·
    refine ⟨15717846305516376387576325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20957128407355168516768433 15717846305516376387576325)
    ·
      refine ⟨2947096182284320572670561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15717846305516376387576325 2947096182284320572670561)
      ·
        refine ⟨2210322136713240429502921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2947096182284320572670561 2210322136713240429502921)
        ·
          refine ⟨1657741602534930322127191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210322136713240429502921 1657741602534930322127191)
          ·
            refine ⟨2486612403802395483190787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657741602534930322127191 2486612403802395483190787)
            ·
              refine ⟨3729918605703593224786181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486612403802395483190787 3729918605703593224786181)
              ·
                refine ⟨699359738569423729647409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3729918605703593224786181 699359738569423729647409)
                ·
                  refine ⟨524519803927067797235557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699359738569423729647409 524519803927067797235557)
                  ·
                    refine ⟨98347463236325211981667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524519803927067797235557 98347463236325211981667)
                    ·
                      rfl

theorem cell23_574593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_574593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574593 prefixEnd_574593 := by exact prefixLift 574593
  have htrace : WordTrace (prefixWord ++ tailWord_574593) baseStart_574593 baseEnd_574593 := by
    simpa [prefixWord, tailWord_574593, baseEnd_574593] using wordTrace_append hprefix tailTrace_574593
  have hstable : (prefixWord ++ tailWord_574593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574593).length < 2 ^ (prefixWord ++ tailWord_574593).sum := by decide
  have hdescent : baseEnd_574593 < baseStart_574593 := by decide
  rcases family_descends (prefixWord ++ tailWord_574593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574606 : List Nat := [4, 1, 1, 3, 2, 1, 3, 8]
def baseStart_574606 : Nat := 118140960795 + 574606 * 2 ^ 59
def prefixEnd_574606 : Nat := 4983230072969 + 3 ^ 40 * 574606 * 2
def baseEnd_574606 : Nat := 10927743146573484632683

theorem tailTrace_574606 : CollatzResearch.WordTrace tailWord_574606 prefixEnd_574606 10927743146573484632683 := by
  unfold tailWord_574606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619700319538508967123959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13971735037538714491327781 2619700319538508967123959)
  ·
    refine ⟨3929550479307763450685939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2619700319538508967123959 3929550479307763450685939)
    ·
      refine ⟨5894325718961645176028909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929550479307763450685939 5894325718961645176028909)
      ·
        refine ⟨2210372144610616941010841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5894325718961645176028909 2210372144610616941010841)
        ·
          refine ⟨1657779108457962705758131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210372144610616941010841 1657779108457962705758131)
          ·
            refine ⟨2486668662686944058637197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657779108457962705758131 2486668662686944058637197)
            ·
              refine ⟨932500748507604021988949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2486668662686944058637197 932500748507604021988949)
              ·
                refine ⟨10927743146573484632683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 932500748507604021988949 10927743146573484632683)
                ·
                  rfl

theorem cell23_574606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_574606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574606 prefixEnd_574606 := by exact prefixLift 574606
  have htrace : WordTrace (prefixWord ++ tailWord_574606) baseStart_574606 baseEnd_574606 := by
    simpa [prefixWord, tailWord_574606, baseEnd_574606] using wordTrace_append hprefix tailTrace_574606
  have hstable : (prefixWord ++ tailWord_574606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574606).length < 2 ^ (prefixWord ++ tailWord_574606).sum := by decide
  have hdescent : baseEnd_574606 < baseStart_574606 := by decide
  rcases family_descends (prefixWord ++ tailWord_574606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574623 : List Nat := [1, 1, 2, 6, 2, 1, 3, 7]
def baseStart_574623 : Nat := 118140960795 + 574623 * 2 ^ 59
def prefixEnd_574623 : Nat := 4983230072969 + 3 ^ 40 * 574623 * 2
def baseEnd_574623 : Nat := 10928066449207796984069

theorem tailTrace_574623 : CollatzResearch.WordTrace tailWord_574623 prefixEnd_574623 10928066449207796984069 := by
  unfold tailWord_574623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958222597246483640360523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13972148398164322426907015 20958222597246483640360523)
  ·
    refine ⟨31437333895869725460540785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20958222597246483640360523 31437333895869725460540785)
    ·
      refine ⟨23578000421902294095405589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31437333895869725460540785 23578000421902294095405589)
      ·
        refine ⟨1105218769776670035722137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23578000421902294095405589 1105218769776670035722137)
        ·
          refine ⟨828914077332502526791603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1105218769776670035722137 828914077332502526791603)
          ·
            refine ⟨1243371115998753790187405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828914077332502526791603 1243371115998753790187405)
            ·
              refine ⟨466264168499532671320277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243371115998753790187405 466264168499532671320277)
              ·
                refine ⟨10928066449207796984069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 466264168499532671320277 10928066449207796984069)
                ·
                  rfl

theorem cell23_574623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 7].length) (baseStart_574623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574623 prefixEnd_574623 := by exact prefixLift 574623
  have htrace : WordTrace (prefixWord ++ tailWord_574623) baseStart_574623 baseEnd_574623 := by
    simpa [prefixWord, tailWord_574623, baseEnd_574623] using wordTrace_append hprefix tailTrace_574623
  have hstable : (prefixWord ++ tailWord_574623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574623).length < 2 ^ (prefixWord ++ tailWord_574623).sum := by decide
  have hdescent : baseEnd_574623 < baseStart_574623 := by decide
  rcases family_descends (prefixWord ++ tailWord_574623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574634 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_574634 : Nat := 118140960795 + 574634 * 2 ^ 59
def prefixEnd_574634 : Nat := 4983230072969 + 3 ^ 40 * 574634 * 2
def baseEnd_574634 : Nat := 295063442415809975532313

theorem tailTrace_574634 : CollatzResearch.WordTrace tailWord_574634 prefixEnd_574634 295063442415809975532313 := by
  unfold tailWord_574634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239655950051658129752739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13972415866804421679340637 5239655950051658129752739)
  ·
    refine ⟨7859483925077487194629109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239655950051658129752739 7859483925077487194629109)
    ·
      refine ⟨736826617976014424496479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7859483925077487194629109 736826617976014424496479)
      ·
        refine ⟨1105239926964021636744719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736826617976014424496479 1105239926964021636744719)
        ·
          refine ⟨1657859890446032455117079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105239926964021636744719 1657859890446032455117079)
          ·
            refine ⟨2486789835669048682675619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657859890446032455117079 2486789835669048682675619)
            ·
              refine ⟨3730184753503573024013429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486789835669048682675619 3730184753503573024013429)
              ·
                refine ⟨349704820640959971001259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3730184753503573024013429 349704820640959971001259)
                ·
                  refine ⟨524557230961439956501889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349704820640959971001259 524557230961439956501889)
                  ·
                    refine ⟨393417923221079967376417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524557230961439956501889 393417923221079967376417)
                    ·
                      refine ⟨295063442415809975532313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393417923221079967376417 295063442415809975532313)
                      ·
                        rfl

theorem cell23_574634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_574634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574634 prefixEnd_574634 := by exact prefixLift 574634
  have htrace : WordTrace (prefixWord ++ tailWord_574634) baseStart_574634 baseEnd_574634 := by
    simpa [prefixWord, tailWord_574634, baseEnd_574634] using wordTrace_append hprefix tailTrace_574634
  have hstable : (prefixWord ++ tailWord_574634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574634).length < 2 ^ (prefixWord ++ tailWord_574634).sum := by decide
  have hdescent : baseEnd_574634 < baseStart_574634 := by decide
  rcases family_descends (prefixWord ++ tailWord_574634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574659 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5]
def baseStart_574659 : Nat := 118140960795 + 574659 * 2 ^ 59
def prefixEnd_574659 : Nat := 4983230072969 + 3 ^ 40 * 574659 * 2
def baseEnd_574659 : Nat := 295076279432172377719697

theorem tailTrace_574659 : CollatzResearch.WordTrace tailWord_574659 prefixEnd_574659 295076279432172377719697 := by
  unfold tailWord_574659
  simp only [CollatzResearch.WordTrace]
  refine ⟨20959535625116061788671031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13973023750077374525780687 20959535625116061788671031)
  ·
    refine ⟨31439303437674092683006547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20959535625116061788671031 31439303437674092683006547)
    ·
      refine ⟨47158955156511139024509821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31439303437674092683006547 47158955156511139024509821)
      ·
        refine ⟨17684608183691677134191183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47158955156511139024509821 17684608183691677134191183)
        ·
          refine ⟨26526912275537515701286775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17684608183691677134191183 26526912275537515701286775)
          ·
            refine ⟨39790368413306273551930163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26526912275537515701286775 39790368413306273551930163)
            ·
              refine ⟨59685552619959410327895245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39790368413306273551930163 59685552619959410327895245)
              ·
                refine ⟨22382082232484778872960717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59685552619959410327895245 22382082232484778872960717)
                ·
                  refine ⟨8393280837181792077360269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22382082232484778872960717 8393280837181792077360269)
                  ·
                    refine ⟨3147480313943172029010101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8393280837181792077360269 3147480313943172029010101)
                    ·
                      refine ⟨295076279432172377719697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3147480313943172029010101 295076279432172377719697)
                      ·
                        rfl

theorem cell23_574659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_574659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574659 prefixEnd_574659 := by exact prefixLift 574659
  have htrace : WordTrace (prefixWord ++ tailWord_574659) baseStart_574659 baseEnd_574659 := by
    simpa [prefixWord, tailWord_574659, baseEnd_574659] using wordTrace_append hprefix tailTrace_574659
  have hstable : (prefixWord ++ tailWord_574659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574659).length < 2 ^ (prefixWord ++ tailWord_574659).sum := by decide
  have hdescent : baseEnd_574659 < baseStart_574659 := by decide
  rcases family_descends (prefixWord ++ tailWord_574659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574666 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_574666 : Nat := 118140960795 + 574666 * 2 ^ 59
def prefixEnd_574666 : Nat := 4983230072969 + 3 ^ 40 * 574666 * 2
def baseEnd_574666 : Nat := 98359957932251283444055

theorem tailTrace_574666 : CollatzResearch.WordTrace tailWord_574666 prefixEnd_574666 98359957932251283444055 := by
  unfold tailWord_574666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239947734022675496043963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13973193957393801322783901 5239947734022675496043963)
  ·
    refine ⟨7859921601034013244065945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239947734022675496043963 7859921601034013244065945)
    ·
      refine ⟨5894941200775509933049459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7859921601034013244065945 5894941200775509933049459)
      ·
        refine ⟨8842411801163264899574189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5894941200775509933049459 8842411801163264899574189)
        ·
          refine ⟨3315904425436224337340321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8842411801163264899574189 3315904425436224337340321)
          ·
            refine ⟨2486928319077168253005241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315904425436224337340321 2486928319077168253005241)
            ·
              refine ⟨1865196239307876189753931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486928319077168253005241 1865196239307876189753931)
              ·
                refine ⟨2797794358961814284630897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865196239307876189753931 2797794358961814284630897)
                ·
                  refine ⟨2098345769221360713473173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797794358961814284630897 2098345769221360713473173)
                  ·
                    refine ⟨98359957932251283444055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2098345769221360713473173 98359957932251283444055)
                    ·
                      rfl

theorem cell23_574666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_574666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574666 prefixEnd_574666 := by exact prefixLift 574666
  have htrace : WordTrace (prefixWord ++ tailWord_574666) baseStart_574666 baseEnd_574666 := by
    simpa [prefixWord, tailWord_574666, baseEnd_574666] using wordTrace_append hprefix tailTrace_574666
  have hstable : (prefixWord ++ tailWord_574666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574666).length < 2 ^ (prefixWord ++ tailWord_574666).sum := by decide
  have hdescent : baseEnd_574666 < baseStart_574666 := by decide
  rcases family_descends (prefixWord ++ tailWord_574666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574677 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_574677 : Nat := 118140960795 + 574677 * 2 ^ 59
def prefixEnd_574677 : Nat := 4983230072969 + 3 ^ 40 * 574677 * 2
def baseEnd_574677 : Nat := 295085522083953307294615

theorem tailTrace_574677 : CollatzResearch.WordTrace tailWord_574677 prefixEnd_574677 295085522083953307294615 := by
  unfold tailWord_574677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20960192139050850862826285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13973461426033900575217523 20960192139050850862826285)
  ·
    refine ⟨7860072052144069073559857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20960192139050850862826285 7860072052144069073559857)
    ·
      refine ⟨5895054039108051805169893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7860072052144069073559857 5895054039108051805169893)
      ·
        refine ⟨1105322632332759713469355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5895054039108051805169893 1105322632332759713469355)
        ·
          refine ⟨1657983948499139570204033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105322632332759713469355 1657983948499139570204033)
          ·
            refine ⟨1243487961374354677653025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657983948499139570204033 1243487961374354677653025)
            ·
              refine ⟨932615971030766008239769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243487961374354677653025 932615971030766008239769)
              ·
                refine ⟨699461978273074506179827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932615971030766008239769 699461978273074506179827)
                ·
                  refine ⟨1049192967409611759269741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699461978273074506179827 1049192967409611759269741)
                  ·
                    refine ⟨393447362778604409726153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049192967409611759269741 393447362778604409726153)
                    ·
                      refine ⟨295085522083953307294615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393447362778604409726153 295085522083953307294615)
                      ·
                        rfl

theorem cell23_574677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_574677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574677 prefixEnd_574677 := by exact prefixLift 574677
  have htrace : WordTrace (prefixWord ++ tailWord_574677) baseStart_574677 baseEnd_574677 := by
    simpa [prefixWord, tailWord_574677, baseEnd_574677] using wordTrace_append hprefix tailTrace_574677
  have hstable : (prefixWord ++ tailWord_574677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574677).length < 2 ^ (prefixWord ++ tailWord_574677).sum := by decide
  have hdescent : baseEnd_574677 < baseStart_574677 := by decide
  rcases family_descends (prefixWord ++ tailWord_574677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574693 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_574693 : Nat := 118140960795 + 574693 * 2 ^ 59
def prefixEnd_574693 : Nat := 4983230072969 + 3 ^ 40 * 574693 * 2
def baseEnd_574693 : Nat := 295093737774425244694541

theorem tailTrace_574693 : CollatzResearch.WordTrace tailWord_574693 prefixEnd_574693 295093737774425244694541 := by
  unfold tailWord_574693
  simp only [CollatzResearch.WordTrace]
  refine ⟨20960775706992885595408733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13973850471328590396939155 20960775706992885595408733)
  ·
    refine ⟨7860290890122332098278275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20960775706992885595408733 7860290890122332098278275)
    ·
      refine ⟨11790436335183498147417413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860290890122332098278275 11790436335183498147417413)
      ·
        refine ⟨2210706812846905902640765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11790436335183498147417413 2210706812846905902640765)
        ·
          refine ⟨829015054817589713490287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2210706812846905902640765 829015054817589713490287)
          ·
            refine ⟨1243522582226384570235431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829015054817589713490287 1243522582226384570235431)
            ·
              refine ⟨1865283873339576855353147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243522582226384570235431 1865283873339576855353147)
              ·
                refine ⟨2797925810009365283029721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865283873339576855353147 2797925810009365283029721)
                ·
                  refine ⟨2098444357507023962272291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797925810009365283029721 2098444357507023962272291)
                  ·
                    refine ⟨3147666536260535943408437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098444357507023962272291 3147666536260535943408437)
                    ·
                      refine ⟨295093737774425244694541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3147666536260535943408437 295093737774425244694541)
                      ·
                        rfl

theorem cell23_574693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_574693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574693 prefixEnd_574693 := by exact prefixLift 574693
  have htrace : WordTrace (prefixWord ++ tailWord_574693) baseStart_574693 baseEnd_574693 := by
    simpa [prefixWord, tailWord_574693, baseEnd_574693] using wordTrace_append hprefix tailTrace_574693
  have hstable : (prefixWord ++ tailWord_574693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574693).length < 2 ^ (prefixWord ++ tailWord_574693).sum := by decide
  have hdescent : baseEnd_574693 < baseStart_574693 := by decide
  rcases family_descends (prefixWord ++ tailWord_574693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574724 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_574724 : Nat := 118140960795 + 574724 * 2 ^ 59
def prefixEnd_574724 : Nat := 4983230072969 + 3 ^ 40 * 574724 * 2
def baseEnd_574724 : Nat := 295109655674714623406899

theorem tailTrace_574724 : CollatzResearch.WordTrace tailWord_574724 prefixEnd_574724 295109655674714623406899 := by
  unfold tailWord_574724
  simp only [CollatzResearch.WordTrace]
  refine ⟨10480953184940288944893613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13974604246587051926524817 10480953184940288944893613)
  ·
    refine ⟨3930357444352608354335105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10480953184940288944893613 3930357444352608354335105)
    ·
      refine ⟨2947768083264456265751329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3930357444352608354335105 2947768083264456265751329)
      ·
        refine ⟨2210826062448342199313497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2947768083264456265751329 2210826062448342199313497)
        ·
          refine ⟨1658119546836256649485123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210826062448342199313497 1658119546836256649485123)
          ·
            refine ⟨2487179320254384974227685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658119546836256649485123 2487179320254384974227685)
            ·
              refine ⟨466346122547697182667691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2487179320254384974227685 466346122547697182667691)
              ·
                refine ⟨699519183821545774001537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466346122547697182667691 699519183821545774001537)
                ·
                  refine ⟨524639387866159330501153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699519183821545774001537 524639387866159330501153)
                  ·
                    refine ⟨393479540899619497875865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524639387866159330501153 393479540899619497875865)
                    ·
                      refine ⟨295109655674714623406899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393479540899619497875865 295109655674714623406899)
                      ·
                        rfl

theorem cell23_574724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_574724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574724 prefixEnd_574724 := by exact prefixLift 574724
  have htrace : WordTrace (prefixWord ++ tailWord_574724) baseStart_574724 baseEnd_574724 := by
    simpa [prefixWord, tailWord_574724, baseEnd_574724] using wordTrace_append hprefix tailTrace_574724
  have hstable : (prefixWord ++ tailWord_574724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574724).length < 2 ^ (prefixWord ++ tailWord_574724).sum := by decide
  have hdescent : baseEnd_574724 < baseStart_574724 := by decide
  rcases family_descends (prefixWord ++ tailWord_574724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574743 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 2, 5]
def baseStart_574743 : Nat := 118140960795 + 574743 * 2 ^ 59
def prefixEnd_574743 : Nat := 4983230072969 + 3 ^ 40 * 574743 * 2
def baseEnd_574743 : Nat := 98373137269050016356437

theorem tailTrace_574743 : CollatzResearch.WordTrace tailWord_574743 prefixEnd_574743 98373137269050016356437 := by
  unfold tailWord_574743
  simp only [CollatzResearch.WordTrace]
  refine ⟨20962599356811744134728883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13975066237874496089819255 20962599356811744134728883)
  ·
    refine ⟨31443899035217616202093325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20962599356811744134728883 31443899035217616202093325)
    ·
      refine ⟨11791462138206606075784997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31443899035217616202093325 11791462138206606075784997)
      ·
        refine ⟨2210899150913738639209687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11791462138206606075784997 2210899150913738639209687)
        ·
          refine ⟨3316348726370607958814531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210899150913738639209687 3316348726370607958814531)
          ·
            refine ⟨4974523089555911938221797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316348726370607958814531 4974523089555911938221797)
            ·
              refine ⟨932723079291733488416587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4974523089555911938221797 932723079291733488416587)
              ·
                refine ⟨1399084618937600232624881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932723079291733488416587 1399084618937600232624881)
                ·
                  refine ⟨1049313464203200174468661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399084618937600232624881 1049313464203200174468661)
                  ·
                    refine ⟨98373137269050016356437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1049313464203200174468661 98373137269050016356437)
                    ·
                      rfl

theorem cell23_574743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_574743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574743 prefixEnd_574743 := by exact prefixLift 574743
  have htrace : WordTrace (prefixWord ++ tailWord_574743) baseStart_574743 baseEnd_574743 := by
    simpa [prefixWord, tailWord_574743, baseEnd_574743] using wordTrace_append hprefix tailTrace_574743
  have hstable : (prefixWord ++ tailWord_574743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574743).length < 2 ^ (prefixWord ++ tailWord_574743).sum := by decide
  have hdescent : baseEnd_574743 < baseStart_574743 := by decide
  rcases family_descends (prefixWord ++ tailWord_574743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574776 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_574776 : Nat := 118140960795 + 574776 * 2 ^ 59
def prefixEnd_574776 : Nat := 4983230072969 + 3 ^ 40 * 574776 * 2
def baseEnd_574776 : Nat := 295136356668748419956659

theorem tailTrace_574776 : CollatzResearch.WordTrace tailWord_574776 prefixEnd_574776 295136356668748419956659 := by
  unfold tailWord_574776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481901482846095385340091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13975868643794793847120121 10481901482846095385340091)
  ·
    refine ⟨15722852224269143078010137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10481901482846095385340091 15722852224269143078010137)
    ·
      refine ⟨11792139168201857308507603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15722852224269143078010137 11792139168201857308507603)
      ·
        refine ⟨17688208752302785962761405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11792139168201857308507603 17688208752302785962761405)
        ·
          refine ⟨6633078282113544736035527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17688208752302785962761405 6633078282113544736035527)
          ·
            refine ⟨9949617423170317104053291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633078282113544736035527 9949617423170317104053291)
            ·
              refine ⟨14924426134755475656079937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949617423170317104053291 14924426134755475656079937)
              ·
                refine ⟨11193319601066606742059953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14924426134755475656079937 11193319601066606742059953)
                ·
                  refine ⟨8394989700799955056544965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11193319601066606742059953 8394989700799955056544965)
                  ·
                    refine ⟨1574060568899991573102181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8394989700799955056544965 1574060568899991573102181)
                    ·
                      refine ⟨295136356668748419956659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1574060568899991573102181 295136356668748419956659)
                      ·
                        rfl

theorem cell23_574776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_574776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574776 prefixEnd_574776 := by exact prefixLift 574776
  have htrace : WordTrace (prefixWord ++ tailWord_574776) baseStart_574776 baseEnd_574776 := by
    simpa [prefixWord, tailWord_574776, baseEnd_574776] using wordTrace_append hprefix tailTrace_574776
  have hstable : (prefixWord ++ tailWord_574776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574776).length < 2 ^ (prefixWord ++ tailWord_574776).sum := by decide
  have hdescent : baseEnd_574776 < baseStart_574776 := by decide
  rcases family_descends (prefixWord ++ tailWord_574776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574780 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_574780 : Nat := 118140960795 + 574780 * 2 ^ 59
def prefixEnd_574780 : Nat := 4983230072969 + 3 ^ 40 * 574780 * 2
def baseEnd_574780 : Nat := 295138410591366404306641

theorem tailTrace_574780 : CollatzResearch.WordTrace tailWord_574780 prefixEnd_574780 295138410591366404306641 := by
  unfold tailWord_574780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481974428838849726912897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13975965905118466302550529 10481974428838849726912897)
  ·
    refine ⟨7861480821629137295184673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10481974428838849726912897 7861480821629137295184673)
    ·
      refine ⟨5896110616221852971388505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7861480821629137295184673 5896110616221852971388505)
      ·
        refine ⟨4422082962166389728541379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5896110616221852971388505 4422082962166389728541379)
        ·
          refine ⟨6633124443249584592812069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422082962166389728541379 6633124443249584592812069)
          ·
            refine ⟨1243710833109297111152263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6633124443249584592812069 1243710833109297111152263)
            ·
              refine ⟨1865566249663945666728395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243710833109297111152263 1865566249663945666728395)
              ·
                refine ⟨2798349374495918500092593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865566249663945666728395 2798349374495918500092593)
                ·
                  refine ⟨2098762030871938875069445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798349374495918500092593 2098762030871938875069445)
                  ·
                    refine ⟨393517880788488539075521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2098762030871938875069445 393517880788488539075521)
                    ·
                      refine ⟨295138410591366404306641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393517880788488539075521 295138410591366404306641)
                      ·
                        rfl

theorem cell23_574780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_574780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574780 prefixEnd_574780 := by exact prefixLift 574780
  have htrace : WordTrace (prefixWord ++ tailWord_574780) baseStart_574780 baseEnd_574780 := by
    simpa [prefixWord, tailWord_574780, baseEnd_574780] using wordTrace_append hprefix tailTrace_574780
  have hstable : (prefixWord ++ tailWord_574780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574780).length < 2 ^ (prefixWord ++ tailWord_574780).sum := by decide
  have hdescent : baseEnd_574780 < baseStart_574780 := by decide
  rcases family_descends (prefixWord ++ tailWord_574780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574797 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_574797 : Nat := 118140960795 + 574797 * 2 ^ 59
def prefixEnd_574797 : Nat := 4983230072969 + 3 ^ 40 * 574797 * 2
def baseEnd_574797 : Nat := 295147139762492837794063

theorem tailTrace_574797 : CollatzResearch.WordTrace tailWord_574797 prefixEnd_574797 295147139762492837794063 := by
  unfold tailWord_574797
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964568898616111357194645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13976379265744074238129763 20964568898616111357194645)
  ·
    refine ⟨982714167122630219868499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20964568898616111357194645 982714167122630219868499)
    ·
      refine ⟨1474071250683945329802749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982714167122630219868499 1474071250683945329802749)
      ·
        refine ⟨552776719006479498676031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1474071250683945329802749 552776719006479498676031)
        ·
          refine ⟨829165078509719248014047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552776719006479498676031 829165078509719248014047)
          ·
            refine ⟨1243747617764578872021071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829165078509719248014047 1243747617764578872021071)
            ·
              refine ⟨1865621426646868308031607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243747617764578872021071 1865621426646868308031607)
              ·
                refine ⟨2798432139970302462047411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865621426646868308031607 2798432139970302462047411)
                ·
                  refine ⟨4197648209955453693071117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798432139970302462047411 4197648209955453693071117)
                  ·
                    refine ⟨1574118078733295134901669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4197648209955453693071117 1574118078733295134901669)
                    ·
                      refine ⟨295147139762492837794063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1574118078733295134901669 295147139762492837794063)
                      ·
                        rfl

theorem cell23_574797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_574797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574797 prefixEnd_574797 := by exact prefixLift 574797
  have htrace : WordTrace (prefixWord ++ tailWord_574797) baseStart_574797 baseEnd_574797 := by
    simpa [prefixWord, tailWord_574797, baseEnd_574797] using wordTrace_append hprefix tailTrace_574797
  have hstable : (prefixWord ++ tailWord_574797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574797).length < 2 ^ (prefixWord ++ tailWord_574797).sum := by decide
  have hdescent : baseEnd_574797 < baseStart_574797 := by decide
  rcases family_descends (prefixWord ++ tailWord_574797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574807 : List Nat := [1, 1, 3, 2, 3, 3, 2, 3, 1, 4]
def baseStart_574807 : Nat := 118140960795 + 574807 * 2 ^ 59
def prefixEnd_574807 : Nat := 4983230072969 + 3 ^ 40 * 574807 * 2
def baseEnd_574807 : Nat := 98384091523012599556339

theorem tailTrace_574807 : CollatzResearch.WordTrace tailWord_574807 prefixEnd_574807 98384091523012599556339 := by
  unfold tailWord_574807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964933628579883065058675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13976622419053255376705783 20964933628579883065058675)
  ·
    refine ⟨31447400442869824597588013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20964933628579883065058675 31447400442869824597588013)
    ·
      refine ⟨11792775166076184224095505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31447400442869824597588013 11792775166076184224095505)
      ·
        refine ⟨8844581374557138168071629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11792775166076184224095505 8844581374557138168071629)
        ·
          refine ⟨3316718015458926813026861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8844581374557138168071629 3316718015458926813026861)
          ·
            refine ⟨1243769255797097554885073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3316718015458926813026861 1243769255797097554885073)
            ·
              refine ⟨932826941847823166163805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243769255797097554885073 932826941847823166163805)
              ·
                refine ⟨349810103192933687311427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932826941847823166163805 349810103192933687311427)
                ·
                  refine ⟨524715154789400530967141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349810103192933687311427 524715154789400530967141)
                  ·
                    refine ⟨98384091523012599556339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524715154789400530967141 98384091523012599556339)
                    ·
                      rfl

theorem cell23_574807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_574807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574807 prefixEnd_574807 := by exact prefixLift 574807
  have htrace : WordTrace (prefixWord ++ tailWord_574807) baseStart_574807 baseEnd_574807 := by
    simpa [prefixWord, tailWord_574807, baseEnd_574807] using wordTrace_append hprefix tailTrace_574807
  have hstable : (prefixWord ++ tailWord_574807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574807).length < 2 ^ (prefixWord ++ tailWord_574807).sum := by decide
  have hdescent : baseEnd_574807 < baseStart_574807 := by decide
  rcases family_descends (prefixWord ++ tailWord_574807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574820 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 6]
def baseStart_574820 : Nat := 118140960795 + 574820 * 2 ^ 59
def prefixEnd_574820 : Nat := 4983230072969 + 3 ^ 40 * 574820 * 2
def baseEnd_574820 : Nat := 32795438868616249756273

theorem tailTrace_574820 : CollatzResearch.WordTrace tailWord_574820 prefixEnd_574820 32795438868616249756273 := by
  unfold tailWord_574820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482703888766393142640957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13976938518355190856854609 10482703888766393142640957)
  ·
    refine ⟨3931013958287397428490359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10482703888766393142640957 3931013958287397428490359)
    ·
      refine ⟨5896520937431096142735539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3931013958287397428490359 5896520937431096142735539)
      ·
        refine ⟨8844781406146644214103309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5896520937431096142735539 8844781406146644214103309)
        ·
          refine ⟨3316793027304991580288741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8844781406146644214103309 3316793027304991580288741)
          ·
            refine ⟨621898692619685921304139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3316793027304991580288741 621898692619685921304139)
            ·
              refine ⟨932848038929528881956209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621898692619685921304139 932848038929528881956209)
              ·
                refine ⟨699636029197146661467157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932848038929528881956209 699636029197146661467157)
                ·
                  refine ⟨32795438868616249756273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 699636029197146661467157 32795438868616249756273)
                  ·
                    rfl

theorem cell23_574820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_574820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574820 prefixEnd_574820 := by exact prefixLift 574820
  have htrace : WordTrace (prefixWord ++ tailWord_574820) baseStart_574820 baseEnd_574820 := by
    simpa [prefixWord, tailWord_574820, baseEnd_574820] using wordTrace_append hprefix tailTrace_574820
  have hstable : (prefixWord ++ tailWord_574820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574820).length < 2 ^ (prefixWord ++ tailWord_574820).sum := by decide
  have hdescent : baseEnd_574820 < baseStart_574820 := by decide
  rcases family_descends (prefixWord ++ tailWord_574820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574837 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 6]
def baseStart_574837 : Nat := 118140960795 + 574837 * 2 ^ 59
def prefixEnd_574837 : Nat := 4983230072969 + 3 ^ 40 * 574837 * 2
def baseEnd_574837 : Nat := 32796408776519186810431

theorem tailTrace_574837 : CollatzResearch.WordTrace tailWord_574837 prefixEnd_574837 32796408776519186810431 := by
  unfold tailWord_574837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966027818471198188650765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13977351878980798792433843 20966027818471198188650765)
  ·
    refine ⟨7862260431926699320744037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20966027818471198188650765 7862260431926699320744037)
    ·
      refine ⟨1474173830986256122639507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7862260431926699320744037 1474173830986256122639507)
      ·
        refine ⟨2211260746479384183959261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474173830986256122639507 2211260746479384183959261)
        ·
          refine ⟨829222779929769068984723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2211260746479384183959261 829222779929769068984723)
          ·
            refine ⟨1243834169894653603477085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829222779929769068984723 1243834169894653603477085)
            ·
              refine ⟨466437813710495101303907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243834169894653603477085 466437813710495101303907)
              ·
                refine ⟨699656720565742651955861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466437813710495101303907 699656720565742651955861)
                ·
                  refine ⟨32796408776519186810431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 699656720565742651955861 32796408776519186810431)
                  ·
                    rfl

theorem cell23_574837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_574837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574837 prefixEnd_574837 := by exact prefixLift 574837
  have htrace : WordTrace (prefixWord ++ tailWord_574837) baseStart_574837 baseEnd_574837 := by
    simpa [prefixWord, tailWord_574837, baseEnd_574837] using wordTrace_append hprefix tailTrace_574837
  have hstable : (prefixWord ++ tailWord_574837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574837).length < 2 ^ (prefixWord ++ tailWord_574837).sum := by decide
  have hdescent : baseEnd_574837 < baseStart_574837 := by decide
  rcases family_descends (prefixWord ++ tailWord_574837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574853 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_574853 : Nat := 118140960795 + 574853 * 2 ^ 59
def prefixEnd_574853 : Nat := 4983230072969 + 3 ^ 40 * 574853 * 2
def baseEnd_574853 : Nat := 295175894679144618693805

theorem tailTrace_574853 : CollatzResearch.WordTrace tailWord_574853 prefixEnd_574853 295175894679144618693805 := by
  unfold tailWord_574853
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966611386413232921233213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13977740924275488614155475 20966611386413232921233213)
  ·
    refine ⟨7862479269904962345462455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20966611386413232921233213 7862479269904962345462455)
    ·
      refine ⟨11793718904857443518193683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7862479269904962345462455 11793718904857443518193683)
      ·
        refine ⟨17690578357286165277290525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11793718904857443518193683 17690578357286165277290525)
        ·
          refine ⟨6633966883982311978983947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17690578357286165277290525 6633966883982311978983947)
          ·
            refine ⟨9950950325973467968475921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633966883982311978983947 9950950325973467968475921)
            ·
              refine ⟨7463212744480100976356941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9950950325973467968475921 7463212744480100976356941)
              ·
                refine ⟨2798704779180037866133853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7463212744480100976356941 2798704779180037866133853)
                ·
                  refine ⟨1049514292192514199800195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2798704779180037866133853 1049514292192514199800195)
                  ·
                    refine ⟨1574271438288771299700293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1049514292192514199800195 1574271438288771299700293)
                    ·
                      refine ⟨295175894679144618693805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1574271438288771299700293 295175894679144618693805)
                      ·
                        rfl

theorem cell23_574853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_574853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574853 prefixEnd_574853 := by exact prefixLift 574853
  have htrace : WordTrace (prefixWord ++ tailWord_574853) baseStart_574853 baseEnd_574853 := by
    simpa [prefixWord, tailWord_574853, baseEnd_574853] using wordTrace_append hprefix tailTrace_574853
  have hstable : (prefixWord ++ tailWord_574853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574853).length < 2 ^ (prefixWord ++ tailWord_574853).sum := by decide
  have hdescent : baseEnd_574853 < baseStart_574853 := by decide
  rcases family_descends (prefixWord ++ tailWord_574853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574873 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_574873 : Nat := 118140960795 + 574873 * 2 ^ 59
def prefixEnd_574873 : Nat := 4983230072969 + 3 ^ 40 * 574873 * 2
def baseEnd_574873 : Nat := 295186164292234540443713

theorem tailTrace_574873 : CollatzResearch.WordTrace tailWord_574873 prefixEnd_574873 295186164292234540443713 := by
  unfold tailWord_574873
  simp only [CollatzResearch.WordTrace]
  refine ⟨20967340846340776336961273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13978227230893850891307515 20967340846340776336961273)
  ·
    refine ⟨15725505634755582252720955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20967340846340776336961273 15725505634755582252720955)
    ·
      refine ⟨23588258452133373379081433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15725505634755582252720955 23588258452133373379081433)
      ·
        refine ⟨17691193839100030034311075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23588258452133373379081433 17691193839100030034311075)
        ·
          refine ⟨26536790758650045051466613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17691193839100030034311075 26536790758650045051466613)
          ·
            refine ⟨2487824133623441723574995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26536790758650045051466613 2487824133623441723574995)
            ·
              refine ⟨3731736200435162585362493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487824133623441723574995 3731736200435162585362493)
              ·
                refine ⟨1399401075163185969510935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3731736200435162585362493 1399401075163185969510935)
                ·
                  refine ⟨2099101612744778954266403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399401075163185969510935 2099101612744778954266403)
                  ·
                    refine ⟨3148652419117168431399605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099101612744778954266403 3148652419117168431399605)
                    ·
                      refine ⟨295186164292234540443713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3148652419117168431399605 295186164292234540443713)
                      ·
                        rfl

theorem cell23_574873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_574873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574873 prefixEnd_574873 := by exact prefixLift 574873
  have htrace : WordTrace (prefixWord ++ tailWord_574873) baseStart_574873 baseEnd_574873 := by
    simpa [prefixWord, tailWord_574873, baseEnd_574873] using wordTrace_append hprefix tailTrace_574873
  have hstable : (prefixWord ++ tailWord_574873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574873).length < 2 ^ (prefixWord ++ tailWord_574873).sum := by decide
  have hdescent : baseEnd_574873 < baseStart_574873 := by decide
  rcases family_descends (prefixWord ++ tailWord_574873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574880 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_574880 : Nat := 118140960795 + 574880 * 2 ^ 59
def prefixEnd_574880 : Nat := 4983230072969 + 3 ^ 40 * 574880 * 2
def baseEnd_574880 : Nat := 98396586218938671018727

theorem tailTrace_574880 : CollatzResearch.WordTrace tailWord_574880 prefixEnd_574880 98396586218938671018727 := by
  unfold tailWord_574880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10483798078657708266233047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13978397438210277688310729 10483798078657708266233047)
  ·
    refine ⟨15725697117986562399349571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10483798078657708266233047 15725697117986562399349571)
    ·
      refine ⟨23588545676979843599024357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15725697117986562399349571 23588545676979843599024357)
      ·
        refine ⟨4422852314433720674817067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23588545676979843599024357 4422852314433720674817067)
        ·
          refine ⟨6634278471650581012225601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422852314433720674817067 6634278471650581012225601)
          ·
            refine ⟨4975708853737935759169201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6634278471650581012225601 4975708853737935759169201)
            ·
              refine ⟨3731781640303451819376901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4975708853737935759169201 3731781640303451819376901)
              ·
                refine ⟨699709057556897216133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3731781640303451819376901 699709057556897216133169)
                ·
                  refine ⟨524781793167672912099877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699709057556897216133169 524781793167672912099877)
                  ·
                    refine ⟨98396586218938671018727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524781793167672912099877 98396586218938671018727)
                    ·
                      rfl

theorem cell23_574880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_574880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574880 prefixEnd_574880 := by exact prefixLift 574880
  have htrace : WordTrace (prefixWord ++ tailWord_574880) baseStart_574880 baseEnd_574880 := by
    simpa [prefixWord, tailWord_574880, baseEnd_574880] using wordTrace_append hprefix tailTrace_574880
  have hstable : (prefixWord ++ tailWord_574880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574880).length < 2 ^ (prefixWord ++ tailWord_574880).sum := by decide
  have hdescent : baseEnd_574880 < baseStart_574880 := by decide
  rcases family_descends (prefixWord ++ tailWord_574880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574920 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_574920 : Nat := 118140960795 + 574920 * 2 ^ 59
def prefixEnd_574920 : Nat := 4983230072969 + 3 ^ 40 * 574920 * 2
def baseEnd_574920 : Nat := 295210297882995856555997

theorem tailTrace_574920 : CollatzResearch.WordTrace tailWord_574920 prefixEnd_574920 295210297882995856555997 := by
  unfold tailWord_574920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484527538585251681961107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13979370051447002242614809 10484527538585251681961107)
  ·
    refine ⟨15726791307877877522941661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10484527538585251681961107 15726791307877877522941661)
    ·
      refine ⟨5897546740454204071103123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15726791307877877522941661 5897546740454204071103123)
      ·
        refine ⟨8846320110681306106654685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5897546740454204071103123 8846320110681306106654685)
        ·
          refine ⟨3317370041505489789995507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8846320110681306106654685 3317370041505489789995507)
          ·
            refine ⟨4976055062258234684993261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317370041505489789995507 4976055062258234684993261)
            ·
              refine ⟨1866020648346838006872473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4976055062258234684993261 1866020648346838006872473)
              ·
                refine ⟨1399515486260128505154355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866020648346838006872473 1399515486260128505154355)
                ·
                  refine ⟨2099273229390192757731533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399515486260128505154355 2099273229390192757731533)
                  ·
                    refine ⟨787227461021322284149325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2099273229390192757731533 787227461021322284149325)
                    ·
                      refine ⟨295210297882995856555997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787227461021322284149325 295210297882995856555997)
                      ·
                        rfl

theorem cell23_574920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_574920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574920 prefixEnd_574920 := by exact prefixLift 574920
  have htrace : WordTrace (prefixWord ++ tailWord_574920) baseStart_574920 baseEnd_574920 := by
    simpa [prefixWord, tailWord_574920, baseEnd_574920] using wordTrace_append hprefix tailTrace_574920
  have hstable : (prefixWord ++ tailWord_574920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574920).length < 2 ^ (prefixWord ++ tailWord_574920).sum := by decide
  have hdescent : baseEnd_574920 < baseStart_574920 := by decide
  rcases family_descends (prefixWord ++ tailWord_574920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574924 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_574924 : Nat := 118140960795 + 574924 * 2 ^ 59
def prefixEnd_574924 : Nat := 4983230072969 + 3 ^ 40 * 574924 * 2
def baseEnd_574924 : Nat := 295212351805613840905979

theorem tailTrace_574924 : CollatzResearch.WordTrace tailWord_574924 prefixEnd_574924 295212351805613840905979 := by
  unfold tailWord_574924
  simp only [CollatzResearch.WordTrace]
  refine ⟨10484600484578006023533913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13979467312770674698045217 10484600484578006023533913)
  ·
    refine ⟨7863450363433504517650435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10484600484578006023533913 7863450363433504517650435)
    ·
      refine ⟨11795175545150256776475653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863450363433504517650435 11795175545150256776475653)
      ·
        refine ⟨2211595414715673145589185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11795175545150256776475653 2211595414715673145589185)
        ·
          refine ⟨1658696561036754859191889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211595414715673145589185 1658696561036754859191889)
          ·
            refine ⟨1244022420777566144393917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658696561036754859191889 1244022420777566144393917)
            ·
              refine ⟨466508407791587304147719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244022420777566144393917 466508407791587304147719)
              ·
                refine ⟨699762611687380956221579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466508407791587304147719 699762611687380956221579)
                ·
                  refine ⟨1049643917531071434332369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699762611687380956221579 1049643917531071434332369)
                  ·
                    refine ⟨787232938148303575749277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049643917531071434332369 787232938148303575749277)
                    ·
                      refine ⟨295212351805613840905979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787232938148303575749277 295212351805613840905979)
                      ·
                        rfl

theorem cell23_574924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_574924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574924 prefixEnd_574924 := by exact prefixLift 574924
  have htrace : WordTrace (prefixWord ++ tailWord_574924) baseStart_574924 baseEnd_574924 := by
    simpa [prefixWord, tailWord_574924, baseEnd_574924] using wordTrace_append hprefix tailTrace_574924
  have hstable : (prefixWord ++ tailWord_574924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574924).length < 2 ^ (prefixWord ++ tailWord_574924).sum := by decide
  have hdescent : baseEnd_574924 < baseStart_574924 := by decide
  rcases family_descends (prefixWord ++ tailWord_574924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574937 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 3]
def baseStart_574937 : Nat := 118140960795 + 574937 * 2 ^ 59
def prefixEnd_574937 : Nat := 4983230072969 + 3 ^ 40 * 574937 * 2
def baseEnd_574937 : Nat := 295219027054122290043419

theorem tailTrace_574937 : CollatzResearch.WordTrace tailWord_574937 prefixEnd_574937 295219027054122290043419 := by
  unfold tailWord_574937
  simp only [CollatzResearch.WordTrace]
  refine ⟨20969675118108915267291065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13979783412072610178194043 20969675118108915267291065)
  ·
    refine ⟨15727256338581686450468299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20969675118108915267291065 15727256338581686450468299)
    ·
      refine ⟨23590884507872529675702449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15727256338581686450468299 23590884507872529675702449)
      ·
        refine ⟨17693163380904397256776837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23590884507872529675702449 17693163380904397256776837)
        ·
          refine ⟨3317468133919574485645657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17693163380904397256776837 3317468133919574485645657)
          ·
            refine ⟨2488101100439680864234243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317468133919574485645657 2488101100439680864234243)
            ·
              refine ⟨3732151650659521296351365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488101100439680864234243 3732151650659521296351365)
              ·
                refine ⟨699778434498660243065881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3732151650659521296351365 699778434498660243065881)
                ·
                  refine ⟨524833825873995182299411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 699778434498660243065881 524833825873995182299411)
                  ·
                    refine ⟨787250738810992773449117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 524833825873995182299411 787250738810992773449117)
                    ·
                      refine ⟨295219027054122290043419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787250738810992773449117 295219027054122290043419)
                      ·
                        rfl

theorem cell23_574937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_574937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574937 prefixEnd_574937 := by exact prefixLift 574937
  have htrace : WordTrace (prefixWord ++ tailWord_574937) baseStart_574937 baseEnd_574937 := by
    simpa [prefixWord, tailWord_574937, baseEnd_574937] using wordTrace_append hprefix tailTrace_574937
  have hstable : (prefixWord ++ tailWord_574937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574937).length < 2 ^ (prefixWord ++ tailWord_574937).sum := by decide
  have hdescent : baseEnd_574937 < baseStart_574937 := by decide
  rcases family_descends (prefixWord ++ tailWord_574937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574938 : List Nat := [3, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2]
def baseStart_574938 : Nat := 118140960795 + 574938 * 2 ^ 59
def prefixEnd_574938 : Nat := 4983230072969 + 3 ^ 40 * 574938 * 2
def baseEnd_574938 : Nat := 295219540534776786130915

theorem tailTrace_574938 : CollatzResearch.WordTrace tailWord_574938 prefixEnd_574938 295219540534776786130915 := by
  unfold tailWord_574938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242427897776323109519367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13979807727403528292051645 5242427897776323109519367)
  ·
    refine ⟨7863641846664484664279051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5242427897776323109519367 7863641846664484664279051)
    ·
      refine ⟨11795462769996726996418577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7863641846664484664279051 11795462769996726996418577)
      ·
        refine ⟨8846597077497545247313933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11795462769996726996418577 8846597077497545247313933)
        ·
          refine ⟨3317473904061579467742725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8846597077497545247313933 3317473904061579467742725)
          ·
            refine ⟨622026357011546150201761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3317473904061579467742725 622026357011546150201761)
            ·
              refine ⟨466519767758659612651321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622026357011546150201761 466519767758659612651321)
              ·
                refine ⟨349889825818994709488491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466519767758659612651321 349889825818994709488491)
                ·
                  refine ⟨524834738728492064232737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349889825818994709488491 524834738728492064232737)
                  ·
                    refine ⟨393626054046369048174553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 524834738728492064232737 393626054046369048174553)
                    ·
                      refine ⟨295219540534776786130915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393626054046369048174553 295219540534776786130915)
                      ·
                        rfl

theorem cell23_574938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_574938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574938 prefixEnd_574938 := by exact prefixLift 574938
  have htrace : WordTrace (prefixWord ++ tailWord_574938) baseStart_574938 baseEnd_574938 := by
    simpa [prefixWord, tailWord_574938, baseEnd_574938] using wordTrace_append hprefix tailTrace_574938
  have hstable : (prefixWord ++ tailWord_574938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574938).length < 2 ^ (prefixWord ++ tailWord_574938).sum := by decide
  have hdescent : baseEnd_574938 < baseStart_574938 := by decide
  rcases family_descends (prefixWord ++ tailWord_574938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574943 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_574943 : Nat := 118140960795 + 574943 * 2 ^ 59
def prefixEnd_574943 : Nat := 4983230072969 + 3 ^ 40 * 574943 * 2
def baseEnd_574943 : Nat := 295222107938049266568391

theorem tailTrace_574943 : CollatzResearch.WordTrace tailWord_574943 prefixEnd_574943 295222107938049266568391 := by
  unfold tailWord_574943
  simp only [CollatzResearch.WordTrace]
  refine ⟨20969893956087178292009483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13979929304058118861339655 20969893956087178292009483)
  ·
    refine ⟨31454840934130767438014225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20969893956087178292009483 31454840934130767438014225)
    ·
      refine ⟨23591130700598075578510669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31454840934130767438014225 23591130700598075578510669)
      ·
        refine ⟨8846674012724278341941501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23591130700598075578510669 8846674012724278341941501)
        ·
          refine ⟨3317502754771604378228063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8846674012724278341941501 3317502754771604378228063)
          ·
            refine ⟨4976254132157406567342095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317502754771604378228063 4976254132157406567342095)
            ·
              refine ⟨7464381198236109851013143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976254132157406567342095 7464381198236109851013143)
              ·
                refine ⟨11196571797354164776519715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464381198236109851013143 11196571797354164776519715)
                ·
                  refine ⟨16794857696031247164779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11196571797354164776519715 16794857696031247164779573)
                  ·
                    refine ⟨1574517909002929421698085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16794857696031247164779573 1574517909002929421698085)
                    ·
                      refine ⟨295222107938049266568391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1574517909002929421698085 295222107938049266568391)
                      ·
                        rfl

theorem cell23_574943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_574943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574943 prefixEnd_574943 := by exact prefixLift 574943
  have htrace : WordTrace (prefixWord ++ tailWord_574943) baseStart_574943 baseEnd_574943 := by
    simpa [prefixWord, tailWord_574943, baseEnd_574943] using wordTrace_append hprefix tailTrace_574943
  have hstable : (prefixWord ++ tailWord_574943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574943).length < 2 ^ (prefixWord ++ tailWord_574943).sum := by decide
  have hdescent : baseEnd_574943 < baseStart_574943 := by decide
  rcases family_descends (prefixWord ++ tailWord_574943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574947 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 3, 3, 2]
def baseStart_574947 : Nat := 118140960795 + 574947 * 2 ^ 59
def prefixEnd_574947 : Nat := 4983230072969 + 3 ^ 40 * 574947 * 2
def baseEnd_574947 : Nat := 295224161860667250918373

theorem tailTrace_574947 : CollatzResearch.WordTrace tailWord_574947 prefixEnd_574947 295224161860667250918373 := by
  unfold tailWord_574947
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970039848072686975155095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13980026565381791316770063 20970039848072686975155095)
  ·
    refine ⟨31455059772109030462732643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20970039848072686975155095 31455059772109030462732643)
    ·
      refine ⟨47182589658163545694098965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31455059772109030462732643 47182589658163545694098965)
      ·
        refine ⟨2211683890226416204410889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47182589658163545694098965 2211683890226416204410889)
        ·
          refine ⟨1658762917669812153308167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211683890226416204410889 1658762917669812153308167)
          ·
            refine ⟨2488144376504718229962251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658762917669812153308167 2488144376504718229962251)
            ·
              refine ⟨3732216564757077344943377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488144376504718229962251 3732216564757077344943377)
              ·
                refine ⟨2799162423567808008707533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732216564757077344943377 2799162423567808008707533)
                ·
                  refine ⟨1049685908837928003265325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2799162423567808008707533 1049685908837928003265325)
                  ·
                    refine ⟨393632215814223001224497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1049685908837928003265325 393632215814223001224497)
                    ·
                      refine ⟨295224161860667250918373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393632215814223001224497 295224161860667250918373)
                      ·
                        rfl

theorem cell23_574947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_574947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574947 prefixEnd_574947 := by exact prefixLift 574947
  have htrace : WordTrace (prefixWord ++ tailWord_574947) baseStart_574947 baseEnd_574947 := by
    simpa [prefixWord, tailWord_574947, baseEnd_574947] using wordTrace_append hprefix tailTrace_574947
  have hstable : (prefixWord ++ tailWord_574947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574947).length < 2 ^ (prefixWord ++ tailWord_574947).sum := by decide
  have hdescent : baseEnd_574947 < baseStart_574947 := by decide
  rcases family_descends (prefixWord ++ tailWord_574947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574963 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5]
def baseStart_574963 : Nat := 118140960795 + 574963 * 2 ^ 59
def prefixEnd_574963 : Nat := 4983230072969 + 3 ^ 40 * 574963 * 2
def baseEnd_574963 : Nat := 295232377551139188318299

theorem tailTrace_574963 : CollatzResearch.WordTrace tailWord_574963 prefixEnd_574963 295232377551139188318299 := by
  unfold tailWord_574963
  simp only [CollatzResearch.WordTrace]
  refine ⟨20970623416014721707737543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13980415610676481138491695 20970623416014721707737543)
  ·
    refine ⟨31455935124022082561606315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20970623416014721707737543 31455935124022082561606315)
    ·
      refine ⟨47183902686033123842409473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31455935124022082561606315 47183902686033123842409473)
      ·
        refine ⟨35387927014524842881807105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47183902686033123842409473 35387927014524842881807105)
        ·
          refine ⟨26540945260893632161355329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35387927014524842881807105 26540945260893632161355329)
          ·
            refine ⟨19905708945670224121016497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26540945260893632161355329 19905708945670224121016497)
            ·
              refine ⟨14929281709252668090762373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19905708945670224121016497 14929281709252668090762373)
              ·
                refine ⟨2799240320484875267017945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14929281709252668090762373 2799240320484875267017945)
                ·
                  refine ⟨2099430240363656450263459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2799240320484875267017945 2099430240363656450263459)
                  ·
                    refine ⟨3149145360545484675395189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2099430240363656450263459 3149145360545484675395189)
                    ·
                      refine ⟨295232377551139188318299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3149145360545484675395189 295232377551139188318299)
                      ·
                        rfl

theorem cell23_574963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_574963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_574963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_574963 prefixEnd_574963 := by exact prefixLift 574963
  have htrace : WordTrace (prefixWord ++ tailWord_574963) baseStart_574963 baseEnd_574963 := by
    simpa [prefixWord, tailWord_574963, baseEnd_574963] using wordTrace_append hprefix tailTrace_574963
  have hstable : (prefixWord ++ tailWord_574963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574963).length < 2 ^ (prefixWord ++ tailWord_574963).sum := by decide
  have hdescent : baseEnd_574963 < baseStart_574963 := by decide
  rcases family_descends (prefixWord ++ tailWord_574963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575011 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 1, 4, 2]
def baseStart_575011 : Nat := 118140960795 + 575011 * 2 ^ 59
def prefixEnd_575011 : Nat := 4983230072969 + 3 ^ 40 * 575011 * 2
def baseEnd_575011 : Nat := 295257024622555000518079

theorem tailTrace_575011 : CollatzResearch.WordTrace tailWord_575011 prefixEnd_575011 295257024622555000518079 := by
  unfold tailWord_575011
  simp only [CollatzResearch.WordTrace]
  refine ⟨20972374119840825905484887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13981582746560550603656591 20972374119840825905484887)
  ·
    refine ⟨31458561179761238858227331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20972374119840825905484887 31458561179761238858227331)
    ·
      refine ⟨47187841769641858287340997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31458561179761238858227331 47187841769641858287340997)
      ·
        refine ⟨8847720331807848428876437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47187841769641858287340997 8847720331807848428876437)
        ·
          refine ⟨414736890553492895103583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8847720331807848428876437 414736890553492895103583)
          ·
            refine ⟨622105335830239342655375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414736890553492895103583 622105335830239342655375)
            ·
              refine ⟨933158003745359013983063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622105335830239342655375 933158003745359013983063)
              ·
                refine ⟨1399737005618038520974595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933158003745359013983063 1399737005618038520974595)
                ·
                  refine ⟨2099605508427057781461893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399737005618038520974595 2099605508427057781461893)
                  ·
                    refine ⟨393676032830073334024105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2099605508427057781461893 393676032830073334024105)
                    ·
                      refine ⟨295257024622555000518079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393676032830073334024105 295257024622555000518079)
                      ·
                        rfl

theorem cell23_575011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_575011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575011 prefixEnd_575011 := by exact prefixLift 575011
  have htrace : WordTrace (prefixWord ++ tailWord_575011) baseStart_575011 baseEnd_575011 := by
    simpa [prefixWord, tailWord_575011, baseEnd_575011] using wordTrace_append hprefix tailTrace_575011
  have hstable : (prefixWord ++ tailWord_575011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575011).length < 2 ^ (prefixWord ++ tailWord_575011).sum := by decide
  have hdescent : baseEnd_575011 < baseStart_575011 := by decide
  rcases family_descends (prefixWord ++ tailWord_575011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575047 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 2, 5]
def baseStart_575047 : Nat := 118140960795 + 575047 * 2 ^ 59
def prefixEnd_575047 : Nat := 4983230072969 + 3 ^ 40 * 575047 * 2
def baseEnd_575047 : Nat := 98425169975372286555971

theorem tailTrace_575047 : CollatzResearch.WordTrace tailWord_575047 prefixEnd_575047 98425169975372286555971 := by
  unfold tailWord_575047
  simp only [CollatzResearch.WordTrace]
  refine ⟨20973687147710404053795395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13982458098473602702530263 20973687147710404053795395)
  ·
    refine ⟨31460530721565606080693093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20973687147710404053795395 31460530721565606080693093)
    ·
      refine ⟨5898849510293551140129955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31460530721565606080693093 5898849510293551140129955)
      ·
        refine ⟨8848274265440326710194933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5898849510293551140129955 8848274265440326710194933)
        ·
          refine ⟨829525712385030629080775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8848274265440326710194933 829525712385030629080775)
          ·
            refine ⟨1244288568577545943621163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829525712385030629080775 1244288568577545943621163)
            ·
              refine ⟨1866432852866318915431745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244288568577545943621163 1866432852866318915431745)
              ·
                refine ⟨1399824639649739186573809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866432852866318915431745 1399824639649739186573809)
                ·
                  refine ⟨1049868479737304389930357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399824639649739186573809 1049868479737304389930357)
                  ·
                    refine ⟨98425169975372286555971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1049868479737304389930357 98425169975372286555971)
                    ·
                      rfl

theorem cell23_575047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_575047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575047 prefixEnd_575047 := by exact prefixLift 575047
  have htrace : WordTrace (prefixWord ++ tailWord_575047) baseStart_575047 baseEnd_575047 := by
    simpa [prefixWord, tailWord_575047, baseEnd_575047] using wordTrace_append hprefix tailTrace_575047
  have hstable : (prefixWord ++ tailWord_575047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575047).length < 2 ^ (prefixWord ++ tailWord_575047).sum := by decide
  have hdescent : baseEnd_575047 < baseStart_575047 := by decide
  rcases family_descends (prefixWord ++ tailWord_575047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575111 : List Nat := [1, 1, 4, 2, 1, 3, 4, 2, 1, 4]
def baseStart_575111 : Nat := 118140960795 + 575111 * 2 ^ 59
def prefixEnd_575111 : Nat := 4983230072969 + 3 ^ 40 * 575111 * 2
def baseEnd_575111 : Nat := 98436124229334869755873

theorem tailTrace_575111 : CollatzResearch.WordTrace tailWord_575111 prefixEnd_575111 98436124229334869755873 := by
  unfold tailWord_575111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20976021419478542984125187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13984014279652361989416791 20976021419478542984125187)
  ·
    refine ⟨31464032129217814476187781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20976021419478542984125187 31464032129217814476187781)
    ·
      refine ⟨5899506024228340214285209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31464032129217814476187781 5899506024228340214285209)
      ·
        refine ⟨4424629518171255160713907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5899506024228340214285209 4424629518171255160713907)
        ·
          refine ⟨6636944277256882741070861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424629518171255160713907 6636944277256882741070861)
          ·
            refine ⟨2488854103971331027901573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6636944277256882741070861 2488854103971331027901573)
            ·
              refine ⟨466660144494624567731545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2488854103971331027901573 466660144494624567731545)
              ·
                refine ⟨349995108370968425798659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466660144494624567731545 349995108370968425798659)
                ·
                  refine ⟨524992662556452638697989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349995108370968425798659 524992662556452638697989)
                  ·
                    refine ⟨98436124229334869755873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 524992662556452638697989 98436124229334869755873)
                    ·
                      rfl

theorem cell23_575111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_575111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575111 prefixEnd_575111 := by exact prefixLift 575111
  have htrace : WordTrace (prefixWord ++ tailWord_575111) baseStart_575111 baseEnd_575111 := by
    simpa [prefixWord, tailWord_575111, baseEnd_575111] using wordTrace_append hprefix tailTrace_575111
  have hstable : (prefixWord ++ tailWord_575111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575111).length < 2 ^ (prefixWord ++ tailWord_575111).sum := by decide
  have hdescent : baseEnd_575111 < baseStart_575111 := by decide
  rcases family_descends (prefixWord ++ tailWord_575111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575137 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_575137 : Nat := 118140960795 + 575137 * 2 ^ 59
def prefixEnd_575137 : Nat := 4983230072969 + 3 ^ 40 * 575137 * 2
def baseEnd_575137 : Nat := 98440574395007169180833

theorem tailTrace_575137 : CollatzResearch.WordTrace tailWord_575137 prefixEnd_575137 98440574395007169180833 := by
  unfold tailWord_575137
  simp only [CollatzResearch.WordTrace]
  refine ⟨20976969717384349424571665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13984646478256232949714443 20976969717384349424571665)
  ·
    refine ⟨15732727288038262068428749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20976969717384349424571665 15732727288038262068428749)
    ·
      refine ⟨5899772733014348275660781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15732727288038262068428749 5899772733014348275660781)
      ·
        refine ⟨2212414774880380603372793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5899772733014348275660781 2212414774880380603372793)
        ·
          refine ⟨1659311081160285452529595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2212414774880380603372793 1659311081160285452529595)
          ·
            refine ⟨2488966621740428178794393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659311081160285452529595 2488966621740428178794393)
            ·
              refine ⟨1866724966305321134095795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488966621740428178794393 1866724966305321134095795)
              ·
                refine ⟨2800087449457981701143693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866724966305321134095795 2800087449457981701143693)
                ·
                  refine ⟨1050032793546743137928885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2800087449457981701143693 1050032793546743137928885)
                  ·
                    refine ⟨98440574395007169180833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1050032793546743137928885 98440574395007169180833)
                    ·
                      rfl

theorem cell23_575137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_575137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575137 prefixEnd_575137 := by exact prefixLift 575137
  have htrace : WordTrace (prefixWord ++ tailWord_575137) baseStart_575137 baseEnd_575137 := by
    simpa [prefixWord, tailWord_575137, baseEnd_575137] using wordTrace_append hprefix tailTrace_575137
  have hstable : (prefixWord ++ tailWord_575137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575137).length < 2 ^ (prefixWord ++ tailWord_575137).sum := by decide
  have hdescent : baseEnd_575137 < baseStart_575137 := by decide
  rcases family_descends (prefixWord ++ tailWord_575137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575138 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_575138 : Nat := 118140960795 + 575138 * 2 ^ 59
def prefixEnd_575138 : Nat := 4983230072969 + 3 ^ 40 * 575138 * 2
def baseEnd_575138 : Nat := 295322236665676003629995

theorem tailTrace_575138 : CollatzResearch.WordTrace tailWord_575138 prefixEnd_575138 295322236665676003629995 := by
  unfold tailWord_575138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244251547595181648839517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13984670793587151063572045 5244251547595181648839517)
  ·
    refine ⟨1966594330348193118314819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5244251547595181648839517 1966594330348193118314819)
    ·
      refine ⟨2949891495522289677472229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1966594330348193118314819 2949891495522289677472229)
      ·
        refine ⟨553104655410429314526043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2949891495522289677472229 553104655410429314526043)
        ·
          refine ⟨829656983115643971789065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553104655410429314526043 829656983115643971789065)
          ·
            refine ⟨622242737336732978841799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829656983115643971789065 622242737336732978841799)
            ·
              refine ⟨933364106005099468262699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622242737336732978841799 933364106005099468262699)
              ·
                refine ⟨1400046159007649202394049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933364106005099468262699 1400046159007649202394049)
                ·
                  refine ⟨1050034619255736901795537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1400046159007649202394049 1050034619255736901795537)
                  ·
                    refine ⟨787525964441802676346653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050034619255736901795537 787525964441802676346653)
                    ·
                      refine ⟨295322236665676003629995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787525964441802676346653 295322236665676003629995)
                      ·
                        rfl

theorem cell23_575138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_575138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575138 prefixEnd_575138 := by exact prefixLift 575138
  have htrace : WordTrace (prefixWord ++ tailWord_575138) baseStart_575138 baseEnd_575138 := by
    simpa [prefixWord, tailWord_575138, baseEnd_575138] using wordTrace_append hprefix tailTrace_575138
  have hstable : (prefixWord ++ tailWord_575138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575138).length < 2 ^ (prefixWord ++ tailWord_575138).sum := by decide
  have hdescent : baseEnd_575138 < baseStart_575138 := by decide
  rcases family_descends (prefixWord ++ tailWord_575138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575151 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 1, 1, 3]
def baseStart_575151 : Nat := 118140960795 + 575151 * 2 ^ 59
def prefixEnd_575151 : Nat := 4983230072969 + 3 ^ 40 * 575151 * 2
def baseEnd_575151 : Nat := 295328911914184452767435

theorem tailTrace_575151 : CollatzResearch.WordTrace tailWord_575151 prefixEnd_575151 295328911914184452767435 := by
  unfold tailWord_575151
  simp only [CollatzResearch.WordTrace]
  refine ⟨20977480339333629815581307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13984986892889086543720871 20977480339333629815581307)
  ·
    refine ⟨31466220509000444723371961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20977480339333629815581307 31466220509000444723371961)
    ·
      refine ⟨23599665381750333542528971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31466220509000444723371961 23599665381750333542528971)
      ·
        refine ⟨35399498072625500313793457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23599665381750333542528971 35399498072625500313793457)
        ·
          refine ⟨26549623554469125235345093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35399498072625500313793457 26549623554469125235345093)
          ·
            refine ⟨4978054416462960981627205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26549623554469125235345093 4978054416462960981627205)
            ·
              refine ⟨933385203086805184055101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4978054416462960981627205 933385203086805184055101)
              ·
                refine ⟨350019451157551944020663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933385203086805184055101 350019451157551944020663)
                ·
                  refine ⟨525029176736327916030995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350019451157551944020663 525029176736327916030995)
                  ·
                    refine ⟨787543765104491874046493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 525029176736327916030995 787543765104491874046493)
                    ·
                      refine ⟨295328911914184452767435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787543765104491874046493 295328911914184452767435)
                      ·
                        rfl

theorem cell23_575151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 1, 3].length) (baseStart_575151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575151 prefixEnd_575151 := by exact prefixLift 575151
  have htrace : WordTrace (prefixWord ++ tailWord_575151) baseStart_575151 baseEnd_575151 := by
    simpa [prefixWord, tailWord_575151, baseEnd_575151] using wordTrace_append hprefix tailTrace_575151
  have hstable : (prefixWord ++ tailWord_575151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575151).length < 2 ^ (prefixWord ++ tailWord_575151).sum := by decide
  have hdescent : baseEnd_575151 < baseStart_575151 := by decide
  rcases family_descends (prefixWord ++ tailWord_575151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575154 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_575154 : Nat := 118140960795 + 575154 * 2 ^ 59
def prefixEnd_575154 : Nat := 4983230072969 + 3 ^ 40 * 575154 * 2
def baseEnd_575154 : Nat := 98443484118715980343307

theorem tailTrace_575154 : CollatzResearch.WordTrace tailWord_575154 prefixEnd_575154 98443484118715980343307 := by
  unfold tailWord_575154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244397439580690331985129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13985059838881840885293677 5244397439580690331985129)
  ·
    refine ⟨3933298079685517748988847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5244397439580690331985129 3933298079685517748988847)
    ·
      refine ⟨5899947119528276623483271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933298079685517748988847 5899947119528276623483271)
      ·
        refine ⟨8849920679292414935224907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899947119528276623483271 8849920679292414935224907)
        ·
          refine ⟨13274881018938622402837361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8849920679292414935224907 13274881018938622402837361)
          ·
            refine ⟨9956160764203966802128021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13274881018938622402837361 9956160764203966802128021)
            ·
              refine ⟨466695035822060943849751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9956160764203966802128021 466695035822060943849751)
              ·
                refine ⟨700042553733091415774627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466695035822060943849751 700042553733091415774627)
                ·
                  refine ⟨1050063830599637123661941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700042553733091415774627 1050063830599637123661941)
                  ·
                    refine ⟨98443484118715980343307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1050063830599637123661941 98443484118715980343307)
                    ·
                      rfl

theorem cell23_575154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_575154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575154 prefixEnd_575154 := by exact prefixLift 575154
  have htrace : WordTrace (prefixWord ++ tailWord_575154) baseStart_575154 baseEnd_575154 := by
    simpa [prefixWord, tailWord_575154, baseEnd_575154] using wordTrace_append hprefix tailTrace_575154
  have hstable : (prefixWord ++ tailWord_575154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575154).length < 2 ^ (prefixWord ++ tailWord_575154).sum := by decide
  have hdescent : baseEnd_575154 < baseStart_575154 := by decide
  rcases family_descends (prefixWord ++ tailWord_575154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575160 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_575160 : Nat := 118140960795 + 575160 * 2 ^ 59
def prefixEnd_575160 : Nat := 4983230072969 + 3 ^ 40 * 575160 * 2
def baseEnd_575160 : Nat := 295333533240074917554893

theorem tailTrace_575160 : CollatzResearch.WordTrace tailWord_575160 prefixEnd_575160 295333533240074917554893 := by
  unfold tailWord_575160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488904298150512176329467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13985205730867349568439289 10488904298150512176329467)
  ·
    refine ⟨15733356447225768264494201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10488904298150512176329467 15733356447225768264494201)
    ·
      refine ⟨11800017335419326198370651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15733356447225768264494201 11800017335419326198370651)
      ·
        refine ⟨17700026003128989297555977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800017335419326198370651 17700026003128989297555977)
        ·
          refine ⟨13275019502346741973166983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17700026003128989297555977 13275019502346741973166983)
          ·
            refine ⟨19912529253520112959750475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13275019502346741973166983 19912529253520112959750475)
            ·
              refine ⟨29868793880280169439625713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19912529253520112959750475 29868793880280169439625713)
              ·
                refine ⟨22401595410210127079719285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29868793880280169439625713 22401595410210127079719285)
                ·
                  refine ⟨2100149569707199413723683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22401595410210127079719285 2100149569707199413723683)
                  ·
                    refine ⟨3150224354560799120585525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100149569707199413723683 3150224354560799120585525)
                    ·
                      refine ⟨295333533240074917554893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3150224354560799120585525 295333533240074917554893)
                      ·
                        rfl

theorem cell23_575160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_575160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575160 prefixEnd_575160 := by exact prefixLift 575160
  have htrace : WordTrace (prefixWord ++ tailWord_575160) baseStart_575160 baseEnd_575160 := by
    simpa [prefixWord, tailWord_575160, baseEnd_575160] using wordTrace_append hprefix tailTrace_575160
  have hstable : (prefixWord ++ tailWord_575160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575160).length < 2 ^ (prefixWord ++ tailWord_575160).sum := by decide
  have hdescent : baseEnd_575160 < baseStart_575160 := by decide
  rcases family_descends (prefixWord ++ tailWord_575160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575167 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 4, 4]
def baseStart_575167 : Nat := 118140960795 + 575167 * 2 ^ 59
def prefixEnd_575167 : Nat := 4983230072969 + 3 ^ 40 * 575167 * 2
def baseEnd_575167 : Nat := 98445709201552130055787

theorem tailTrace_575167 : CollatzResearch.WordTrace tailWord_575167 prefixEnd_575167 98445709201552130055787 := by
  unfold tailWord_575167
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978063907275664548163755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13985375938183776365442503 20978063907275664548163755)
  ·
    refine ⟨31467095860913496822245633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20978063907275664548163755 31467095860913496822245633)
    ·
      refine ⟨23600321895685122616684225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31467095860913496822245633 23600321895685122616684225)
      ·
        refine ⟨17700241421763841962513169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23600321895685122616684225 17700241421763841962513169)
        ·
          refine ⟨13275181066322881471884877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17700241421763841962513169 13275181066322881471884877)
          ·
            refine ⟨4978192899871080551956829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13275181066322881471884877 4978192899871080551956829)
            ·
              refine ⟨1866822337451655206983811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4978192899871080551956829 1866822337451655206983811)
              ·
                refine ⟨2800233506177482810475717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866822337451655206983811 2800233506177482810475717)
                ·
                  refine ⟨525043782408278026964197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2800233506177482810475717 525043782408278026964197)
                  ·
                    refine ⟨98445709201552130055787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525043782408278026964197 98445709201552130055787)
                    ·
                      rfl

theorem cell23_575167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_575167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575167 prefixEnd_575167 := by exact prefixLift 575167
  have htrace : WordTrace (prefixWord ++ tailWord_575167) baseStart_575167 baseEnd_575167 := by
    simpa [prefixWord, tailWord_575167, baseEnd_575167] using wordTrace_append hprefix tailTrace_575167
  have hstable : (prefixWord ++ tailWord_575167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575167).length < 2 ^ (prefixWord ++ tailWord_575167).sum := by decide
  have hdescent : baseEnd_575167 < baseStart_575167 := by decide
  rcases family_descends (prefixWord ++ tailWord_575167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575194 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_575194 : Nat := 118140960795 + 575194 * 2 ^ 59
def prefixEnd_575194 : Nat := 4983230072969 + 3 ^ 40 * 575194 * 2
def baseEnd_575194 : Nat := 295350991582327784529737

theorem tailTrace_575194 : CollatzResearch.WordTrace tailWord_575194 prefixEnd_575194 295350991582327784529737 := by
  unfold tailWord_575194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244762169544462039849159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13986032452118565439597757 5244762169544462039849159)
  ·
    refine ⟨7867143254316693059773739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5244762169544462039849159 7867143254316693059773739)
    ·
      refine ⟨11800714881475039589660609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7867143254316693059773739 11800714881475039589660609)
      ·
        refine ⟨8850536161106279692245457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11800714881475039589660609 8850536161106279692245457)
        ·
          refine ⟨6637902120829709769184093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8850536161106279692245457 6637902120829709769184093)
          ·
            refine ⟨2489213295311141163444035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6637902120829709769184093 2489213295311141163444035)
            ·
              refine ⟨3733819942966711745166053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489213295311141163444035 3733819942966711745166053)
              ·
                refine ⟨700091239306258452218635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3733819942966711745166053 700091239306258452218635)
                ·
                  refine ⟨1050136858959387678327953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700091239306258452218635 1050136858959387678327953)
                  ·
                    refine ⟨787602644219540758745965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050136858959387678327953 787602644219540758745965)
                    ·
                      refine ⟨295350991582327784529737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787602644219540758745965 295350991582327784529737)
                      ·
                        rfl

theorem cell23_575194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_575194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575194 prefixEnd_575194 := by exact prefixLift 575194
  have htrace : WordTrace (prefixWord ++ tailWord_575194) baseStart_575194 baseEnd_575194 := by
    simpa [prefixWord, tailWord_575194, baseEnd_575194] using wordTrace_append hprefix tailTrace_575194
  have hstable : (prefixWord ++ tailWord_575194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575194).length < 2 ^ (prefixWord ++ tailWord_575194).sum := by decide
  have hdescent : baseEnd_575194 < baseStart_575194 := by decide
  rcases family_descends (prefixWord ++ tailWord_575194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575262 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_575262 : Nat := 118140960795 + 575262 * 2 ^ 59
def prefixEnd_575262 : Nat := 4983230072969 + 3 ^ 40 * 575262 * 2
def baseEnd_575262 : Nat := 295385908266833518479425

theorem tailTrace_575262 : CollatzResearch.WordTrace tailWord_575262 prefixEnd_575262 295385908266833518479425 := by
  unfold tailWord_575262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622691105241436971609005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13987685894620997181914693 2622691105241436971609005)
  ·
    refine ⟨983509164465538864353377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2622691105241436971609005 983509164465538864353377)
    ·
      refine ⟨737631873349154148265033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983509164465538864353377 737631873349154148265033)
      ·
        refine ⟨553223905011865611198775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 737631873349154148265033 553223905011865611198775)
        ·
          refine ⟨829835857517798416798163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553223905011865611198775 829835857517798416798163)
          ·
            refine ⟨1244753786276697625197245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829835857517798416798163 1244753786276697625197245)
            ·
              refine ⟨466782669853761609448967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244753786276697625197245 466782669853761609448967)
              ·
                refine ⟨700174004780642414173451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466782669853761609448967 700174004780642414173451)
                ·
                  refine ⟨1050261007170963621260177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700174004780642414173451 1050261007170963621260177)
                  ·
                    refine ⟨787695755378222715945133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050261007170963621260177 787695755378222715945133)
                    ·
                      refine ⟨295385908266833518479425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787695755378222715945133 295385908266833518479425)
                      ·
                        rfl

theorem cell23_575262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_575262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575262 prefixEnd_575262 := by exact prefixLift 575262
  have htrace : WordTrace (prefixWord ++ tailWord_575262) baseStart_575262 baseEnd_575262 := by
    simpa [prefixWord, tailWord_575262, baseEnd_575262] using wordTrace_append hprefix tailTrace_575262
  have hstable : (prefixWord ++ tailWord_575262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575262).length < 2 ^ (prefixWord ++ tailWord_575262).sum := by decide
  have hdescent : baseEnd_575262 < baseStart_575262 := by decide
  rcases family_descends (prefixWord ++ tailWord_575262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575267 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5]
def baseStart_575267 : Nat := 118140960795 + 575267 * 2 ^ 59
def prefixEnd_575267 : Nat := 4983230072969 + 3 ^ 40 * 575267 * 2
def baseEnd_575267 : Nat := 295388475670105998916901

theorem tailTrace_575267 : CollatzResearch.WordTrace tailWord_575267 prefixEnd_575267 295388475670105998916901 := by
  unfold tailWord_575267
  simp only [CollatzResearch.WordTrace]
  refine ⟨20981711206913381626804055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13987807471275587751202703 20981711206913381626804055)
  ·
    refine ⟨31472566810370072440206083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20981711206913381626804055 31472566810370072440206083)
    ·
      refine ⟨47208850215555108660309125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31472566810370072440206083 47208850215555108660309125)
      ·
        refine ⟨8851659415416582873807961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47208850215555108660309125 8851659415416582873807961)
        ·
          refine ⟨6638744561562437155355971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8851659415416582873807961 6638744561562437155355971)
          ·
            refine ⟨9958116842343655733033957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638744561562437155355971 9958116842343655733033957)
            ·
              refine ⟨1867146907939435449943867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9958116842343655733033957 1867146907939435449943867)
              ·
                refine ⟨2800720361909153174915801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867146907939435449943867 2800720361909153174915801)
                ·
                  refine ⟨2100540271431864881186851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2800720361909153174915801 2100540271431864881186851)
                  ·
                    refine ⟨3150810407147797321780277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100540271431864881186851 3150810407147797321780277)
                    ·
                      refine ⟨295388475670105998916901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3150810407147797321780277 295388475670105998916901)
                      ·
                        rfl

theorem cell23_575267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_575267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575267 prefixEnd_575267 := by exact prefixLift 575267
  have htrace : WordTrace (prefixWord ++ tailWord_575267) baseStart_575267 baseEnd_575267 := by
    simpa [prefixWord, tailWord_575267, baseEnd_575267] using wordTrace_append hprefix tailTrace_575267
  have hstable : (prefixWord ++ tailWord_575267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575267).length < 2 ^ (prefixWord ++ tailWord_575267).sum := by decide
  have hdescent : baseEnd_575267 < baseStart_575267 := by decide
  rcases family_descends (prefixWord ++ tailWord_575267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575294 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_575294 : Nat := 118140960795 + 575294 * 2 ^ 59
def prefixEnd_575294 : Nat := 4983230072969 + 3 ^ 40 * 575294 * 2
def baseEnd_575294 : Nat := 295402339647777393279277

theorem tailTrace_575294 : CollatzResearch.WordTrace tailWord_575294 prefixEnd_575294 295402339647777393279277 := by
  unfold tailWord_575294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622836997226945654754617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13988463985210376825357957 2622836997226945654754617)
  ·
    refine ⟨1967127747920209241065963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2622836997226945654754617 1967127747920209241065963)
    ·
      refine ⟨2950691621880313861598945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1967127747920209241065963 2950691621880313861598945)
      ·
        refine ⟨2213018716410235396199209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2950691621880313861598945 2213018716410235396199209)
        ·
          refine ⟨1659764037307676547149407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213018716410235396199209 1659764037307676547149407)
          ·
            refine ⟨2489646055961514820724111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659764037307676547149407 2489646055961514820724111)
            ·
              refine ⟨3734469083942272231086167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489646055961514820724111 3734469083942272231086167)
              ·
                refine ⟨5601703625913408346629251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734469083942272231086167 5601703625913408346629251)
                ·
                  refine ⟨8402555438870112519943877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5601703625913408346629251 8402555438870112519943877)
                  ·
                    refine ⟨1575479144788146097489477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8402555438870112519943877 1575479144788146097489477)
                    ·
                      refine ⟨295402339647777393279277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1575479144788146097489477 295402339647777393279277)
                      ·
                        rfl

theorem cell23_575294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_575294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575294 prefixEnd_575294 := by exact prefixLift 575294
  have htrace : WordTrace (prefixWord ++ tailWord_575294) baseStart_575294 baseEnd_575294 := by
    simpa [prefixWord, tailWord_575294, baseEnd_575294] using wordTrace_append hprefix tailTrace_575294
  have hstable : (prefixWord ++ tailWord_575294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575294).length < 2 ^ (prefixWord ++ tailWord_575294).sum := by decide
  have hdescent : baseEnd_575294 < baseStart_575294 := by decide
  rcases family_descends (prefixWord ++ tailWord_575294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575332 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_575332 : Nat := 118140960795 + 575332 * 2 ^ 59
def prefixEnd_575332 : Nat := 4983230072969 + 3 ^ 40 * 575332 * 2
def baseEnd_575332 : Nat := 295421851912648244604103

theorem tailTrace_575332 : CollatzResearch.WordTrace tailWord_575332 prefixEnd_575332 295421851912648244604103 := by
  unfold tailWord_575332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492040975838948863960125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13989387967785265151946833 10492040975838948863960125)
  ·
    refine ⟨3934515365939605823985047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10492040975838948863960125 3934515365939605823985047)
    ·
      refine ⟨5901773048909408735977571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3934515365939605823985047 5901773048909408735977571)
      ·
        refine ⟨8852659573364113103966357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5901773048909408735977571 8852659573364113103966357)
        ·
          refine ⟨414968417501442801748423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8852659573364113103966357 414968417501442801748423)
          ·
            refine ⟨622452626252164202622635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414968417501442801748423 622452626252164202622635)
            ·
              refine ⟨933678939378246303933953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622452626252164202622635 933678939378246303933953)
              ·
                refine ⟨700259204533684727950465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933678939378246303933953 700259204533684727950465)
                ·
                  refine ⟨525194403400263545962849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700259204533684727950465 525194403400263545962849)
                  ·
                    refine ⟨393895802550197659472137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 525194403400263545962849 393895802550197659472137)
                    ·
                      refine ⟨295421851912648244604103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 393895802550197659472137 295421851912648244604103)
                      ·
                        rfl

theorem cell23_575332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_575332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575332 prefixEnd_575332 := by exact prefixLift 575332
  have htrace : WordTrace (prefixWord ++ tailWord_575332) baseStart_575332 baseEnd_575332 := by
    simpa [prefixWord, tailWord_575332, baseEnd_575332] using wordTrace_append hprefix tailTrace_575332
  have hstable : (prefixWord ++ tailWord_575332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575332).length < 2 ^ (prefixWord ++ tailWord_575332).sum := by decide
  have hdescent : baseEnd_575332 < baseStart_575332 := by decide
  rcases family_descends (prefixWord ++ tailWord_575332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575377 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 8]
def baseStart_575377 : Nat := 118140960795 + 575377 * 2 ^ 59
def prefixEnd_575377 : Nat := 4983230072969 + 3 ^ 40 * 575377 * 2
def baseEnd_575377 : Nat := 32827217615788952060155

theorem tailTrace_575377 : CollatzResearch.WordTrace tailWord_575377 prefixEnd_575377 32827217615788952060155 := by
  unfold tailWord_575377
  simp only [CollatzResearch.WordTrace]
  refine ⟨20985723236514870413308385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13990482157676580275538923 20985723236514870413308385)
  ·
    refine ⟨15739292427386152809981289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20985723236514870413308385 15739292427386152809981289)
    ·
      refine ⟨11804469320539614607485967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15739292427386152809981289 11804469320539614607485967)
      ·
        refine ⟨17706703980809421911228951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11804469320539614607485967 17706703980809421911228951)
        ·
          refine ⟨26560055971214132866843427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17706703980809421911228951 26560055971214132866843427)
          ·
            refine ⟨39840083956821199300265141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26560055971214132866843427 39840083956821199300265141)
            ·
              refine ⟨3735007870951987434399857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39840083956821199300265141 3735007870951987434399857)
              ·
                refine ⟨2801255903213990575799893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735007870951987434399857 2801255903213990575799893)
                ·
                  refine ⟨32827217615788952060155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2801255903213990575799893 32827217615788952060155)
                  ·
                    rfl

theorem cell23_575377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_575377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575377 prefixEnd_575377 := by exact prefixLift 575377
  have htrace : WordTrace (prefixWord ++ tailWord_575377) baseStart_575377 baseEnd_575377 := by
    simpa [prefixWord, tailWord_575377, baseEnd_575377] using wordTrace_append hprefix tailTrace_575377
  have hstable : (prefixWord ++ tailWord_575377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575377).length < 2 ^ (prefixWord ++ tailWord_575377).sum := by decide
  have hdescent : baseEnd_575377 < baseStart_575377 := by decide
  rcases family_descends (prefixWord ++ tailWord_575377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
